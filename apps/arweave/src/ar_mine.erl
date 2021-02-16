-module(ar_mine).

-export([
	start/1, stop/1,
	mine_spora/2,
	validate/4, validate/3, validate_spora/9,
	min_difficulty/1, max_difficulty/0,
	min_spora_difficulty/1,
	sha384_diff_to_randomx_diff/1,
	spora_solution_hash/5,
	pick_recall_byte/4,
	get_search_space_upper_bound/2
]).

-include_lib("arweave/include/ar.hrl").
-include_lib("arweave/include/ar_pricing.hrl").
-include_lib("arweave/include/ar_block.hrl").
-include_lib("arweave/include/ar_mine.hrl").

-include_lib("eunit/include/eunit.hrl").

%% @doc State record for miners.
-record(state, {
	parent,						% The parent process. The mining solution is sent there.
	current_block,				% The current tip block.
	candidate_block = not_set,	% The product of mining.
	block_txs_pairs,			% List of {BH, TXIDs} pairs for the latest
								% ?MAX_TX_ANCHOR_DEPTH blocks.
	txs,						% The list of transactions to be mined.
	timestamp,					% The block timestamp used for the mining.
	timestamp_refresh_timer,	% Reference for timer for updating the timestamp.
	data_segment = <<>>,		% The data segment generated for mining.
	data_segment_duration,		% Duration in seconds of the last generation of the data segment.
	reward_addr,				% The mining reward address
	reward_wallet_before_mining_reward = not_in_the_list,
	tags, % The block tags.
	diff, % The currently estimated new network difficulty.
	delay = 0,							% Hashing delay used for testing
	max_miners = ?NUM_MINING_PROCESSES, % The number of mining process to spawn.
	miners = [],						% Miner worker processes.
	bds_base = not_generated,			% Part of the block data segment not changed during
										% mining before the fork 2.5.
	started_at = not_set,			% The timestamp when the mining begins,
									% used to estimate the  hashrate.
	total_sporas_tried = 0,			% The number of Succinct Proofs of Random Access
									% checked during mining.
	total_sporas_discovered = 0,	% The number of Succinct Proofs of Random Access
									% discovered but not neccessarily
									% checked (because they are not present locally)
									% during mining.
	block_index = not_set			% The latest block index.
}).

%%%===================================================================
%%% Public interface.
%%%===================================================================

%% @doc Spawns a new mining process and returns its PID.
start(Args) ->
	{CurrentB, TXs, RewardAddr, Tags, Parent, BlockTXPairs, BI} = Args,
	CurrentHeight = CurrentB#block.height,
	CandidateB = #block{
		height = CurrentHeight + 1,
		hash_list = ?BI_TO_BHL(lists:sublist(BI, ?STORE_BLOCKS_BEHIND_CURRENT)),
		previous_block = CurrentB#block.indep_hash,
		hash_list_merkle = ar_block:compute_hash_list_merkle(CurrentB, BI),
		reward_addr = RewardAddr,
		tags = Tags
	},
	State =
		#state{
			parent = Parent,
			current_block = CurrentB,
			data_segment_duration = 0,
			reward_addr = RewardAddr,
			tags = Tags,
			max_miners = ar_meta_db:get(max_miners),
			block_txs_pairs = BlockTXPairs,
			started_at = erlang:timestamp(),
			candidate_block = CandidateB,
			txs = TXs,
			block_index = BI
		},
	State2 =
		case CurrentHeight + 1 >= ar_fork:height_2_5() of
			false ->
				State;
			true ->
				{Rate, ScheduledRate} = ar_pricing:recalculate_usd_to_ar_rate(CurrentB),
				State#state{
					candidate_block =
						CandidateB#block{
							usd_to_ar_rate = Rate,
							scheduled_usd_to_ar_rate = ScheduledRate
						}
				}
		end,
	start_server(State2).

%% @doc Stop the running mining server.
stop(PID) ->
	PID ! stop.

%% @doc Validate that a given hash/nonce satisfy the difficulty requirement.
validate(BDS, Nonce, Diff, Height) ->
	BDSHash = ar_weave:hash(BDS, Nonce, Height),
	case validate(BDSHash, Diff, Height) of
		true ->
			{valid, BDSHash};
		false ->
			{invalid, BDSHash}
	end.

%% @doc Validate that a given block data segment hash satisfies the difficulty requirement.
validate(BDSHash, Diff, Height) ->
	case ar_fork:height_1_8() of
		H when Height >= H ->
			binary:decode_unsigned(BDSHash, big) > Diff;
		_ ->
			case BDSHash of
				<< 0:Diff, _/bitstring >> ->
					true;
				_ ->
					false
			end
	end.

%% @doc Validate Succinct Proof of Random Access.
validate_spora(BDS, Nonce, Timestamp, Height, Diff, PrevH, SearchSpaceUpperBound, SPoA, BI) ->
	H0 = ar_weave:hash(BDS, Nonce, Height),
	case validate(H0, ?SPORA_SLOW_HASH_DIFF(Height), Height) of
		false ->
			false;
		true ->
			SolutionHash = spora_solution_hash(PrevH, Timestamp, H0, SPoA#poa.chunk, Height),
			case validate(SolutionHash, Diff, Height) of
				false ->
					false;
				true ->
					case pick_recall_byte(H0, PrevH, SearchSpaceUpperBound, Height) of
						{error, weave_size_too_small} ->
							SPoA == #poa{};
						{ok, RecallByte} ->
							case ar_poa:validate(RecallByte, BI, SPoA) of
								false ->
									false;
								true ->
									{true, SolutionHash}
							end
					end
			end
	end.

%% @doc Maximum linear difficulty.
%% Assumes 256 bit RandomX hashes.
%% @end
max_difficulty() ->
	erlang:trunc(math:pow(2, 256)).

-ifdef(DEBUG).
min_difficulty(_Height) ->
	1.
-else.
min_difficulty(Height) ->
	Diff = case Height >= ar_fork:height_1_7() of
		true ->
			case Height >= ar_fork:height_2_4() of
				true ->
					min_spora_difficulty(Height);
				false ->
					min_randomx_difficulty()
			end;
		false ->
			min_sha384_difficulty()
	end,
	case Height >= ar_fork:height_1_8() of
		true ->
			ar_retarget:switch_to_linear_diff(Diff);
		false ->
			Diff
	end.
-endif.

sha384_diff_to_randomx_diff(Sha384Diff) ->
	max(Sha384Diff + ?RANDOMX_DIFF_ADJUSTMENT, min_randomx_difficulty()).

%%%===================================================================
%%% Private functions.
%%%===================================================================

%% @doc Takes a state and a set of transactions and return a new state with the
%% new set of transactions.
%% @end
update_txs(
	S = #state {
		current_block = CurrentB,
		data_segment_duration = BDSGenerationDuration,
		block_txs_pairs = BlockTXPairs,
		reward_addr = RewardAddr,
		candidate_block = #block{ height = Height } = CandidateB,
		txs = TXs
	}
) ->
	Rate =
		case Height > ar_fork:height_2_5() of
			true ->
				CurrentB#block.usd_to_ar_rate;
			false ->
				?USD_TO_AR_INITIAL_RATE
		end,
	NextBlockTimestamp = next_block_timestamp(BDSGenerationDuration),
	NextDiff = calc_diff(CurrentB, NextBlockTimestamp),
	ValidTXs =
		ar_tx_replay_pool:pick_txs_to_mine(
			BlockTXPairs,
			CurrentB#block.height,
			Rate,
			NextBlockTimestamp,
			ar_wallets:get(CurrentB#block.wallet_list, ar_tx:get_addresses(TXs)),
			TXs
		),
	BlockSize2 =
		lists:foldl(
			fun(TX, Acc) ->
				Acc + TX#tx.data_size
			end,
			0,
			ValidTXs
		),
	WeaveSize2 = CurrentB#block.weave_size + BlockSize2,
	{FinderReward, EndowmentPool} =
		ar_pricing:get_miner_reward_and_endowment_pool({
			CurrentB#block.reward_pool,
			ValidTXs,
			RewardAddr,
			WeaveSize2,
			CandidateB#block.height,
			NextBlockTimestamp,
			Rate
		}),
	Addresses = [RewardAddr | ar_tx:get_addresses(ValidTXs)],
	Wallets = ar_wallets:get(CurrentB#block.wallet_list, Addresses),
	AppliedTXsWallets = ar_node_utils:apply_txs(Wallets, ValidTXs, CurrentB#block.height),
	RewardWalletBeforeMiningReward =
		case maps:get(RewardAddr, AppliedTXsWallets, not_found) of
			not_found ->
				not_in_the_list;
			{Balance, LastTX} ->
				{RewardAddr, Balance, LastTX}
		end,
	Wallets2 =
		ar_node_utils:apply_mining_reward(AppliedTXsWallets, RewardAddr, FinderReward),
	{ok, RootHash2} =
		ar_wallets:add_wallets(
			CurrentB#block.wallet_list,
			Wallets2,
			RewardAddr,
			Height
		),
	CandidateB2 =
		CandidateB#block{
			txs = [TX#tx.id || TX <- ValidTXs],
			tx_root = ar_block:generate_tx_root_for_block(ValidTXs),
			block_size = BlockSize2,
			weave_size = WeaveSize2,
			wallet_list = RootHash2,
			reward_pool = EndowmentPool
		},
	BDSBase = ar_block:generate_block_data_segment_base(CandidateB2),
	update_data_segment(
		S#state{
			candidate_block = CandidateB2,
			bds_base = BDSBase,
			reward_wallet_before_mining_reward = RewardWalletBeforeMiningReward,
			txs = ValidTXs
		},
		NextBlockTimestamp,
		NextDiff
	).

%% @doc Generate a new timestamp to be used in the next block. To compensate for
%% the time it takes to generate the block data segment, adjust the timestamp
%% with the same time it took to generate the block data segment the last time.
%% @end
next_block_timestamp(BDSGenerationDuration) ->
	os:system_time(seconds) + BDSGenerationDuration.

%% @doc Given a block calculate the difficulty to mine on for the next block.
%% Difficulty is retargeted each ?RETARGET_BlOCKS blocks, specified in ar.hrl
%% This is done in attempt to maintain on average a fixed block time.
%% @end
calc_diff(CurrentB, NextBlockTimestamp) ->
	ar_retarget:maybe_retarget(
		CurrentB#block.height + 1,
		CurrentB#block.diff,
		NextBlockTimestamp,
		CurrentB#block.last_retarget
	).

%% @doc Generate a new data_segment and update the timestamp and diff.
update_data_segment(
	S = #state {
		data_segment_duration = BDSGenerationDuration,
		current_block = CurrentB
	}
) ->
	Timestamp = next_block_timestamp(BDSGenerationDuration),
	Diff = calc_diff(CurrentB, Timestamp),
	update_data_segment(S, Timestamp, Diff).

update_data_segment(State, Timestamp, Diff) ->
	#state{ candidate_block = #block{ height = Height } } = State,
	case Height >= ar_fork:height_2_5() of
		true ->
			update_data_segment2(State, Timestamp, Diff);
		false ->
			update_data_segment_pre_fork_2_5(State, Timestamp, Diff)
	end.

update_data_segment2(State, Timestamp, Diff) ->
	#state{
		current_block = CurrentB,
		candidate_block = #block{ height = Height } = CandidateB,
		bds_base = BDSBase
	} = State,
	LastRetarget2 =
		case ar_retarget:is_retarget_height(Height) of
			true ->
				Timestamp;
			false ->
				CurrentB#block.last_retarget
		end,
	CDiff =
		ar_difficulty:next_cumulative_diff(
			CurrentB#block.cumulative_diff,
			Diff,
			Height
		),
	{DurationMicros, BDS2} =
		timer:tc(
			fun() ->
				ar_block:generate_block_data_segment(
					BDSBase,
					CandidateB#block.hash_list_merkle,
					#{
						timestamp => Timestamp,
						last_retarget => LastRetarget2,
						diff => Diff,
						cumulative_diff => CDiff,
						reward_pool => CandidateB#block.reward_pool,
						wallet_list => CandidateB#block.wallet_list
					}
				)
			end
		),
	CandidateB2 =
		CandidateB#block{
			timestamp = Timestamp,
			last_retarget = LastRetarget2,
			diff = Diff,
			cumulative_diff = CDiff
		},
	State2 =
		State#state {
			timestamp = Timestamp,
			diff = Diff,
			data_segment = BDS2,
			data_segment_duration = round(DurationMicros / 1000000),
			candidate_block = CandidateB2
		},
	reschedule_timestamp_refresh(State2).

update_data_segment_pre_fork_2_5(S, BlockTimestamp, Diff) ->
	#state{
		current_block = CurrentB,
		candidate_block = CandidateB,
		reward_addr = RewardAddr,
		bds_base = BDSBase,
		reward_wallet_before_mining_reward = RewardWalletBeforeMiningReward,
		txs = TXs
	} = S,
	Height = CandidateB#block.height,
	LastRetarget2 =
		case ar_retarget:is_retarget_height(Height) of
			true -> BlockTimestamp;
			false -> CurrentB#block.last_retarget
		end,
	{MinerReward, RewardPool} =
		ar_pricing:get_miner_reward_and_endowment_pool({
			CurrentB#block.reward_pool,
			TXs,
			RewardAddr,
			CandidateB#block.weave_size,
			Height,
			BlockTimestamp,
			?USD_TO_AR_INITIAL_RATE
		}),
	RewardWallet = case RewardWalletBeforeMiningReward of
		not_in_the_list ->
			#{};
		{Addr, Balance, LastTX} ->
			#{ Addr => {Balance, LastTX} }
	end,
	RewardWallet2 =
		case maps:get(
			RewardAddr,
			ar_node_utils:apply_mining_reward(RewardWallet, RewardAddr, MinerReward),
			not_found
		) of
			not_found ->
				#{};
			WalletData ->
				#{ RewardAddr => WalletData }
		end,
	{ok, RootHash2} =
		ar_wallets:update_wallets(
			CandidateB#block.wallet_list,
			RewardWallet2,
			RewardAddr,
			Height
		),
	CDiff = ar_difficulty:next_cumulative_diff(
		CurrentB#block.cumulative_diff,
		Diff,
		Height
	),
	{DurationMicros, BDS2} = timer:tc(
		fun() ->
			ar_block:generate_block_data_segment(
				BDSBase,
				CandidateB#block.hash_list_merkle,
				#{
					timestamp => BlockTimestamp,
					last_retarget => LastRetarget2,
					diff => Diff,
					cumulative_diff => CDiff,
					reward_pool => RewardPool,
					wallet_list => RootHash2
				}
			)
		end
	),
	CandidateB2 =
		CandidateB#block{
			timestamp = BlockTimestamp,
			last_retarget = LastRetarget2,
			diff = Diff,
			cumulative_diff = CDiff,
			reward_pool = RewardPool,
			wallet_list = RootHash2
		},
	S2 =
		S#state {
			timestamp = BlockTimestamp,
			diff = Diff,
			data_segment = BDS2,
			data_segment_duration = round(DurationMicros / 1000000),
			candidate_block = CandidateB2
		},
	reschedule_timestamp_refresh(S2).

reschedule_timestamp_refresh(S = #state{
	timestamp_refresh_timer = Timer,
	data_segment_duration = BDSGenerationDuration,
	txs = TXs
}) ->
	timer:cancel(Timer),
	case ?MINING_TIMESTAMP_REFRESH_INTERVAL - BDSGenerationDuration  of
		TimeoutSeconds when TimeoutSeconds =< 0 ->
			TXIDs = lists:map(fun(TX) -> TX#tx.id end, TXs),
			?LOG_WARNING([
				{event, ar_mine_slow_data_segment_generation},
				{duration, BDSGenerationDuration},
				{timestamp_refresh_interval, ?MINING_TIMESTAMP_REFRESH_INTERVAL},
				{txs_count, length(TXIDs)}
			]),
			self() ! refresh_timestamp,
			S#state{ timestamp_refresh_timer = no_timer };
		TimeoutSeconds ->
			case timer:send_after(TimeoutSeconds * 1000, refresh_timestamp) of
				{ok, Ref} ->
					S#state{ timestamp_refresh_timer = Ref };
				{error, Reason} ->
					?LOG_ERROR("ar_mine: Reschedule timestamp refresh failed: ~p", [Reason]),
					S
			end
	end.

%% @doc Start the main mining server.
start_server(S) ->
	spawn(fun() ->
		try
			server(start_miners(update_txs(S)))
		catch Type:Exception ->
			?LOG_ERROR(
				"event: mining_server_exception, type: ~p, exception: ~p",
				[Type, Exception]
			)
		end
	end).

%% @doc The main mining server.
server(
	S = #state {
		miners = Miners,
		started_at = StartedAt,
		txs = MinedTXs,
		candidate_block = #block { diff = Diff, timestamp = Timestamp },
		total_sporas_tried = TotalSPoRAsTried,
		total_sporas_discovered = TotalSPoRAsDiscovered
	}
) ->
	receive
		%% Stop the mining process and all the workers.
		stop ->
			stop_miners(Miners),
			log_spora_performance(TotalSPoRAsTried, TotalSPoRAsDiscovered, StartedAt);
		%% The block timestamp must be reasonable fresh since it's going to be
		%% validated on the remote nodes when it's propagated to them. Only blocks
		%% with a timestamp close to current time will be accepted in the propagation.
		refresh_timestamp ->
			server(restart_miners(update_data_segment(S)));
		{sporas_tried, SPoRAsTried} ->
			server(
				S#state{
					total_sporas_tried = TotalSPoRAsTried + SPoRAsTried,
					total_sporas_discovered = TotalSPoRAsDiscovered + SPoRAsTried
				}
			);
		{sporas_discovered, SPoRAsDiscovered} ->
			server(
				S#state{
					total_sporas_discovered = TotalSPoRAsDiscovered + SPoRAsDiscovered
				}
			);
		{spora_solution, Hash, Nonce, SPoA, Timestamp} ->
			process_spora_solution(S, Hash, Nonce, SPoA, MinedTXs, Diff, Timestamp);
		{spora_solution, _, _, _, _} ->
			%% A stale solution.
			server(S);
		UnexpectedMessage ->
			?LOG_WARNING(
				"event: mining_server_got_unexpected_message, message: ~p",
				[UnexpectedMessage]
			),
			server(S)
	end.

process_spora_solution(S, Hash, Nonce, SPoA, MinedTXs, Diff, Timestamp) ->
	#state {
		parent = Parent,
		miners = Miners,
		current_block = #block{ indep_hash = CurrentBH },
		total_sporas_tried = TotalSPoRAsTried,
		total_sporas_discovered = TotalSPoRAsDiscovered,
		started_at = StartedAt,
		data_segment = BDS,
		candidate_block = #block { diff = Diff, timestamp = Timestamp } = CandidateB
	} = S,
	NewBBeforeHash = CandidateB#block{
		nonce = Nonce,
		hash = Hash,
		poa = SPoA
	},
	IndepHash = ar_weave:indep_hash(BDS, Hash, Nonce, SPoA),
	NewB = NewBBeforeHash#block{ indep_hash = IndepHash },
	Parent ! {work_complete, CurrentBH, NewB, MinedTXs, BDS, SPoA},
	log_spora_performance(TotalSPoRAsTried, TotalSPoRAsDiscovered, StartedAt),
	stop_miners(Miners).

log_spora_performance(TotalSPoRAsTried, TotalSPoRAsDiscovered, StartedAt) ->
	Time = timer:now_diff(erlang:timestamp(), StartedAt),
	Rate = TotalSPoRAsTried / (Time / 1000000),
	prometheus_histogram:observe(mining_rate, Rate),
	DiscoverRate = TotalSPoRAsDiscovered / (Time / 1000000),
	?LOG_INFO([
		{event, stopped_mining},
		{miner_sporas_per_second, Rate},
		{miner_discovered_sporas_per_second, DiscoverRate}
	]),
	ar:console("Miner spora rate: ~B h/s.~n", [erlang:trunc(Rate)]).

%% @doc Start the workers and return the new state.
start_miners(
	S = #state{
		max_miners = MaxMiners,
		candidate_block = #block{ height = Height, previous_block = PrevH },
		diff = Diff,
		block_index = BI,
		data_segment = BDS,
		timestamp = Timestamp
	}
) ->
	SearchSpaceUpperBound = get_search_space_upper_bound(BI, Height),
	WorkerState = #{
		data_segment => BDS,
		diff => Diff,
		timestamp => Timestamp,
		height => Height,
		prev_h => PrevH,
		search_space_upper_bound => SearchSpaceUpperBound
	},
	Miners = [spawn(?MODULE, mine_spora, [WorkerState, self()]) || _ <- lists:seq(1, MaxMiners)],
	S#state{ miners = Miners }.

%% @doc Stop all workers.
stop_miners(Miners) ->
	lists:foreach(
		fun(PID) ->
			exit(PID, stop)
		end,
		Miners
	).

%% @doc Stop and then start the workers again and return the new state.
restart_miners(S) ->
	stop_miners(S#state.miners),
	start_miners(S).

get_search_space_upper_bound(BI, Height) ->
	SearchSpaceUpperBoundDepth = ?SEARCH_SPACE_UPPER_BOUND_DEPTH(Height),
	case length(BI) < SearchSpaceUpperBoundDepth of
		true ->
			element(2, lists:last(BI));
		false ->
			element(2, lists:nth(SearchSpaceUpperBoundDepth, BI))
	end.

%% @doc Search for a Succinct Proof of Random Access.
mine_spora(
	#{
		data_segment := BDS,
		diff := Diff,
		timestamp := Timestamp,
		height := Height,
		prev_h := PrevH,
		search_space_upper_bound := SearchSpaceUpperBound
	} = WorkerState,
	Supervisor
) ->
	case randomx_hasher(Height) of
		{ok, Hasher} ->
			StartNonce = crypto:strong_rand_bytes(256 div 8),
			{Nonce, H0} = find_rx_hash(Hasher, StartNonce, BDS, Height),
			SPoA =
				case pick_recall_byte(H0, PrevH, SearchSpaceUpperBound, Height) of
					{error, weave_size_too_small} ->
						#poa{};
					{ok, RecallByte} ->
						ar_poa:get_poa_from_v2_index(RecallByte)
				end,
			case SPoA of
				not_found ->
					Supervisor ! {sporas_discovered, 1},
					mine_spora(WorkerState, Supervisor);
				_ ->
					SolutionHash =
						spora_solution_hash(PrevH, Timestamp, H0, SPoA#poa.chunk, Height),
					case validate(SolutionHash, Diff, Height) of
						false ->
							Supervisor ! {sporas_tried, 1},
							mine_spora(WorkerState, Supervisor);
						true ->
							Supervisor ! {spora_solution, SolutionHash, Nonce, SPoA, Timestamp}
					end
			end;
		not_found ->
			?LOG_INFO([{event, mining_waiting_on_randomx_initialization}]),
			timer:sleep(30 * 1000),
			mine_spora(WorkerState, Supervisor)
	end.

randomx_hasher(Height) ->
	case ar_randomx_state:randomx_state_by_height(Height) of
		{state, {fast, FastState}} ->
			%% Use RandomX fast-mode, where hashing is fast but initialization is slow.
			Hasher = fun(Nonce, BDS) ->
				ar_mine_randomx:hash_fast(FastState, << Nonce/binary, BDS/binary >>)
			end,
			{ok, Hasher};
		{state, {light, _}} ->
			not_found;
		{key, _} ->
			not_found
	end.

find_rx_hash(Hasher, Nonce, BDS, Height) ->
	H = Hasher(Nonce, BDS),
	case validate(H, ?SPORA_SLOW_HASH_DIFF(Height), Height) of
		true ->
			{Nonce, H};
		false ->
			find_rx_hash(Hasher, H, BDS, Height)
	end.

pick_recall_byte(H, PrevH, SearchSpaceUpperBound, Height) ->
	Subspaces = ?SPORA_SEARCH_SPACE_SUBSPACES_COUNT(Height),
	SubspaceNumber = binary:decode_unsigned(H, big) rem Subspaces,
	EvenSubspaceSize = SearchSpaceUpperBound div Subspaces,
	SearchSubspaceSize = ?SPORA_SEARCH_SPACE_SIZE(Height, SearchSpaceUpperBound) div Subspaces,
	case SearchSubspaceSize of
		0 ->
			{error, weave_size_too_small};
		_ ->
			SubspaceStart = SubspaceNumber * EvenSubspaceSize,
			SubspaceSize = min(SearchSpaceUpperBound - SubspaceStart, EvenSubspaceSize),
			EncodedSubspaceNumber = binary:encode_unsigned(SubspaceNumber),
			SearchSubspaceSeed =
				binary:decode_unsigned(
					crypto:hash(sha256, << PrevH/binary, EncodedSubspaceNumber/binary >>),
					big
				),
			SearchSubspaceStart = SearchSubspaceSeed rem SubspaceSize,
			SearchSubspaceByteSeed = binary:decode_unsigned(crypto:hash(sha256, H), big),
			SearchSubspaceByte = SearchSubspaceByteSeed rem SearchSubspaceSize,
			{ok, SubspaceStart + (SearchSubspaceStart + SearchSubspaceByte) rem SubspaceSize}
	end.

spora_solution_hash(PrevH, Timestamp, H0, Chunk, Height) ->
	ar_randomx_state:hash(
		Height,
		<< H0/binary, PrevH/binary, Timestamp:(?TIMESTAMP_FIELD_SIZE_LIMIT * 8), Chunk/binary >>
	).

-ifdef(DEBUG).
min_randomx_difficulty() -> 1.
-else.
min_randomx_difficulty() -> min_sha384_difficulty() + ?RANDOMX_DIFF_ADJUSTMENT.
min_sha384_difficulty() -> 31.
-endif.

min_spora_difficulty(Height) ->
	?SPORA_MIN_DIFFICULTY(Height).

%%%===================================================================
%%% Tests.
%%%===================================================================

%% Test that found nonces abide by the difficulty criteria.
basic_test_() ->
	{timeout, 20, fun test_basic/0}.

test_basic() ->
	[B0] = ar_weave:init([]),
	ar_test_node:start(B0),
	ar_node:mine(),
	BI = ar_test_node:wait_until_height(1),
	B1 = ar_test_node:read_block_when_stored(hd(BI)),
	start({B1, [], unclaimed, [], self(), [], BI}),
	assert_mine_output(B1, []).

%% Ensure that the block timestamp gets updated regularly while mining.
timestamp_refresh_test_() ->
	{timeout, 60, fun test_timestamp_refresh/0}.

test_timestamp_refresh() ->
	%% Start mining with a high enough difficulty, so that the block
	%% timestamp gets refreshed at least once. Since we might be unlucky
	%% and find the block too fast, we retry until it succeeds.
	[B0] = ar_weave:init([], ar_retarget:switch_to_linear_diff(18)),
	B = B0,
	Run = fun(_) ->
		TXs = [],
		StartTime = os:system_time(seconds),
		start({
			B,
			TXs,
			unclaimed,
			[],
			self(),
			[],
			[ar_util:block_index_entry_from_block(B0)]
		}),
		{_, MinedTimestamp} = assert_mine_output(B, TXs),
		MinedTimestamp > StartTime + ?MINING_TIMESTAMP_REFRESH_INTERVAL
	end,
	?assert(lists:any(Run, lists:seq(1, 20))).

%% Ensures ar_mine can be started and stopped.
start_stop_test() ->
	[B] = ar_weave:init(),
	{_Node, _} = ar_test_node:start(B),
	BI = ar_test_node:wait_until_height(0),
	HighDiff = ar_retarget:switch_to_linear_diff(30),
	PID = start({B#block{ diff = HighDiff }, [], unclaimed, [], self(), [], BI}),
	timer:sleep(500),
	assert_alive(PID),
	stop(PID),
	assert_not_alive(PID, 3000).

%% Ensures a miner can be started and stopped.
miner_start_stop_test() ->
	S = #{
		diff => ar_retarget:switch_to_linear_diff(30),
		timestamp => os:system_time(seconds),
		data_segment => <<>>,
		height => 1,
		prev_h => crypto:strong_rand_bytes(32),
		search_space_upper_bound => 1000000
	},
	PID = spawn(?MODULE, mine_spora, [S, self()]),
	timer:sleep(500),
	assert_alive(PID),
	stop_miners([PID]),
	assert_not_alive(PID, 3000).

assert_mine_output(B, TXs) ->
	receive
		{work_complete, BH, NewB, MinedTXs, BDS, _POA} ->
			?assertEqual(BH, B#block.indep_hash),
			?assertEqual(lists:sort(TXs), lists:sort(MinedTXs)),
			BDS = ar_block:generate_block_data_segment(NewB),
			#block{
				height = Height,
				previous_block = PrevH,
				timestamp = Timestamp,
				nonce = Nonce,
				poa = #poa{ chunk = Chunk }
			} = NewB,
			H0 = ar_randomx_state:hash(Height, << Nonce/binary, BDS/binary >>),
			?assertEqual(
				spora_solution_hash(PrevH, Timestamp, H0, Chunk, Height),
				NewB#block.hash
			),
			?assert(binary:decode_unsigned(NewB#block.hash) > NewB#block.diff),
			{NewB#block.diff, NewB#block.timestamp}
	after 20000 ->
		error(timeout)
	end.

assert_alive(PID) ->
	?assert(is_process_alive(PID)).

assert_not_alive(PID, Timeout) ->
	Do = fun () -> not is_process_alive(PID) end,
	?assert(ar_util:do_until(Do, 50, Timeout)).
