-module(ar_mine).
-export([start/3, start/4]).
-export([change_data/2, stop/1, validate/4]).
-include("ar.hrl").
-include_lib("eunit/include/eunit.hrl").

%%% A module for managing mining of blocks on the weave.

%% State record for miners
-record(state,{
	parent, % parent process
	hash,
	diff,
	data,
	delay
}).

%% Returns the PID of a new mining worker process.
start(Hash, Diff, Data) ->
	start(Hash, Diff, Data, 0).
start(Hash, Diff, Data, Delay) ->
	Parent = self(),
	spawn(
		fun() ->
			server(
				schedule_hash(
					#state {
						parent = Parent,
						hash = Hash,
						diff = Diff,
						data = Data,
						delay = Delay
					}
				)
			)
		end
	).

%% Stop a running miner.
stop(PID) ->
	PID ! stop.

%% Change the data attachment that the miner is using.
change_data(PID, NewData) ->
	PID ! {new_data, NewData}.

%% The main mining server.
server(
	S = #state {
		parent = Parent,
		hash = Hash,
		diff = Diff,
		data = Data
	}) ->
	receive
		stop ->
			ar:report([{miner, self()}, stopping]),
			ok;
		{new_data, NewData} ->
			server(
				S#state {
					data = NewData
				}
			);
	hash ->
		schedule_hash(S),
		case validate(Hash, Diff, Data, Nonce = generate()) of
			false -> server(S);
			NextHash ->
				ar:report([{miner, self()}, {found_block, Nonce}]),
				Parent ! {work_complete, Hash, NextHash, Diff, Nonce},
				ok
		end
	end.

%% Validate that a hash and a nonce satisfy the difficulty.
validate(Hash, Diff, Data, Nonce) ->
	case NewHash = ar_weave:hash(Hash, Data, Nonce) of
		<< 0:Diff, _/bitstring >> -> NewHash;
		_ -> false
	end.

%% Send a message to ourselves at some point in the future, asking us to mine.
schedule_hash(S = #state { delay = Delay }) ->
	Parent = self(),
	spawn(fun() -> receive after ar:scale_time(Delay) -> Parent ! hash end end),
	S.

%% Generate a random nonce, to be added to the previous hash.
generate() -> crypto:strong_rand_bytes(8).

%%% Tests

%% Test that found nonces abide by the difficulty criteria.
basic_test() ->
	LastHash = crypto:strong_rand_bytes(32),
	Data = crypto:strong_rand_bytes(32),
	Diff = 18,
	start(LastHash, Diff, Data),
	receive
		{work_complete, LastHash, _NewHash, Diff, Nonce} ->
			<< 0:Diff, _/bitstring >>
				= crypto:hash(?HASH_ALG, << LastHash/binary, Data/binary, Nonce/binary >>)
	end.

%% Ensure that we can change the data while mining is in progress.
change_data_test() ->
	LastHash = crypto:strong_rand_bytes(32),
	Data = crypto:strong_rand_bytes(32),
	NewData = crypto:strong_rand_bytes(32),
	Diff = 18,
	PID = start(LastHash, Diff, Data),
	change_data(PID, NewData),
	receive
		{work_complete, LastHash, _NewHash, Diff, Nonce} ->
			<< 0:Diff, _/bitstring >>
				= crypto:hash(?HASH_ALG, << LastHash/binary, NewData/binary, Nonce/binary >>)
	end.
