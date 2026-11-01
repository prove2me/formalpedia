-- Prove2me | Definitions.Def_OpenSearchPreVote
-- name    : OpenSearchPreVote
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-11-01T00:35:04.887819+00:00
-- url     : https://prove2.me/theorems/da684f75-3c7c-43f6-8633-cae77313afd6
-- title:
--   OpenSearch pre-voting: pre-vote requests and responses, pre-voting rounds, the election they trigger, and the election scheduler's delays
-- statement:
--   A transcription of `PreVoteCollector`, the parts of `Coordinator` it calls, and the delay computation of `ElectionSchedulerFactory`, at OpenSearch revision `b2a54ba5c0defba3d1d20423e911d4bf920bab19`, over the per-node `CoordinationState` of the `OpenSearchCoordination` mission (whose `DiscoveryNode`, `ClusterState`, `VoteCollection`, `ElectionStrategy`, `Join`, `CoordinationState`, `handleStartJoin` and `handleJoin` are used as they are).
--
--   **Messages.** **`PreVoteRequest`** — the requesting node and its current term. **`PreVoteResponse`** — the responder's current term, and the term and the version (the metadata version, for a term-0 state) of its last accepted state. **`preVoteResponseOf cs`** — the response a node with coordination state `cs` gives: `cs.currentTerm`, `cs.lastAcceptedTerm`, `cs.lastAcceptedVersionOrMetadataVersion` (`Coordinator.getPreVoteResponse`).
--
--   **Answering.** **`CollectorState`** — the known leader (`none` when no leader is known) and the node's own response, as last set by the `Coordinator` (itself when it becomes leader, the leader it follows, `none` when it becomes a candidate). **`handlePreVoteRequest healthy st req`** — rejects if the node is not healthy; otherwise answers with `st.response` if the node knows no leader or knows `req.sourceNode` as its leader, and rejects if it knows another leader.
--
--   **Rounds.** **`PreVotingRound V`** — the requester's last accepted cluster state when the round started, the requester (`localNode`), the recorded pre-votes as a list of (sender, response) pairs, most recent first, and the flags `electionStarted` and `isClosed`. **`PreVotingRound.start s n`** — an open round over `s` for requester `n`, with no pre-votes and no election started. **`votes r`** — the vote collection built by adding the vote of each recorded sender to the empty collection (only cluster-manager-eligible senders count). **`isElectionQuorumFor es n t at av committed accepted votes`** — `ElectionStrategy.isElectionQuorum` with explicit arguments: `votes` is a quorum of `committed` and of `accepted`, and the strategy's additional constraint holds for the local node `n`, current term `t`, accepted term `at` and version `av`, the two configurations and `votes`.
--
--   **`r.handlePreVoteResponse es lr resp sender`** (PVC:225-279) returns the new round, whether `startElection` is called, and the term passed to `updateMaxTermSeen` (`none` if none is passed); `lr` is the requester's own current response, read when the response arrives. If the round is closed: unchanged, `false`, `none`. Otherwise, if `resp` is fresher than the round's accepted state `s` — `resp.lastAcceptedTerm > s.term`, or equal terms and `resp.lastAcceptedVersion > s.versionOrMetadataVersion` — the round is unchanged, with `false` and `some resp.currentTerm`. Otherwise the pair `(sender, resp)` replaces any earlier entry of `sender`; if the new votes are not an election quorum (`isElectionQuorumFor es r.localNode lr.currentTerm lr.lastAcceptedTerm lr.lastAcceptedVersion` over the last committed and last accepted configurations of `s`), or the round has already started an election, the result is that round with `false`; otherwise the round with `electionStarted` set, and `true`. In every case but the closed one, the term passed is `some resp.currentTerm`. **`close r`** — the round with `isClosed` set.
--
--   **`NoFresher resp s`** — `resp.lastAcceptedTerm < s.term`, or `resp.lastAcceptedTerm = s.term` and `resp.lastAcceptedVersion ≤ s.versionOrMetadataVersion`: the responses a round records. **`RoundReachable es Delivered`** — the rounds obtained from `start s n` (any `s`, `n`) by handling, any number of times and in any order, responses `resp` from senders `n` with `Delivered n resp` (each step with an arbitrary requester response `lr`), and by `close`.
--
--   **The election.** **`handleJoins es cs js`** — the joins of `js` handled in order by `CoordinationState.handleJoin`; a rejected join leaves the state unchanged. For joins whose term is not above the node's current term this is `Coordinator.handleJoin` (CO:1267-1299); a join of a higher term is rejected here (term mismatch), whereas the `Coordinator` first moves the node to that term (CO:1269). The joins' target is not checked (Java asserts it). **`startElectionTerm currentTerm maxTermSeen`** — `max currentTerm maxTermSeen + 1`, the term of the `StartJoinRequest` that `startElection` sends (CO:593). **`nodeMayWinElection s excluded n`** — `n` is in the last committed or the last accepted configuration of `s`, or is not among the excluded ids (CO:628-633); it is not used by the theorems.
--
--   **The scheduler** (times in milliseconds). **`SchedulerSettings`** — `initialTimeout`, `backoffTime`, `maxTimeout`, `duration`. **`Valid`** — the setting ranges (`1 ≤ initialTimeout ≤ 10000`, `1 ≤ backoffTime ≤ 60000`, `200 ≤ maxTimeout ≤ 300000`, `1 ≤ duration ≤ 300000`) and the constructor's check `initialTimeout ≤ maxTimeout`. **`default`** — 100, 100, 10000, 500 (not used by the theorems). **`maxDelay s k`** — `min(maxTimeout, initialTimeout + k · backoffTime)`, the bound for attempt `k` (counted from 0). **`nonNegative n`** — 0 for `n = -2^63` (`Long.MIN_VALUE`), `|n|` otherwise. **`toPositiveLongAtMost r b`** — `nonNegative r mod b + 1`. **`attemptDelay s k r g`** — `toPositiveLongAtMost r (maxDelay s k) + g`, the delay of attempt `k` for the drawn random long `r` and the grace period `g`, a free parameter (Java passes 0 for the first attempt, CO:1574, and `duration` for the later ones, ESF:218; the field `duration` occurs only in `Valid`).
--
--   **Formalization Note.** The `Coordinator`'s side effects are not modelled. The argument of `updateMaxTermSeen` is returned by `handlePreVoteResponse`, and not at all by `handlePreVoteRequest` (where it is always the request's term); the call's effect is outside these functions: in particular a leader whose current term is below the largest term it has seen moves to that term and starts an election, at once or, while a publication is in progress, when that publication ends (CO:560-581, CO:1784). Nodes are compared by id and role, while Java's `DiscoveryNode.equals` compares ephemeral ids, which change at each restart: the two can differ only between two incarnations of one node with the same role. The election strategy sees voter ids only (the per-node mission's abstraction). Health is a Boolean parameter, the network is the delivery predicate of `RoundReachable`, and the random long is any integer: the theorems hold for every value. Only the per-node mission's definitions are imported.
-- source:
--   OpenSearch b2a54ba5c0defba3d1d20423e911d4bf920bab19: PreVoteCollector (state line 79, start 111-115, update 128-131, handlePreVoteRequest 133-163, PreVotingRound 175-300, handlePreVoteResponse 225-279, close 296-299): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/PreVoteCollector.java#L66-L301; Coordinator (updateMaxTermSeen lines 560-581, startElection 583-602, nodeMayWinElection 628-633, getPreVoteResponse 873-879, handleJoin 1267-1299, startElectionScheduler 1567-1618, the preVoteCollector.update calls 516, 653, 777, 801, 839, 1157): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/Coordinator.java#L560-L633; ElectionSchedulerFactory (settings lines 85-115, constructor check 133-143, nonNegative 159-161, toPositiveLongAtMost 169-172, scheduleNextElection 195-241): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ElectionSchedulerFactory.java#L62-L254; ElectionStrategy.isElectionQuorum (lines 68-88): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ElectionStrategy.java#L68-L88; the messages PreVoteRequest.java and PreVoteResponse.java in the same directory; CoordinationState (handleStartJoin, handleJoin) as transcribed by the OpenSearchCoordination mission

import Definitions.Def_OpenSearchCoordination

/-!
# OpenSearch cluster coordination: pre-voting and election scheduling

Before a node starts an election it runs a **pre-voting round** (`PreVoteCollector`, OpenSearch
`b2a54ba5c0defba3d1d20423e911d4bf920bab19`,
`server/src/main/java/org/opensearch/cluster/coordination/PreVoteCollector.java`, cited `PVC:<line>`): it asks the nodes
it has discovered, including itself, for a pre-vote. A node answers with its current term and the term and version of
its last accepted state, unless it is unhealthy or already follows a leader other than the requester. The round counts
the answers that are no fresher than the requester's own accepted state, and when they form an election quorum the
requester starts an election (`Coordinator.startElection`, Coordinator.java, cited `CO:<line>`): it sends a
`StartJoinRequest` in a term above every term it has seen. Pre-voting rounds are started by an **election scheduler**
(`ElectionSchedulerFactory`, cited `ESF:<line>`) at randomized, backed-off intervals.

The pre-vote messages and handlers are transcribed below as functions. Both handlers raise the Coordinator's
`maxTermSeen` (`updateMaxTermSeen`, CO:560-581): `handlePreVoteRequest` first of all, with the request's term (PVC:134);
`handlePreVoteResponse` once it has found the round open, with the response's current term, before the freshness test
(PVC:226-231). `handlePreVoteResponse` returns the term it passes (`none` when the round is closed);
`handlePreVoteRequest` returns nothing, its argument being always the request's term. When `maxTermSeen` exceeds the
current term of a leader, the leader moves to that term and starts an election itself, at once or, while a publication
is in progress, when that publication ends (CO:564-578, CO:1784); that effect is outside these functions.

Node equality: Java's `DiscoveryNode.equals` compares ephemeral ids, which change when a node restarts; here nodes are
compared by id and role. The two can differ only between two incarnations of the same node with the same role, which
Java treats as different nodes (so a follower of a node's previous incarnation with the same role refuses that node's
pre-vote request in Java, and accepts it here).
-/

namespace OpenSearchPreVote

open OpenSearchCoordination

variable {V : Type}

/-- `PreVoteRequest` (PreVoteRequest.java): the requesting node and its current term. -/
structure PreVoteRequest where
  sourceNode : DiscoveryNode
  currentTerm : Nat
  deriving DecidableEq, Repr

/-- `PreVoteResponse` (PreVoteResponse.java): the responder's current term and the term and version (or metadata
version, for a term-0 state) of its last accepted state. -/
structure PreVoteResponse where
  currentTerm : Nat
  lastAcceptedTerm : Nat
  lastAcceptedVersion : Int
  deriving DecidableEq, Repr

/-- `Coordinator.getPreVoteResponse()` (CO:873-879): the response a node gives, computed from its coordination state. -/
def preVoteResponseOf (cs : CoordinationState V) : PreVoteResponse :=
  ⟨cs.currentTerm, cs.lastAcceptedTerm, cs.lastAcceptedVersionOrMetadataVersion⟩

/-- The pre-vote collector's state (PVC:79): the known leader (`none` is Java `null`, no known leader) and the node's
own response, both as last set by `update` (PVC:128-131) — `Coordinator` sets the leader to itself when it becomes
leader, to the leader it follows when it becomes a follower, and to `null` when it becomes a candidate (CO:516, 653, 777,
801, 839, 1157). Java's state is `null` before the first `update`; a node answers pre-votes only after it. -/
structure CollectorState where
  leader : Option DiscoveryNode
  response : PreVoteResponse
  deriving DecidableEq, Repr

/-- `PreVoteCollector.handlePreVoteRequest(request)` (PVC:133-163). `healthy` is the node health status
(`nodeHealthService.getHealth()`). A node that knows a leader other than the requester refuses. (Before answering, the
handler calls `updateMaxTermSeen(request.getCurrentTerm())`, PVC:134; see the module documentation.) -/
def handlePreVoteRequest (healthy : Bool) (st : CollectorState) (req : PreVoteRequest) :
    Except String PreVoteResponse :=
  if !healthy then .error "rejecting on unhealthy node"
  else match st.leader with
    | none => .ok st.response
    | some l => if l = req.sourceNode then .ok st.response else .error "rejecting as there is already a leader"

/-- A pre-voting round (`PreVoteCollector.PreVotingRound`, PVC:175-300): the last accepted cluster state of the
requester when the round started, the requester, the pre-votes received so far (Java: a map keyed by sender; here a
list, most recent first, which in every reachable round has at most one entry per sender, a sender being a node value,
id and role, as `round_entries` proves; the type itself allows repeats), whether it has started an election, and
whether it was closed.
Java takes the requester from the round's cluster state (`clusterState.nodes().getLocalNode()`, PVC:244); the request's
term (PVC:112) is not needed here. -/
structure PreVotingRound (V : Type) where
  clusterState : ClusterState V
  localNode : DiscoveryNode
  preVotesReceived : List (DiscoveryNode × PreVoteResponse)
  electionStarted : Bool
  isClosed : Bool

/-- `PreVoteCollector.start` (PVC:111-115): a new, open round over the requester's last accepted state. -/
def PreVotingRound.start (s : ClusterState V) (localNode : DiscoveryNode) : PreVotingRound V :=
  ⟨s, localNode, [], false, false⟩

/-- The `VoteCollection` the round builds from its pre-votes (PVC:242-257): `addJoinVote` of a join from each sender,
which counts the cluster-manager-eligible senders. -/
def PreVotingRound.votes (r : PreVotingRound V) : VoteCollection :=
  r.preVotesReceived.foldr (fun p v => (v.addVote p.1).1) VoteCollection.empty

/-- `ElectionStrategy.isElectionQuorum` (ElectionStrategy.java:68-88), as called with explicit arguments. -/
def isElectionQuorumFor (es : ElectionStrategy) (localNode : DiscoveryNode) (currentTerm acceptedTerm : Nat)
    (acceptedVersion : Int) (committed accepted : VotingConfiguration) (votes : VoteCollection) : Bool :=
  votes.isQuorum committed && votes.isQuorum accepted &&
    es.satisfiesAdditionalQuorumConstraints localNode currentTerm acceptedTerm acceptedVersion committed accepted votes

/-- `PreVotingRound.handlePreVoteResponse(response, sender)` (PVC:225-279). `localResponse` is the requester's own
current response (`getPreVoteResponse()`, read when the response arrives). Returns the new round, whether
`startElection` is called, and the argument of the `updateMaxTermSeen` call (`none` when the round is closed and the
response is ignored before it). A response fresher than the round's accepted state is ignored. -/
def PreVotingRound.handlePreVoteResponse (es : ElectionStrategy) (localResponse : PreVoteResponse)
    (r : PreVotingRound V) (resp : PreVoteResponse) (sender : DiscoveryNode) :
    PreVotingRound V × Bool × Option Nat :=
  if r.isClosed then (r, false, none)
  else if resp.lastAcceptedTerm > r.clusterState.term ∨
      (resp.lastAcceptedTerm = r.clusterState.term ∧
        resp.lastAcceptedVersion > r.clusterState.versionOrMetadataVersion) then
    (r, false, some resp.currentTerm)
  else
    let r₁ : PreVotingRound V :=
      { r with preVotesReceived := (sender, resp) :: r.preVotesReceived.filter (fun p => p.1 ≠ sender) }
    if !isElectionQuorumFor es r.localNode localResponse.currentTerm localResponse.lastAcceptedTerm
        localResponse.lastAcceptedVersion r.clusterState.lastCommittedConfiguration
        r.clusterState.lastAcceptedConfiguration r₁.votes then
      (r₁, false, some resp.currentTerm)
    else if r₁.electionStarted then
      (r₁, false, some resp.currentTerm)
    else
      ({ r₁ with electionStarted := true }, true, some resp.currentTerm)

/-- `PreVotingRound.close()` (PVC:296-299). -/
def PreVotingRound.close (r : PreVotingRound V) : PreVotingRound V := { r with isClosed := true }

/-- A pre-vote response is no fresher than the accepted state `s`: its accepted (term, version) is lexicographically at
most `s`'s (term, version-or-metadata-version) — the responses a round counts (PVC:233-238). -/
def NoFresher (resp : PreVoteResponse) (s : ClusterState V) : Prop :=
  resp.lastAcceptedTerm < s.term ∨
    (resp.lastAcceptedTerm = s.term ∧ resp.lastAcceptedVersion ≤ s.versionOrMetadataVersion)

/-- The rounds a node can be in: started over any cluster state for any requester (in Java, over the requester's last
accepted state; the theorems that need this link assume it), then any sequence of responses handled — each response
from a sender and with a content allowed by `Delivered` — and possibly closed. `localResponse` (the requester's own
current response) is arbitrary at each step. -/
inductive RoundReachable (es : ElectionStrategy) (Delivered : DiscoveryNode → PreVoteResponse → Prop) :
    PreVotingRound V → Prop where
  | start (s : ClusterState V) (n : DiscoveryNode) : RoundReachable es Delivered (PreVotingRound.start s n)
  | handle (r : PreVotingRound V) (localResponse resp : PreVoteResponse) (sender : DiscoveryNode) :
      RoundReachable es Delivered r → Delivered sender resp →
      RoundReachable es Delivered (r.handlePreVoteResponse es localResponse resp sender).1
  | close (r : PreVotingRound V) : RoundReachable es Delivered r → RoundReachable es Delivered r.close

/-- The joins a node handles, in the order given, as `Coordinator.handleJoin` (CO:1267-1287, with
`handleJoinIgnoringExceptions`, CO:1289-1299) does for joins whose term is not above the node's current term. A join
of a higher term is rejected here (term mismatch), whereas the `Coordinator` first moves the node to that term
(CO:1269). A rejected join leaves the state unchanged: `handleJoin` throws before changing anything, and
`Coordinator.handleJoin` either propagates the exception to the joining node or ignores it. The joins' target node is
not checked (Java asserts it, CoordinationState.java:265). -/
def handleJoins (es : ElectionStrategy) (cs : CoordinationState V) (js : List Join) : CoordinationState V :=
  js.foldl (fun cs j => match cs.handleJoin es j with
    | .ok (cs', _) => cs'
    | .error _ => cs) cs

/-- The term of the election `Coordinator.startElection` starts (CO:583-602): one above the larger of the current term
and the largest term seen. -/
def startElectionTerm (currentTerm maxTermSeen : Nat) : Nat := max currentTerm maxTermSeen + 1

/-- `Coordinator.nodeMayWinElection` (CO:628-633): the node is in the last committed or last accepted configuration,
or it is not excluded from voting. `excluded` lists the node ids of the voting-configuration exclusions. -/
def nodeMayWinElection (s : ClusterState V) (excluded : List NodeId) (n : NodeId) : Bool :=
  s.lastCommittedConfiguration.nodeIds.contains n || s.lastAcceptedConfiguration.nodeIds.contains n ||
    !(excluded.contains n)

/-! ## Election scheduling (`ElectionSchedulerFactory`) -/

/-- The scheduler settings, in milliseconds (ESF:85-115): `cluster.election.initial_timeout` (default 100, range
1..10000), `cluster.election.back_off_time` (default 100, range 1..60000), `cluster.election.max_timeout` (default 10000,
range 200..300000, at least the initial timeout), `cluster.election.duration` (default 500, range 1..300000). -/
structure SchedulerSettings where
  initialTimeout : Nat
  backoffTime : Nat
  maxTimeout : Nat
  duration : Nat

/-- The settings' validity (setting bounds, ESF:85-115, and the constructor check, ESF:133-143). -/
def SchedulerSettings.Valid (s : SchedulerSettings) : Prop :=
  1 ≤ s.initialTimeout ∧ s.initialTimeout ≤ 10000 ∧ 1 ≤ s.backoffTime ∧ s.backoffTime ≤ 60000 ∧
  200 ≤ s.maxTimeout ∧ s.maxTimeout ≤ 300000 ∧ s.initialTimeout ≤ s.maxTimeout ∧ 1 ≤ s.duration ∧ s.duration ≤ 300000

/-- The defaults. -/
def SchedulerSettings.default : SchedulerSettings := ⟨100, 100, 10000, 500⟩

/-- The bound on the delay of attempt `k` (ESF:203): `min(maxTimeout, initialTimeout + k * backoffTime)`. -/
def maxDelay (s : SchedulerSettings) (k : Nat) : Nat := min s.maxTimeout (s.initialTimeout + k * s.backoffTime)

/-- `nonNegative(n)` (ESF:159-161), defined on every integer: `-2^63` (`Long.MIN_VALUE`) maps to 0, every other `n` to
`|n|`. On a Java `long`, `n ∈ [-2^63, 2^63)`, this is Java's value. -/
def nonNegative (n : Int) : Nat := if n = -2 ^ 63 then 0 else n.natAbs

/-- `toPositiveLongAtMost(randomNumber, upperBound)` (ESF:169-172): `nonNegative(randomNumber) % upperBound + 1`, with
the natural-number remainder (for `upperBound = 0`, which Java's assertion `0 < upperBound` excludes, this is
`nonNegative(randomNumber) + 1`). -/
def toPositiveLongAtMost (randomNumber : Int) (upperBound : Nat) : Nat := nonNegative randomNumber % upperBound + 1

/-- The delay before attempt `k` fires, given the random long drawn for it and the grace period (ESF:195-204). The grace
period is a parameter: Java passes 0 for the first attempt (`Coordinator.startElectionScheduler`, CO:1574) and
`duration` for every later one (ESF:218); `SchedulerSettings.duration` is read only by `Valid`. -/
def attemptDelay (s : SchedulerSettings) (k : Nat) (randomNumber : Int) (gracePeriod : Nat) : Nat :=
  toPositiveLongAtMost randomNumber (maxDelay s k) + gracePeriod

end OpenSearchPreVote


