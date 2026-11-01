-- Prove2me | Definitions.Def_OpenSearchCoordination
-- name    : OpenSearchCoordination
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-11-01T00:31:35.600849+00:00
-- url     : https://prove2.me/theorems/d5e98024-44b6-4309-bd29-08b0d83e1bc5
-- title:
--   OpenSearch CoordinationState: voting configurations, vote collections, the reduced cluster state, and the seven handlers of the per-node consensus state machine
-- statement:
--   A transcription of `org.opensearch.cluster.coordination.CoordinationState` at OpenSearch revision `b2a54ba5c0defba3d1d20423e911d4bf920bab19`, the per-node state machine of OpenSearch's cluster coordination ("Zen2"), with the parts of `VotingConfiguration`, `ElectionStrategy`, `ClusterState` and the message classes it reads. Line numbers below are those of `CoordinationState.java` unless stated.
--
--   **Nodes.** **`NodeId`** — a natural number (Java: the node id string). **`DiscoveryNode`** — a node id and whether the node has the cluster-manager (master-eligible) role, `isClusterManagerNode`. **`ZEN1_BWC_TERM`** — the term `0` (`Coordinator.java:134`): the term of the states a node holds before the first election, and of the states an Elasticsearch 6.x (Zen1) cluster-manager publishes during a rolling upgrade.
--
--   **Voting configurations.** **`VotingConfiguration`** — a list of node ids that is strictly increasing, so that two configurations are equal exactly when they have the same members (Java compares the sets of ids). **`EMPTY_CONFIG`** — the empty configuration; **`isEmpty`**. **`hasQuorum c votes`** — the number of members of `c` that occur in the list `votes`, doubled, exceeds the number of members of `c` (`CoordinationMetadata.java:405-409`); an empty configuration has no quorum.
--
--   **Vote collections.** **`VoteCollection`** — the list of ids of the nodes whose votes were added, most recent first; **`empty`**. **`addVote v n`** (755-757) — if `n` has the cluster-manager role and its id is not yet present, the collection with `n.id` added and `true`; otherwise `v` unchanged and `false`. **`isQuorum v c`** — `c.hasQuorum` of the ids; **`containsVoteFor v n`** — `n.id` is present; **`isEmpty`**.
--
--   **Cluster states.** **`ClusterState V`** — the fields `CoordinationState` reads or writes: `term` (natural number), `version` and `metadataVersion` (integers), `lastCommittedConfiguration`, `lastAcceptedConfiguration`, `clusterManagerNode` (the elected cluster-manager, identified by its ephemeral id, or `none` for Java `null`), `clusterUUIDKnown`, `clusterUUIDCommitted`, and an opaque payload `value : V` standing for everything else. **`versionOrMetadataVersion s`** — the metadata version when `s.term = 0`, otherwise the version (`ClusterState.java:239-244`). **`markCommitted s`** (703-740) — if the accepted configuration differs from the committed one, the committed configuration becomes the accepted one; then, if the cluster UUID is known and not committed, it is marked committed.
--
--   **Messages.** **`StartJoinRequest`** (source node, term); **`Join`** (source node, target node, term, the voter's last accepted term, and its last accepted version or metadata version); **`PublishRequest V`** (the accepted state); **`PublishResponse`** (term, version); **`ApplyCommitRequest`** (source node, term, version).
--
--   **Election strategies.** **`ElectionStrategy`** — a function `satisfiesAdditionalQuorumConstraints` of the local node, the current term, the last accepted term and version, the last committed and last accepted configurations and the vote collection, returning a Boolean (the plugin extension point; `isElectionQuorum` itself is final in Java). **`DEFAULT_INSTANCE`** — the constant `true`. **`Monotone es`** — for all arguments, if every id of `v` is an id of `w` and the constraint holds for `v`, it holds for `w`.
--
--   **The state.** **`CoordinationState V`** — the local node; the persisted current term (natural number) and last accepted cluster state; and the transient `joinVotes`, `startedJoinSinceLastReboot`, `electionWon`, `lastPublishedVersion` (integer), `lastPublishedConfiguration`, `publishVotes`. **`init n t s`** (84-106) — node `n` over the persisted term `t` and accepted state `s`: empty join and publish votes, `startedJoinSinceLastReboot = false`, `electionWon = false`, `lastPublishedVersion = 0`, `lastPublishedConfiguration` the accepted configuration of `s`. The accessors **`lastAcceptedTerm`**, **`lastAcceptedVersion`**, **`lastAcceptedVersionOrMetadataVersion`**, **`lastCommittedConfiguration`**, **`lastAcceptedConfiguration`** read the last accepted state. **`isElectionQuorum es cs votes`** (144-154) — `votes` is a quorum of the last committed configuration and of the last accepted configuration, and the strategy's constraint holds for the local node, current term, last accepted term and version, the two configurations and `votes`. **`isPublishQuorum cs votes`** (156-158) — a quorum of the last committed configuration and of `lastPublishedConfiguration`.
--
--   **The handlers**, each returning a rejection (`.error` with a message) or the new state, paired with its output for the five that have one (all but `setInitialState` and `handleCommit`), checking the Java conditions in the Java order:
--
--   - **`setInitialState cs s`** (180-204) — rejects if the last accepted configuration is nonempty; otherwise the last accepted state becomes `s`. **`initialStateContract cs s`** — the method's assertions (190-201): last accepted term 0, empty committed configuration, `lastPublishedVersion = 0`, empty `lastPublishedConfiguration`, election not won, empty join and publish votes, `s.term = 0`, `s.version` equal to the last accepted version, and both configurations of `s` nonempty.
--   - **`handleStartJoin cs req`** (213-255) — rejects if `req.term ≤ currentTerm`; otherwise sets the current term to `req.term`, `lastPublishedVersion` to 0, `lastPublishedConfiguration` to the last accepted configuration, `startedJoinSinceLastReboot` to true, `electionWon` to false, empties both vote collections, and returns the `Join` from the local node to `req.sourceNode` in term `req.term` with the last accepted term and version-or-metadata-version.
--   - **`handleJoin es cs j`** (264-339) — rejects, in order, if `j.term ≠ currentTerm`; if no start-join was handled since the last restart; if `j.lastAcceptedTerm > lastAcceptedTerm`; if the terms are equal and `j.lastAcceptedVersion > lastAcceptedVersionOrMetadataVersion`; if the last accepted configuration is empty. Otherwise adds the vote of `j.sourceNode`, sets `electionWon` to `isElectionQuorum es cs` of the new votes, sets `lastPublishedVersion` to the last accepted version if the election has just been won, and returns whether the vote was new.
--   - **`handleClientValue cs s`** (348-407) — rejects if the election is not won; if `lastPublishedVersion ≠ lastAcceptedVersion`; if `s.term ≠ currentTerm`; if `s.version ≤ lastPublishedVersion`; if `s` changes the accepted configuration while the committed configuration differs from the accepted one; if the join votes are not a quorum of `s`'s accepted configuration. Otherwise sets `lastPublishedVersion` to `s.version`, `lastPublishedConfiguration` to `s`'s accepted configuration, empties the publish votes and returns the `PublishRequest` of `s`. **`clientValueContract cs s`** — the assertion of 397-398: `s` has the node's last committed configuration.
--   - **`handlePublishRequest cs req`** (416-460) — for the incoming state `s`: rejects if `s.term ≠ currentTerm`; if `s.term` equals the last accepted term and `s.version ≤ lastAcceptedVersion`, rejects unless `s.term = 0`, `s` names a cluster-manager, and the last accepted state names none or a different one (the Zen1 compatibility branch; a term-0 state naming no cluster-manager is rejected there, Java's `NullPointerException`); otherwise the last accepted state becomes `s` and the response carries `s.term` and `s.version`.
--   - **`handlePublishResponse cs src r`** (471-515) — rejects if the election is not won; if `r.term ≠ currentTerm`; if `r.version ≠ lastPublishedVersion`. Otherwise adds the vote of `src` to the publish votes, and returns the `ApplyCommitRequest` (local node, `r.term`, `r.version`) if the new votes are a publish quorum, nothing otherwise.
--   - **`handleCommit cs c`** (523-573) — rejects if `c.term ≠ currentTerm`, if `c.term ≠ lastAcceptedTerm`, or if `c.version ≠ lastAcceptedVersion`; otherwise replaces the last accepted state by `markCommitted` of it.
--
--   **`javaInvariant es cs`** — the five assertions of `invariant()` (601-611): the last accepted term is at most the current term; `electionWon` equals `isElectionQuorum es cs joinVotes`; if the election is won, `lastPublishedVersion ≥ lastAcceptedVersion`, otherwise `lastPublishedVersion = 0`; a won election implies `startedJoinSinceLastReboot`; the publish votes are empty or the election is won.
--
--   **Formalization Note.** Node ids are naturals (only their equality is used); two `DiscoveryNode`s are equal when their ids and roles are, whereas Java compares ephemeral ids (no handler compares nodes), and `clusterManagerNode` holds an ephemeral id, a natural number unrelated to the node ids. The election strategy is an argument of `isElectionQuorum`, `handleJoin` and `javaInvariant` rather than a field of the state (Java: a `final` field); each theorem uses a single strategy. Terms are naturals (Java `long`s that are never negative: a fresh node's persisted term is 0, and among the handlers only `handleStartJoin` changes the current term, upwards); `init` takes the persisted term as a parameter, so a state may be in any term. Versions are integers (Java `long`; overflow is not modelled). A cluster state keeps only the fields above; the payload is a type parameter. Vote collections keep only voter ids: Java also records the `Join`s, which only tests read, and Java's `equals` (used only by tests) compares the map of voters and the recorded joins, whereas `=` here compares the lists of ids, including their order (the order in which votes were added) and multiplicity; no handler compares vote collections. The remote cluster-state store (the REMOTE persisted state) is omitted: the handlers read it only to decide whether to write it (616-642; the write in `handlePublishResponse`, `handlePreCommit` at 510 and 593-599, is gated by the `isRemoteStateEnabled` setting), every value they compute comes from the LOCAL persisted state, and a failed remote write makes the Java method throw after its local effects, where the transcription returns the result: the Java run is then the transcription's run with that output lost, which a cluster model whose messages may be lost includes. Java `assert`s are disabled in production; the handlers do not check them, and the asserted preconditions of `setInitialState` and `handleClientValue` are stated separately as `initialStateContract` and `clientValueContract`, which no other definition and no theorem of this mission uses. Not represented: the assertion that a join targets the local node (265), the assertion of `markLastAcceptedStateAsCommitted` that a state with an unknown cluster UUID is committed only in term 0 (708-710), and the assertions of the `Join` and `PublishResponse` constructors that their versions are non-negative (versions here are unbounded integers; terms are naturals). Rejection messages are fixed strings containing the substrings OpenSearch's tests match. The file has no imports (Lean core only).
-- source:
--   OpenSearch b2a54ba5c0defba3d1d20423e911d4bf920bab19: CoordinationState (constructor lines 84-106, isElectionQuorum 144-154, isPublishQuorum 156-158, setInitialState 180-204, handleStartJoin 213-255, handleJoin 264-339, handleClientValue 348-407, handlePublishRequest 416-460, handlePublishResponse 471-515, handleCommit 523-573, invariant 601-611, PersistedState.markLastAcceptedStateAsCommitted 703-728, commitVotingConfiguration 730-740, VoteCollection 750-814), server/src/main/java/org/opensearch/cluster/coordination/CoordinationState.java: https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/CoordinationState.java#L64-L815; CoordinationMetadata.VotingConfiguration (lines 383-449, hasQuorum 405-409): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/CoordinationMetadata.java#L383-L449; ElectionStrategy (DEFAULT_INSTANCE lines 46-59, isElectionQuorum 68-88): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ElectionStrategy.java#L44-L110; ClusterState.getVersionOrMetadataVersion (lines 239-244): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/ClusterState.java#L239-L244; Coordinator.ZEN1_BWC_TERM (line 134): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/Coordinator.java#L134; the messages StartJoinRequest.java, Join.java, PublishRequest.java, PublishResponse.java, ApplyCommitRequest.java in the same directory; test vectors from server/src/test/java/org/opensearch/cluster/coordination/CoordinationStateTests.java (https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/test/java/org/opensearch/cluster/coordination/CoordinationStateTests.java) and CoordinationMetadataTests.java (testVotingConfiguration)

/-!
# OpenSearch cluster coordination: `CoordinationState`

Transcription of the per-node consensus state machine of OpenSearch's cluster coordination ("Zen2"),
`org.opensearch.cluster.coordination.CoordinationState`, at OpenSearch revision
`b2a54ba5c0defba3d1d20423e911d4bf920bab19`
(`server/src/main/java/org/opensearch/cluster/coordination/CoordinationState.java`, cited below as `CS:<line>`),
with the parts of `CoordinationMetadata.VotingConfiguration` (`CM:<line>`), `ElectionStrategy` (`ES:<line>`),
`ClusterState` (`CLS:<line>`) and the message classes that it reads.

Abstractions:
* Node ids are `Nat` (Java: `String`); only equality is used.
* Terms are `Nat` (Java `long`s that are never negative: a fresh node's persisted term is `0`, and among the handlers
  only `handleStartJoin` changes it, to a strictly larger value); `init` takes the persisted term as a parameter.
* Versions are `Int` (Java `long`).
* A `ClusterState` is reduced to the fields that `CoordinationState` reads or writes; everything else is an opaque
  payload `value : V`.
* `VotingConfiguration` stores its node ids strictly sorted, so that `=` is Java's `Set.equals`.
* The REMOTE persisted state (remote cluster-state store) is omitted. The handlers read it only to decide whether to
  write it (CS:616-642; the write in `handlePublishResponse`, `handlePreCommit` at CS:510 and CS:593-599, is gated by
  the `isRemoteStateEnabled` setting), and every value they compute is read from the LOCAL persisted state. A failed
  remote write makes the Java method throw after its local effects (for example after `publishVotes.addVote` in
  `handlePublishResponse`, CS:503-510); the transcription returns the result instead, so the Java run is the
  transcription's run with that output lost, which a cluster model whose messages may be lost includes.
* Java `assert`s are not checked in production; they are caller contracts. The handlers below do not check them. The
  asserted preconditions of `setInitialState` and `handleClientValue` are the predicates `initialStateContract` and
  `clientValueContract`, which nothing in this file uses (the cluster model of the `OpenSearchSafety` mission imposes
  them at its `bootstrap` and `clientValue` steps, and delivers a join only to its target). The asserted
  postconditions (CS:240, CS:323-324, CS:457, CS:572) and the assertions of `invariant()` (`javaInvariant` below) are
  the subject of the mission's theorems. Not represented: `join.targetMatches(localNode)` (CS:265), the assertion of
  `markLastAcceptedStateAsCommitted` that a state with an unknown cluster UUID is committed only in term 0
  (CS:708-710), and the assertions of the `Join` and `PublishResponse` constructors that their versions are
  non-negative (Join.java:62, PublishResponse.java:53; their terms are `Nat`).
-/

namespace OpenSearchCoordination

/-- A node id (`DiscoveryNode.getId()`). -/
abbrev NodeId := Nat

/-- `DiscoveryNode`, as far as coordination reads it: the node id and whether the node has the cluster-manager
(master-eligible) role (`DiscoveryNode.isClusterManagerNode()`). The derived equality compares the id and the role;
Java's `equals` compares ephemeral ids. No handler compares nodes. -/
structure DiscoveryNode where
  id : NodeId
  isClusterManagerNode : Bool
  deriving DecidableEq, Repr

/-- `Coordinator.ZEN1_BWC_TERM` (Coordinator.java:134). -/
def ZEN1_BWC_TERM : Nat := 0

/-! ## Voting configurations and vote collections -/

/-- `CoordinationMetadata.VotingConfiguration` (CM:383-449): a set of node ids. Stored strictly sorted, so that
structural equality is set equality (Java `equals` compares the `Set<String> nodeIds`). -/
structure VotingConfiguration where
  nodeIds : List NodeId
  sorted : nodeIds.Pairwise (· < ·)

instance : DecidableEq VotingConfiguration := fun a b =>
  if h : a.nodeIds = b.nodeIds then isTrue (by cases a; cases b; simp at h; subst h; rfl)
  else isFalse (by intro e; exact h (e ▸ rfl))

namespace VotingConfiguration

/-- `VotingConfiguration.EMPTY_CONFIG` (CM:385). -/
def EMPTY_CONFIG : VotingConfiguration := ⟨[], List.Pairwise.nil⟩

/-- `isEmpty()` (CM:433-435). -/
def isEmpty (c : VotingConfiguration) : Bool := c.nodeIds.isEmpty

/-- `hasQuorum(votes)` (CM:405-409): `intersection.size() * 2 > nodeIds.size()` where `intersection` is
`nodeIds ∩ votes`. -/
def hasQuorum (c : VotingConfiguration) (votes : List NodeId) : Bool :=
  decide ((c.nodeIds.filter (fun x => votes.contains x)).length * 2 > c.nodeIds.length)

end VotingConfiguration

/-- `CoordinationState.VoteCollection` (CS:750-814): the ids of the nodes whose votes were added, most recent first.
(Java keys a `Map<String, DiscoveryNode>` by node id and also records the `Join`s in a set that only tests read. Java's
`equals`, used only by tests, compares that map and the set of joins, CS:798-806, whereas the derived `=` here compares
the lists, including the order and any repetitions of the ids; no handler compares vote collections, and the handlers
read them only through membership.) -/
structure VoteCollection where
  nodes : List NodeId
  deriving DecidableEq, Repr

namespace VoteCollection

/-- `new VoteCollection()`. -/
def empty : VoteCollection := ⟨[]⟩

/-- `addVote(sourceNode)` (CS:755-757): `sourceNode.isClusterManagerNode() && nodes.put(id, sourceNode) == null`. The
new collection and whether the vote was added. -/
def addVote (v : VoteCollection) (n : DiscoveryNode) : VoteCollection × Bool :=
  if n.isClusterManagerNode && !(v.nodes.contains n.id) then (⟨n.id :: v.nodes⟩, true) else (v, false)

/-- `isQuorum(configuration)` (CS:772-774). -/
def isQuorum (v : VoteCollection) (c : VotingConfiguration) : Bool := c.hasQuorum v.nodes

/-- `containsVoteFor(node)` (CS:776-778). -/
def containsVoteFor (v : VoteCollection) (n : DiscoveryNode) : Bool := v.nodes.contains n.id

/-- `isEmpty()` (CS:780-782). -/
def isEmpty (v : VoteCollection) : Bool := v.nodes.isEmpty

end VoteCollection

/-! ## Cluster states, persisted state, messages -/

/-- A cluster state, reduced to what `CoordinationState` reads or writes. -/
structure ClusterState (V : Type) where
  /-- `term()` (= `coordinationMetadata().term()`). -/
  term : Nat
  /-- `version()`. -/
  version : Int
  /-- `metadata().version()`. -/
  metadataVersion : Int
  /-- `getLastCommittedConfiguration()`. -/
  lastCommittedConfiguration : VotingConfiguration
  /-- `getLastAcceptedConfiguration()`. -/
  lastAcceptedConfiguration : VotingConfiguration
  /-- `nodes().getClusterManagerNode()`, identified by its ephemeral id (`DiscoveryNode.equals` compares ephemeral
  ids), a number unrelated to the `NodeId`s; `none` is Java `null`. Read only by the Zen1 compatibility branch of
  `handlePublishRequest`. -/
  clusterManagerNode : Option Nat
  /-- `metadata().clusterUUID()` differs from `Metadata.UNKNOWN_CLUSTER_UUID`. -/
  clusterUUIDKnown : Bool
  /-- `metadata().clusterUUIDCommitted()`. -/
  clusterUUIDCommitted : Bool
  /-- Everything else. -/
  value : V

namespace ClusterState

variable {V : Type}

/-- `getVersionOrMetadataVersion()` (CLS:239-244). -/
def versionOrMetadataVersion (s : ClusterState V) : Int :=
  if s.term = ZEN1_BWC_TERM then s.metadataVersion else s.version

/-- `PersistedState.markLastAcceptedStateAsCommitted()` (CS:703-728) with `commitVotingConfiguration` (CS:730-740):
the committed configuration becomes the accepted one, and a known cluster UUID is marked committed. -/
def markCommitted (s : ClusterState V) : ClusterState V :=
  let s₁ := if s.lastAcceptedConfiguration ≠ s.lastCommittedConfiguration then
      { s with lastCommittedConfiguration := s.lastAcceptedConfiguration } else s
  if s₁.clusterUUIDKnown && !s₁.clusterUUIDCommitted then { s₁ with clusterUUIDCommitted := true } else s₁

end ClusterState

/-- `StartJoinRequest` (StartJoinRequest.java). -/
structure StartJoinRequest where
  sourceNode : DiscoveryNode
  term : Nat
  deriving DecidableEq, Repr

/-- `Join` (Join.java): a vote from `sourceNode` for `targetNode` in `term`, with the voter's last accepted term and
version (or metadata version, for term-0 states). -/
structure Join where
  sourceNode : DiscoveryNode
  targetNode : DiscoveryNode
  term : Nat
  lastAcceptedTerm : Nat
  lastAcceptedVersion : Int
  deriving DecidableEq, Repr

/-- `PublishRequest` (PublishRequest.java). -/
structure PublishRequest (V : Type) where
  acceptedState : ClusterState V

/-- `PublishResponse` (PublishResponse.java). -/
structure PublishResponse where
  term : Nat
  version : Int
  deriving DecidableEq, Repr

/-- `ApplyCommitRequest` (ApplyCommitRequest.java). -/
structure ApplyCommitRequest where
  sourceNode : DiscoveryNode
  term : Nat
  version : Int
  deriving DecidableEq, Repr

/-- `ElectionStrategy` (ES): `isElectionQuorum` is final; plugins override only
`satisfiesAdditionalQuorumConstraints(localNode, currentTerm, acceptedTerm, acceptedVersion, lastCommitted,
lastAccepted, joinVotes)`. A Java strategy also sees the voters' `DiscoveryNode`s and the recorded joins; here it sees
the voters' ids. `DEFAULT_INSTANCE`, the only strategy in OpenSearch itself, uses none of them. Java's
`CoordinationState` keeps its strategy in a `final` field; here the strategy is an argument of `isElectionQuorum`,
`handleJoin` and `javaInvariant`. -/
structure ElectionStrategy where
  satisfiesAdditionalQuorumConstraints :
    DiscoveryNode → Nat → Nat → Int → VotingConfiguration → VotingConfiguration → VoteCollection → Bool

/-- `ElectionStrategy.DEFAULT_INSTANCE`: no additional constraint. -/
def ElectionStrategy.DEFAULT_INSTANCE : ElectionStrategy := ⟨fun _ _ _ _ _ _ _ => true⟩

/-- An election strategy whose additional constraint is monotone in the votes (adding votes never turns a satisfied
constraint into an unsatisfied one). The default strategy is. -/
def ElectionStrategy.Monotone (es : ElectionStrategy) : Prop :=
  ∀ n t at' av c a (v w : VoteCollection), (∀ x, x ∈ v.nodes → x ∈ w.nodes) →
    es.satisfiesAdditionalQuorumConstraints n t at' av c a v = true →
    es.satisfiesAdditionalQuorumConstraints n t at' av c a w = true

/-! ## The state machine -/

/-- The fields of `CoordinationState` (CS:64-106): the LOCAL persisted state (current term, last accepted cluster
state) and the transient state that a restart discards. -/
structure CoordinationState (V : Type) where
  localNode : DiscoveryNode
  /-- persisted: `getCurrentTerm()` -/
  currentTerm : Nat
  /-- persisted: `getLastAcceptedState()` -/
  lastAcceptedState : ClusterState V
  joinVotes : VoteCollection
  startedJoinSinceLastReboot : Bool
  electionWon : Bool
  lastPublishedVersion : Int
  lastPublishedConfiguration : VotingConfiguration
  publishVotes : VoteCollection

namespace CoordinationState

variable {V : Type}

/-- The constructor (CS:84-106): a fresh `CoordinationState` over a persisted state. A restart. -/
def init (localNode : DiscoveryNode) (currentTerm : Nat) (lastAcceptedState : ClusterState V) :
    CoordinationState V where
  localNode := localNode
  currentTerm := currentTerm
  lastAcceptedState := lastAcceptedState
  joinVotes := VoteCollection.empty
  startedJoinSinceLastReboot := false
  electionWon := false
  lastPublishedVersion := 0
  lastPublishedConfiguration := lastAcceptedState.lastAcceptedConfiguration
  publishVotes := VoteCollection.empty

def lastAcceptedTerm (cs : CoordinationState V) : Nat := cs.lastAcceptedState.term
def lastAcceptedVersion (cs : CoordinationState V) : Int := cs.lastAcceptedState.version
def lastAcceptedVersionOrMetadataVersion (cs : CoordinationState V) : Int :=
  cs.lastAcceptedState.versionOrMetadataVersion
def lastCommittedConfiguration (cs : CoordinationState V) : VotingConfiguration :=
  cs.lastAcceptedState.lastCommittedConfiguration
def lastAcceptedConfiguration (cs : CoordinationState V) : VotingConfiguration :=
  cs.lastAcceptedState.lastAcceptedConfiguration

/-- `isElectionQuorum(joinVotes)` (CS:144-154, ES:68-88). -/
def isElectionQuorum (es : ElectionStrategy) (cs : CoordinationState V) (votes : VoteCollection) : Bool :=
  votes.isQuorum cs.lastCommittedConfiguration && votes.isQuorum cs.lastAcceptedConfiguration &&
    es.satisfiesAdditionalQuorumConstraints cs.localNode cs.currentTerm cs.lastAcceptedTerm cs.lastAcceptedVersion
      cs.lastCommittedConfiguration cs.lastAcceptedConfiguration votes

/-- `isPublishQuorum(votes)` (CS:156-158). -/
def isPublishQuorum (cs : CoordinationState V) (votes : VoteCollection) : Bool :=
  votes.isQuorum cs.lastCommittedConfiguration && votes.isQuorum cs.lastPublishedConfiguration

/-- `setInitialState(initialState)` (CS:180-204). The asserted preconditions are `initialStateContract`. -/
def setInitialState (cs : CoordinationState V) (initialState : ClusterState V) :
    Except String (CoordinationState V) :=
  if !cs.lastAcceptedConfiguration.isEmpty then
    .error "initial state already set: last-accepted configuration now nonempty"
  else
    .ok { cs with lastAcceptedState := initialState }

/-- The assertions of `setInitialState` (CS:190-201): the caller's contract. -/
def initialStateContract (cs : CoordinationState V) (initialState : ClusterState V) : Prop :=
  cs.lastAcceptedTerm = 0 ∧ cs.lastCommittedConfiguration.isEmpty ∧ cs.lastPublishedVersion = 0 ∧
  cs.lastPublishedConfiguration.isEmpty ∧ cs.electionWon = false ∧ cs.joinVotes.isEmpty ∧
  cs.publishVotes.isEmpty ∧ initialState.term = 0 ∧ initialState.version = cs.lastAcceptedVersion ∧
  initialState.lastAcceptedConfiguration.isEmpty = false ∧ initialState.lastCommittedConfiguration.isEmpty = false

/-- `handleStartJoin(startJoinRequest)` (CS:213-255). -/
def handleStartJoin (cs : CoordinationState V) (req : StartJoinRequest) :
    Except String (CoordinationState V × Join) :=
  if req.term ≤ cs.currentTerm then
    .error "incoming term not greater than current term"
  else
    let cs' : CoordinationState V :=
      { cs with
        currentTerm := req.term
        lastPublishedVersion := 0
        lastPublishedConfiguration := cs.lastAcceptedConfiguration
        startedJoinSinceLastReboot := true
        electionWon := false
        joinVotes := VoteCollection.empty
        publishVotes := VoteCollection.empty }
    .ok (cs', ⟨cs.localNode, req.sourceNode, req.term, cs.lastAcceptedTerm, cs.lastAcceptedVersionOrMetadataVersion⟩)

/-- `handleJoin(join)` (CS:264-339). Returns whether the vote was new. (Asserted: `join.targetNode` is this node.) -/
def handleJoin (es : ElectionStrategy) (cs : CoordinationState V) (join : Join) :
    Except String (CoordinationState V × Bool) :=
  if join.term ≠ cs.currentTerm then
    .error "incoming term does not match current term"
  else if !cs.startedJoinSinceLastReboot then
    .error "ignored join as term has not been incremented yet after reboot"
  else if join.lastAcceptedTerm > cs.lastAcceptedTerm then
    .error "incoming last accepted term of join higher than current last accepted term"
  else if join.lastAcceptedTerm = cs.lastAcceptedTerm ∧
      join.lastAcceptedVersion > cs.lastAcceptedVersionOrMetadataVersion then
    .error "incoming last accepted version of join higher than current last accepted version"
  else if cs.lastAcceptedConfiguration.isEmpty then
    .error "rejecting join since this node has not received its initial configuration yet"
  else
    let (votes, added) := cs.joinVotes.addVote join.sourceNode
    let won := isElectionQuorum es cs votes
    let cs₁ : CoordinationState V := { cs with joinVotes := votes, electionWon := won }
    let cs₂ := if won && !cs.electionWon then { cs₁ with lastPublishedVersion := cs.lastAcceptedVersion } else cs₁
    .ok (cs₂, added)

/-- `handleClientValue(clusterState)` (CS:348-407). The assertion of CS:397-398 is `clientValueContract`. -/
def handleClientValue (cs : CoordinationState V) (clusterState : ClusterState V) :
    Except String (CoordinationState V × PublishRequest V) :=
  if !cs.electionWon then
    .error "election not won"
  else if cs.lastPublishedVersion ≠ cs.lastAcceptedVersion then
    .error "cannot start publishing next value before accepting previous one"
  else if clusterState.term ≠ cs.currentTerm then
    .error "incoming term does not match current term"
  else if clusterState.version ≤ cs.lastPublishedVersion then
    .error "incoming cluster state version lower or equal to last published version"
  else if clusterState.lastAcceptedConfiguration ≠ cs.lastAcceptedConfiguration ∧
      cs.lastCommittedConfiguration ≠ cs.lastAcceptedConfiguration then
    .error "only allow reconfiguration while not already reconfiguring"
  else if !cs.joinVotes.isQuorum clusterState.lastAcceptedConfiguration then
    .error "only allow reconfiguration if joinVotes have quorum for new config"
  else
    .ok ({ cs with
            lastPublishedVersion := clusterState.version
            lastPublishedConfiguration := clusterState.lastAcceptedConfiguration
            publishVotes := VoteCollection.empty },
         ⟨clusterState⟩)

/-- The assertion of `handleClientValue` (CS:397-398): the last committed configuration does not change. -/
def clientValueContract (cs : CoordinationState V) (clusterState : ClusterState V) : Prop :=
  clusterState.lastCommittedConfiguration = cs.lastCommittedConfiguration

/-- `handlePublishRequest(publishRequest)` (CS:416-460). In the Zen1 compatibility branch, Java's
`getClusterManagerNode().equals(...)` on a `null` incoming cluster-manager throws (a rejection). -/
def handlePublishRequest (cs : CoordinationState V) (req : PublishRequest V) :
    Except String (CoordinationState V × PublishResponse) :=
  let s := req.acceptedState
  let accept : Except String (CoordinationState V × PublishResponse) :=
    .ok ({ cs with lastAcceptedState := s }, ⟨s.term, s.version⟩)
  if s.term ≠ cs.currentTerm then
    .error "incoming term does not match current term"
  else if s.term = cs.lastAcceptedTerm ∧ s.version ≤ cs.lastAcceptedVersion then
    if s.term = ZEN1_BWC_TERM then
      match s.clusterManagerNode with
      | none => .error "NullPointerException"
      | some m =>
        if some m ≠ cs.lastAcceptedState.clusterManagerNode then accept
        else .error "incoming version lower or equal to current version"
    else
      .error "incoming version lower or equal to current version"
  else
    accept

/-- `handlePublishResponse(sourceNode, publishResponse)` (CS:471-515). The optional `ApplyCommitRequest`. -/
def handlePublishResponse (cs : CoordinationState V) (sourceNode : DiscoveryNode) (resp : PublishResponse) :
    Except String (CoordinationState V × Option ApplyCommitRequest) :=
  if !cs.electionWon then
    .error "election not won"
  else if resp.term ≠ cs.currentTerm then
    .error "incoming term does not match current term"
  else if resp.version ≠ cs.lastPublishedVersion then
    .error "incoming version does not match current version"
  else
    let votes := (cs.publishVotes.addVote sourceNode).1
    let cs' : CoordinationState V := { cs with publishVotes := votes }
    if isPublishQuorum cs' votes then
      .ok (cs', some ⟨cs.localNode, resp.term, resp.version⟩)
    else
      .ok (cs', none)

/-- `handleCommit(applyCommit)` (CS:523-573). -/
def handleCommit (cs : CoordinationState V) (c : ApplyCommitRequest) : Except String (CoordinationState V) :=
  if c.term ≠ cs.currentTerm then
    .error "incoming term does not match current term"
  else if c.term ≠ cs.lastAcceptedTerm then
    .error "incoming term does not match last accepted term"
  else if c.version ≠ cs.lastAcceptedVersion then
    .error "incoming version does not match current version"
  else
    .ok { cs with lastAcceptedState := cs.lastAcceptedState.markCommitted }

/-- `invariant()` (CS:601-611), the assertions Java checks in tests. -/
def javaInvariant (es : ElectionStrategy) (cs : CoordinationState V) : Prop :=
  cs.lastAcceptedTerm ≤ cs.currentTerm ∧
  cs.electionWon = isElectionQuorum es cs cs.joinVotes ∧
  (if cs.electionWon then cs.lastPublishedVersion ≥ cs.lastAcceptedVersion else cs.lastPublishedVersion = 0) ∧
  (cs.electionWon = true → cs.startedJoinSinceLastReboot = true) ∧
  (cs.publishVotes.isEmpty = true ∨ cs.electionWon = true)

end CoordinationState

end OpenSearchCoordination


