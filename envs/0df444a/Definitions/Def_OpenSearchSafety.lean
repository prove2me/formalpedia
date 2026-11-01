-- Prove2me | Definitions.Def_OpenSearchSafety
-- name    : OpenSearchSafety
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-11-01T00:41:30.733661+00:00
-- url     : https://prove2.me/theorems/52e8274a-fb57-4625-bec4-e1651ab40dd0
-- title:
--   OpenSearch coordination as a message-passing system: every node runs CoordinationState, messages may be lost, duplicated or reordered, nodes restart; the safety vocabulary and the inductive invariant
-- statement:
--   A model of an OpenSearch cluster at revision `b2a54ba5c0defba3d1d20423e911d4bf920bab19` in which every node runs the `CoordinationState` of the `OpenSearchCoordination` mission (its `NodeId`, `DiscoveryNode`, `VotingConfiguration`, `ClusterState`, message types, `ElectionStrategy`, `CoordinationState`, handlers and contracts are used as they are), the notions in which the safety theorems are stated, and the inductive invariant `Inv` from which they are proved. `CO` is `Coordinator.java`, `CBS` is `ClusterBootstrapService.java`.
--
--   **Messages.** **`Message V`** — `join j`, a `Join`; `publishRequest source state parentTerm parentVersion`, a `PublishRequest` of `state` from `source`, together with ghost data that the real message does not carry: the term and version of the state the publisher had accepted when it published, the publication's *parent*; `publishResponse source dest resp`, a `PublishResponse` from `source` to `dest`; `applyCommit c`, an `ApplyCommitRequest`.
--
--   **Parameters.** **`Params`** — `eligible n`, whether node `n` has the cluster-manager role (`DiscoveryNode.isClusterManagerNode()`, fixed); `initConfs`, the configurations a node may bootstrap with (a predicate on configurations); `strategy`, the election strategy of every node. **`P.dn n`** — the `DiscoveryNode` `⟨n, P.eligible n⟩`. **`P.InitCompatible`** — for all configurations `X`, `Y` with `P.initConfs X` and `P.initConfs Y` and all lists `q₁`, `q₂` of eligible node ids with `X.hasQuorum q₁` and `Y.hasQuorum q₂`, some node id is in both lists. **`BootstrapConfig k resolve placeholder matched X`** — `X` has the form of a configuration that `ClusterBootstrapService` bootstraps with (CBS:176-215, 259-273, 306-335): the `k` bootstrap requirements (`cluster.initial_cluster_manager_nodes`) are numbered `0 … k-1`; the members of `X` are exactly, for `i < k`, `resolve i` if `matched i` (the node has discovered the node requirement `i` names) and the placeholder id `placeholder i` otherwise (`"{bootstrap-placeholder}-" + requirement`); and more than half of the `k` requirements are matched. The predicate does not require `resolve` or `placeholder` to be injective or their values to be distinct (`bootstrap_compatible` assumes this; in Java the requirements have no duplicates and `checkRequirements` matches each requirement and each discovered node at most once, CBS:150-155, 306-335), nor the bootstrapping node to be eligible and matched (Java requires both, CBS:179, 202-209); no other definition refers to it (the `bootstrap` step uses `P.initConfs`).
--
--   **Clusters.** **`Cluster V`** — `node : NodeId → CoordinationState V`, the state of every node, and `sent : Message V → Prop`, the messages sent so far. **`W.set n cs`** replaces node `n`'s state by `cs`; **`W.send m`** adds `m` to the sent messages. **`Initial P W`** — every node `n` is `CoordinationState.init (P.dn n) 0 s` for some cluster state `s` of term 0 whose last committed and last accepted configurations are empty (its other fields, version and metadata version included, are arbitrary), and no message has been sent. **`RestartState s s'`** — the accepted state `s'` a restarting cluster-manager-eligible node comes back with, given the accepted state `s` it had: `s'` has the term, the version, the two configurations and the two cluster-UUID flags of `s` (its metadata version, cluster-manager node and payload may differ: Java rebuilds the cluster-manager node and the parts of the state outside the persisted metadata, and leaving the persisted metadata, metadata version included, free only adds behaviours); or `s` has term 0, empty configurations and an unknown cluster UUID, and `s'` has term 0 and empty configurations (a node that never joined a cluster, restoring a state from the remote store).
--
--   **Steps.** **`Step P W W'`** — one successful handler call at a node `n`, its output, if any, being added to the sent messages:
--   - `bootstrap`: `(W.node n).setInitialState s = .ok cs'` for a state `s` whose two configurations are some `X` with `P.initConfs X`, with `initialStateContract` (the method's asserted preconditions); `W' = W.set n cs'`;
--   - `startJoin`: `handleStartJoin ⟨P.dn src, t⟩ = .ok (cs', j)` for any eligible `src` and any term `t`; `W' = (W.set n cs').send (.join j)`;
--   - `join`: `handleJoin P.strategy j = .ok (cs', b)` for a sent join `j` with `j.targetNode.id = n`; `W' = W.set n cs'`;
--   - `clientValue`: `handleClientValue s = .ok (cs', p)` with `clientValueContract` (the asserted precondition: `s` carries `n`'s last committed configuration); sends `publishRequest n p.acceptedState lt lv`, where `(lt, lv)` are `n`'s last accepted term and version before the call;
--   - `publish`: `handlePublishRequest ⟨s⟩ = .ok (cs', r)` for a sent `publishRequest src s pt pv`; sends `publishResponse n src r`;
--   - `respond`: `handlePublishResponse (P.dn src) r = .ok (cs', o)` for a sent `publishResponse src n r`; sends `applyCommit c` if `o = some c`;
--   - `commit`: `handleCommit c = .ok cs'` for a sent `applyCommit c`;
--   - `restart`: for an eligible `n`, the state becomes `CoordinationState.init (W.node n).localNode (W.node n).currentTerm s'` for a state `s'` with `RestartState (W.node n).lastAcceptedState s'`;
--   - `restartAny`: for a node `n` that is not eligible, the state becomes `CoordinationState.init (W.node n).localNode t s'` for any term `t` and any state `s'`.
--
--   **`Reachable P W`** — `W` is initial, or is reached from a reachable cluster by a step.
--
--   **Safety vocabulary.** A publication is named by its *key*, its (term, version). **`Committed W t v`** — some `applyCommit ⟨src, t, v⟩` has been sent. **`Parent W t v t' v'`** — some `publishRequest src s t v` with `s.term = t'` and `s.version = v'` has been sent. **`Descends W t v t' v'`** — the reflexive-transitive closure of `Parent`: `(t', v')` descends from `(t, v)`.
--
--   **Proof-side notions** (used by `Inv`, the lemmas and their proofs only; `Published` appears only in the proofs). **`KeyLE t v t' v'`** — `t < t' ∨ (t = t' ∧ v ≤ v')`. **`Below lt lv bt bv`** — `lt < bt ∨ (lt = bt ∧ (bt = 0 ∨ lv ≤ bv))`: `handleJoin`'s freshness comparison, ignoring the version at term 0, where joins carry metadata versions. **`Published W t v`** — some publication of term `t` and version `v` has been sent. **`Realizes P W t v x y`** — the pair (last committed, last accepted) `(x, y)` realizes the key `(t, v)`: `t = 0`, `x = y` and `P.initConfs x` (a bootstrap state); or some sent publication of term `t` and version `v` has last accepted configuration `y`, and last committed configuration `x`, or last accepted configuration `x` with `(t, v)` committed. **`JoinVoters P W L t J`** — every member of `J` is eligible and sent node `L` a join of term `t`. **`BaseVoters P W L t bt bv J`** — every member of `J` is eligible and sent `L` a join of term `t` whose last accepted term and version are `Below bt bv`. **`RespVoters P W t v A`** — every member of `A` is eligible and sent a `PublishResponse` for `(t, v)` to some node. **`ElectionRecord P W L t bt bv x y J`** — `bt < t`, `Realizes P W bt bv x y`, `BaseVoters P W L t bt bv J`, `x.hasQuorum J` and `y.hasQuorum J`: an election of `L` in term `t` over the base `(bt, bv)`. **`Won P W b t`** — `b` is eligible, and either `(W.node b).electionWon = true` with current term `t`, or `b` has sent a publication of term `t`.
--
--   **`Inv P W`** — the inductive invariant, 30 facts (field names in parentheses).
--   - Every node `n`: its local node is `P.dn n` (`localNode_eq`); if it has not won, its last published version is 0 and its publish votes are empty (`idle_of_not_won`); if it has won, and if it holds join votes, it has handled a start-join since its last restart (`won_started`, `votes_started`); if it has handled one, its current term is at least 1 (`started_term_pos`); its join votes are a quorum of both its last committed and its last accepted configuration if it has won (`won_quorum`) and not if it has not (`not_won_no_quorum`); every join vote it holds is of an eligible node that sent it a join for its current term with a last accepted term and version `Below` its own (`joinVotes_sent`); every publish vote it holds is of an eligible node that sent it a `PublishResponse` for its current term and last published version (`publishVotes_sent`).
--   - Every eligible node: its last accepted term is at most its current term (`term_le`); its accepted state has term 0 and empty configurations, or its two configurations realize its last accepted term and version (`accepted_realizes`).
--   - Joins and responses: every join is from the `DiscoveryNode` of its source and addressed to an eligible node (`join_wf`); the joins of an eligible node have terms at most its current term (`join_term_le`), at most one per term (`join_unique`), and a join of an eligible node for a term later than one of its publish responses carries a last accepted (term, version) at least the response's (`join_after_response`); the publish responses of an eligible node have terms at most its current term and keys at most its last accepted key (`response_le`); every publish response answers a publication of its key sent by the node it is addressed to (`response_published`).
--   - Publications: every publication is sent by an eligible node, has term ≥ 1, a parent of term at most its term and of smaller version, and, if the parent has term 0, a bootstrap configuration as last committed configuration (`pub_wf`); a parent of term ≥ 1 is the key of a sent publication, the last committed configuration is that publication's last committed one, or its last accepted one if the parent is committed, and the last accepted configuration differs from that publication's only if the last committed configuration is that publication's last accepted one (`pub_parent`); two publications with the same key are the same message (`pub_unique`); every publication descends from a key of term 0 (`pub_rooted`); two publications of the same term are related by descent (`pub_same_term`); the eligible nodes that sent the publisher a join for the publication's term include a quorum of both its configurations (`pub_voters`); a publication whose parent is of an older term carries an election record of its publisher for its term, over the parent, with its last committed configuration as `x` (`pub_election`).
--   - Commits: every commit is of a sent publication whose publish responses from eligible nodes include a quorum `A` of its last accepted configuration such that `A` is also a quorum of its last committed configuration, or the publication's parent is committed and is a sent publication with the same last accepted configuration (`commit_quorum`).
--   - Leaders: for each term `t`, at most one node `b` has `Won P W b t` (`won_unique`); a node that published in a term is past that term, or still in it and either elected or without a start-join handled since its last restart (`pub_source_term`); every publication of an elected node's current term has a version at most the node's last published version, descends to (current term, last published version), and has both configurations with a quorum in the node's join votes (`leader_pubs`); an elected node whose last published version differs from its last accepted version sent a publication of key (current term, last published version) with its accepted key as parent, its last published configuration is that publication's last accepted configuration, and its last committed configuration is that publication's last committed one, or that publication's last accepted one with its accepted key committed and its last accepted configuration equal to that publication's (`leader_inflight`); an elected node whose last published version equals its last accepted version has its last accepted term equal to its current term and its last published configuration equal to its last accepted one, or an older last accepted term while no publication of its current term has been sent (`leader_settled`).
--
--   **Formalization Note.** Messages are never removed: a step may handle any sent message any number of times, in any order, or never, which models loss, duplication, delay and reordering. A join is handled only by its target and a publish response only by its addressee; publish requests and commits may be handled by any node. Start-join requests are not messages: any node may handle a request from any eligible node for any term at any time, which covers the `Coordinator`'s elections, abdication and `ensureTermAtLeast` (CO:583-657) and over-approximates them; the `Coordinator`'s other guards only reject more calls. The asserted preconditions of `setInitialState` and `handleClientValue` are imposed at the `bootstrap` and `clientValue` steps. The ghost parent of a publication is not read by any handler. A cluster-manager-eligible node persists its current term and accepted state synchronously; a restart keeps its current term and either keeps its accepted state except for the metadata version, the cluster-manager node and the payload, which it leaves free, or, if the node never joined a cluster (term 0, empty configurations, unknown cluster UUID), replaces it by a term-0 state with empty configurations, as restored from the remote store (`RestartState`); a node that is not cluster-manager-eligible may come back with any term and state. Outside the model (assumptions): a node's cluster-manager role never changes; persisted state is never rolled back; the offline `opensearch-node` tools are not used; bootstrap requirements name the same node at every node; every node uses the same election strategy; a publication delivered through the remote cluster-state store reconstructs exactly the published state. The per-node abstractions of `OpenSearchCoordination` apply (terms are naturals, versions integers without overflow, the remote persisted state omitted). The safety theorems assume `P.InitCompatible` and `P.strategy = ElectionStrategy.DEFAULT_INSTANCE`. The file imports only the `OpenSearchCoordination` definitions (Lean core).
-- source:
--   OpenSearch b2a54ba5c0defba3d1d20423e911d4bf920bab19: CoordinationState (the per-node handlers as transcribed by the OpenSearchCoordination mission; handleCommit lines 523-573, isPublishQuorum 156-158, invariant 601-611): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/CoordinationState.java; Coordinator (the calls into CoordinationState: handleApplyCommit lines 419-452, handlePublishRequest 454-526, startElection 583-602, abdicateTo 604-620, ensureTermAtLeast 635-641, joinLeaderInTerm 643-657, setInitialConfiguration 1101-1161, handleJoin 1267-1299, publish 1350 with the handleClientValue call at 1404, CoordinatorPublication.handlePublishResponse 1871-1876): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/Coordinator.java; ClusterBootstrapService (requirements 146-157, onFoundPeersUpdated 176-215, startBootstrap 259-273, checkRequirements 306-335): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ClusterBootstrapService.java#L146-L335; GatewayMetaState.start (persisted state loaded and rebuilt 141-231, remote restore 169-188, synchronous and asynchronous persistence 199-207, nodes without the cluster-manager and data roles 232-255): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/gateway/GatewayMetaState.java#L126-L257; PersistedStateRegistry.addPersistedState (lines 38-41): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/PersistedStateRegistry.java#L38-L41; ElectionStrategy (DEFAULT_INSTANCE lines 46-59): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ElectionStrategy.java#L44-L110; the randomized safety test CoordinationStateTestCluster (reboot 156-193, runRandomly 279-329, invariant 331-370): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/test/framework/src/main/java/org/opensearch/cluster/coordination/CoordinationStateTestCluster.java and CoordinationStateTests.testSafety (lines 917-924): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/test/java/org/opensearch/cluster/coordination/CoordinationStateTests.java#L917-L924; for comparison, Elastic's TLA+ model ZenWithTerms (HandleCommit 241-250, CommittedValuesDescendantsFromInitialValue 338-347, CommitHasQuorumVsPreviousCommittedConfiguration 349-358): https://github.com/elastic/elasticsearch-formal-models/blob/ca30663506a7e18de9d23fabbc70a369903d7c98/ZenWithTerms/tla/ZenWithTerms.tla

import Definitions.Def_OpenSearchCoordination

/-!
# OpenSearch cluster coordination: the cluster

Every node runs the `CoordinationState` of `Def_OpenSearchCoordination` (OpenSearch
`b2a54ba5c0defba3d1d20423e911d4bf920bab19`). Nodes exchange messages through a network that may lose, duplicate, delay
and reorder them: a message, once sent, stays available forever and may be handled any number of times, by any node it
is addressed to, or never. Nodes may crash and restart at any time.

Each step is a successful call of one `CoordinationState` method, its output, if any, being sent. The steps cover every
call the `Coordinator` makes (`Coordinator.java`, cited `CO:<line>`; the `Coordinator`'s own guards only reject more):
* `bootstrap`: `setInitialState` with a bootstrap configuration (`ClusterBootstrapService`, CO:1101-1161), under the
  method's asserted preconditions; nodes may bootstrap with different configurations (`BootstrapConfig` describes
  `ClusterBootstrapService`'s configurations; the model does not refer to it);
* `startJoin`: `handleStartJoin` for a request from any cluster-manager-eligible node in any term (elections, abdication,
  and `ensureTermAtLeast` on receiving a message of a higher term, which joins that message's sender); the `Join` is
  sent to the requester;
* `join`: `handleJoin` of a sent `Join` addressed to the node;
* `clientValue`: `handleClientValue` of any cluster state satisfying the asserted precondition; the `PublishRequest` is
  sent to every node;
* `publish`: `handlePublishRequest` of a sent `PublishRequest`; the `PublishResponse` goes back to the publisher;
* `respond`: `handlePublishResponse` of a sent `PublishResponse` addressed to the node; a resulting `ApplyCommitRequest`
  is sent to every node;
* `commit`: `handleCommit` of a sent `ApplyCommitRequest`;
* `restart`: a new `CoordinationState` over the persisted state. A cluster-manager-eligible node persists its current
  term and accepted state synchronously (`GatewayMetaState.LucenePersistedState`) and rebuilds on startup the parts of
  the accepted state that are not persisted (the node list, routing table, transient settings;
  GatewayMetaState.java:164-197); the model leaves the metadata version, the cluster-manager node and the payload free,
  which only adds behaviours. A node that never joined a cluster (term 0, empty configurations, unknown cluster UUID)
  may instead come back with a term-0 state with empty configurations, as restored from the remote store
  (GatewayMetaState.java:169-188). A node that is not cluster-manager-eligible persists asynchronously or not at all,
  and may come back with any persisted state.

A `PublishRequest` records, as ghost data that the real message does not carry, the term and version of the state its
publisher had accepted when it published (its parent); this defines descent between published states.

OpenSearch's randomized safety test `CoordinationStateTestCluster` (`test/framework/.../coordination/`) runs random
executions of a similar model (messages are never removed, start-join requests carry arbitrary terms, any elected node
publishes arbitrary values and configurations, and nodes reboot) and checks the assertions of `invariant()` at every
node and, at the end, one cluster-manager per term and one cluster state per (term, version).

Assumptions (outside the model): the cluster-manager role of a node never changes (changing it and back can reset the
persisted term, GatewayMetaState.java:232-255); no disk rollback; no offline tools (`opensearch-node` unsafe-bootstrap,
detach-cluster, remove-settings, remove-customs); bootstrap requirements name the same node at every node; one election
strategy for all nodes; a publication delivered through the remote store reconstructs exactly the published state.
-/

namespace OpenSearchSafety

open OpenSearchCoordination

/-- Messages. -/
inductive Message (V : Type) where
  | join (j : Join)
  /-- A `PublishRequest` from `source`, with the ghost parent (term, version). -/
  | publishRequest (source : NodeId) (state : ClusterState V) (parentTerm : Nat) (parentVersion : Int)
  /-- A `PublishResponse` from `source` to `dest`. -/
  | publishResponse (source dest : NodeId) (resp : PublishResponse)
  | applyCommit (c : ApplyCommitRequest)

/-- The fixed parameters of a cluster. -/
structure Params where
  /-- `DiscoveryNode.isClusterManagerNode()` of each node. -/
  eligible : NodeId → Bool
  /-- The configurations a node may bootstrap with. -/
  initConfs : VotingConfiguration → Prop
  /-- The election strategy of every node. -/
  strategy : ElectionStrategy

/-- The `DiscoveryNode` of node `n`. -/
def Params.dn (P : Params) (n : NodeId) : DiscoveryNode := ⟨n, P.eligible n⟩

/-- The bootstrap configurations are compatible: votes of cluster-manager-eligible nodes that form a quorum of one
bootstrap configuration share a voter with votes that form a quorum of another. -/
def Params.InitCompatible (P : Params) : Prop :=
  ∀ X Y, P.initConfs X → P.initConfs Y → ∀ q₁ q₂ : List NodeId,
    (∀ x ∈ q₁, P.eligible x = true) → (∀ x ∈ q₂, P.eligible x = true) →
    X.hasQuorum q₁ = true → Y.hasQuorum q₂ = true → ∃ x, x ∈ q₁ ∧ x ∈ q₂

/-- The form of the configurations `ClusterBootstrapService` bootstraps with (CBS:176-215, CBS:259-273, CBS:306-335):
the bootstrap requirements (`cluster.initial_cluster_manager_nodes`, without duplicates) are numbered `0 … k-1`;
requirement `i`, when the node has discovered the node it names, contributes that node's id `resolve i`, and otherwise a
placeholder id `placeholder i` (`"{bootstrap-placeholder}-" + requirement`); more than half of the requirements must be
matched. The predicate does not require `resolve` or `placeholder` to be injective or their values to be distinct
(`bootstrap_compatible` assumes this), nor the bootstrapping node to be eligible and matched (Java requires both,
CBS:179, 202-209). No other definition refers to it: the `bootstrap` step uses `P.initConfs`. -/
def BootstrapConfig (k : Nat) (resolve placeholder : Nat → NodeId) (matched : Nat → Bool)
    (X : VotingConfiguration) : Prop :=
  (∀ x, x ∈ X.nodeIds ↔ ∃ i, i < k ∧ x = if matched i then resolve i else placeholder i) ∧
  ((List.range k).filter matched).length * 2 > k

/-- A cluster: the coordination state of every node and the set of messages sent so far. -/
structure Cluster (V : Type) where
  node : NodeId → CoordinationState V
  sent : Message V → Prop

namespace Cluster

variable {V : Type}

/-- Replace node `n`'s state. -/
def set (W : Cluster V) (n : NodeId) (cs : CoordinationState V) : Cluster V :=
  { W with node := fun m => if m = n then cs else W.node m }

/-- Send a message. -/
def send (W : Cluster V) (m : Message V) : Cluster V := { W with sent := fun x => W.sent x ∨ x = m }

end Cluster

variable {V : Type}

/-- A fresh cluster: every node is in term 0 with an accepted term-0 state with empty configurations (its version,
metadata version, cluster-manager node, cluster-UUID flags and payload are arbitrary and may differ between nodes — a
fresh node has version 0, a node restored from the remote store or upgraded from an older version may have others),
and no message has been sent. -/
def Initial (P : Params) (W : Cluster V) : Prop :=
  (∀ n, ∃ s : ClusterState V, s.term = 0 ∧ s.lastCommittedConfiguration = VotingConfiguration.EMPTY_CONFIG ∧
      s.lastAcceptedConfiguration = VotingConfiguration.EMPTY_CONFIG ∧
      W.node n = CoordinationState.init (P.dn n) 0 s) ∧
  (∀ m, ¬ W.sent m)

/-- The accepted state a restarting cluster-manager-eligible node comes back with, given the one it had: the persisted
term, version, configurations and cluster-UUID flags, with the rest (metadata version, cluster-manager node, payload)
left free — Java rebuilds the cluster-manager node and the parts of the state outside the persisted metadata, and
leaving the persisted metadata free only adds behaviours; or, if it never joined a cluster (term 0, empty
configurations, unknown cluster UUID), a term-0 state with empty configurations, as restored from the remote store. -/
def RestartState (s s' : ClusterState V) : Prop :=
  (s'.term = s.term ∧ s'.version = s.version ∧
    s'.lastCommittedConfiguration = s.lastCommittedConfiguration ∧
    s'.lastAcceptedConfiguration = s.lastAcceptedConfiguration ∧
    s'.clusterUUIDKnown = s.clusterUUIDKnown ∧ s'.clusterUUIDCommitted = s.clusterUUIDCommitted) ∨
  (s.term = 0 ∧ s.lastCommittedConfiguration = VotingConfiguration.EMPTY_CONFIG ∧
    s.lastAcceptedConfiguration = VotingConfiguration.EMPTY_CONFIG ∧ s.clusterUUIDKnown = false ∧
    s'.term = 0 ∧ s'.lastCommittedConfiguration = VotingConfiguration.EMPTY_CONFIG ∧
    s'.lastAcceptedConfiguration = VotingConfiguration.EMPTY_CONFIG)

/-- One step of the cluster. -/
inductive Step (P : Params) : Cluster V → Cluster V → Prop where
  | bootstrap (W : Cluster V) (n : NodeId) (X : VotingConfiguration) (s : ClusterState V)
      (cs' : CoordinationState V) (hX : P.initConfs X)
      (hcontract : (W.node n).initialStateContract s)
      (hconf : s.lastCommittedConfiguration = X ∧ s.lastAcceptedConfiguration = X)
      (h : (W.node n).setInitialState s = .ok cs') :
      Step P W (W.set n cs')
  | startJoin (W : Cluster V) (n src : NodeId) (t : Nat) (cs' : CoordinationState V) (j : Join)
      (hsrc : P.eligible src = true)
      (h : (W.node n).handleStartJoin ⟨P.dn src, t⟩ = .ok (cs', j)) :
      Step P W ((W.set n cs').send (.join j))
  | join (W : Cluster V) (n : NodeId) (j : Join) (cs' : CoordinationState V) (b : Bool)
      (hsent : W.sent (.join j)) (hdest : j.targetNode.id = n)
      (h : (W.node n).handleJoin P.strategy j = .ok (cs', b)) :
      Step P W (W.set n cs')
  | clientValue (W : Cluster V) (n : NodeId) (s : ClusterState V) (cs' : CoordinationState V)
      (p : PublishRequest V) (hcontract : (W.node n).clientValueContract s)
      (h : (W.node n).handleClientValue s = .ok (cs', p)) :
      Step P W ((W.set n cs').send (.publishRequest n p.acceptedState (W.node n).lastAcceptedTerm
        (W.node n).lastAcceptedVersion))
  | publish (W : Cluster V) (n src : NodeId) (s : ClusterState V) (pt : Nat) (pv : Int)
      (cs' : CoordinationState V) (r : PublishResponse) (hsent : W.sent (.publishRequest src s pt pv))
      (h : (W.node n).handlePublishRequest ⟨s⟩ = .ok (cs', r)) :
      Step P W ((W.set n cs').send (.publishResponse n src r))
  | respond (W : Cluster V) (n src : NodeId) (r : PublishResponse) (cs' : CoordinationState V)
      (o : Option ApplyCommitRequest) (hsent : W.sent (.publishResponse src n r))
      (h : (W.node n).handlePublishResponse (P.dn src) r = .ok (cs', o)) :
      Step P W (match o with
        | none => W.set n cs'
        | some c => (W.set n cs').send (.applyCommit c))
  | commit (W : Cluster V) (n : NodeId) (c : ApplyCommitRequest) (cs' : CoordinationState V)
      (hsent : W.sent (.applyCommit c)) (h : (W.node n).handleCommit c = .ok cs') :
      Step P W (W.set n cs')
  | restart (W : Cluster V) (n : NodeId) (s' : ClusterState V) (hn : P.eligible n = true)
      (hs : RestartState (W.node n).lastAcceptedState s') :
      Step P W (W.set n (CoordinationState.init (W.node n).localNode (W.node n).currentTerm s'))
  | restartAny (W : Cluster V) (n : NodeId) (t : Nat) (s' : ClusterState V) (hn : P.eligible n = false) :
      Step P W (W.set n (CoordinationState.init (W.node n).localNode t s'))

/-- The clusters reachable from a fresh cluster. -/
inductive Reachable (P : Params) : Cluster V → Prop where
  | init (W : Cluster V) : Initial P W → Reachable P W
  | step (W W' : Cluster V) : Reachable P W → Step P W W' → Reachable P W'

/-- A (term, version) is committed when an `ApplyCommitRequest` for it has been sent (that it is then the key of a sent
publication follows from the invariant, `inv_committed_published`). -/
def Committed (W : Cluster V) (t : Nat) (v : Int) : Prop := ∃ src, W.sent (.applyCommit ⟨src, t, v⟩)

/-- `(t, v)` is the parent of `(t', v')`: a publication of `(t', v')` was made on top of an accepted `(t, v)`. -/
def Parent (W : Cluster V) (t : Nat) (v : Int) (t' : Nat) (v' : Int) : Prop :=
  ∃ src s, W.sent (.publishRequest src s t v) ∧ s.term = t' ∧ s.version = v'

/-- Descent between (term, version) pairs: the reflexive-transitive closure of `Parent` (reflexive on every pair,
published or not). -/
inductive Descends (W : Cluster V) : Nat → Int → Nat → Int → Prop where
  | refl (t : Nat) (v : Int) : Descends W t v t v
  | step (t : Nat) (v : Int) (t' : Nat) (v' : Int) (t'' : Nat) (v'' : Int) :
      Descends W t v t' v' → Parent W t' v' t'' v'' → Descends W t v t'' v''

/-! ## The inductive invariant

Proof-side notions (none of them is used by the model above) and the invariant `Inv`, from which the safety theorems
follow. A publication is named by its *key*, its (term, version); its ghost parent is the key of the state its publisher
had accepted. Publications thus form a forest: following parents, versions strictly decrease until a term-0 key, the
*root*, which stands for a bootstrap state (several nodes may bootstrap, with different bootstrap configurations). All
notions are relations, never functions computed from the messages sent: `KeyLE` and `Below` compare keys, `Won` also
reads node states, and the others depend on the messages sent only. All sets of voters are lists of
cluster-manager-eligible nodes, so that `Params.InitCompatible` applies to them. -/

/-- The lexicographic order on (term, version) keys: `(t, v)` is at most `(t', v')`. -/
def KeyLE (t : Nat) (v : Int) (t' : Nat) (v' : Int) : Prop := t < t' ∨ (t = t' ∧ v ≤ v')

/-- The last accepted (term, version) `(lt, lv)` carried by a join is at or below the base `(bt, bv)` in the way
`handleJoin` compares them: an older term, or the same term and, unless that term is 0, a version at most `bv`.
(At term 0 a join carries a metadata version, `versionOrMetadataVersion`, which plays no role in safety.) -/
def Below (lt : Nat) (lv : Int) (bt : Nat) (bv : Int) : Prop := lt < bt ∨ (lt = bt ∧ (bt = 0 ∨ lv ≤ bv))

/-- A publication of term `t` and version `v` has been sent. -/
def Published (W : Cluster V) (t : Nat) (v : Int) : Prop :=
  ∃ src s pt pv, W.sent (.publishRequest src s pt pv) ∧ s.term = t ∧ s.version = v

/-- The pair of configurations `(x, y)` (last committed, last accepted) *realizes* the key `(t, v)`: either `t = 0`
and `x = y` is a bootstrap configuration (a bootstrap state), or `(t, v)` is the key of a sent publication whose last
accepted configuration is `y` and whose last committed configuration is `x` — or, if `(t, v)` is committed, whose last
accepted configuration is also `x` (a node that applied the commit, `markCommitted`). The accepted state of every
bootstrapped cluster-manager-eligible node realizes its own key (`Inv.accepted_realizes`). -/
def Realizes (P : Params) (W : Cluster V) (t : Nat) (v : Int) (x y : VotingConfiguration) : Prop :=
  (t = 0 ∧ x = y ∧ P.initConfs x) ∨
  ∃ src s pt pv, W.sent (.publishRequest src s pt pv) ∧ s.term = t ∧ s.version = v ∧
    y = s.lastAcceptedConfiguration ∧
    (x = s.lastCommittedConfiguration ∨ (x = s.lastAcceptedConfiguration ∧ Committed W t v))

/-- Every member of `J` is a cluster-manager-eligible node that sent node `L` a join for term `t`. -/
def JoinVoters (P : Params) (W : Cluster V) (L : NodeId) (t : Nat) (J : List NodeId) : Prop :=
  ∀ x ∈ J, P.eligible x = true ∧
    ∃ j : Join, W.sent (.join j) ∧ j.sourceNode.id = x ∧ j.targetNode.id = L ∧ j.term = t

/-- Every member of `J` is a cluster-manager-eligible node that sent node `L` a join for term `t` whose last accepted
(term, version) is `Below` the base `(bt, bv)`. -/
def BaseVoters (P : Params) (W : Cluster V) (L : NodeId) (t bt : Nat) (bv : Int) (J : List NodeId) : Prop :=
  ∀ x ∈ J, P.eligible x = true ∧
    ∃ j : Join, W.sent (.join j) ∧ j.sourceNode.id = x ∧ j.targetNode.id = L ∧ j.term = t ∧
      Below j.lastAcceptedTerm j.lastAcceptedVersion bt bv

/-- Every member of `A` is a cluster-manager-eligible node that sent a `PublishResponse` for term `t` and version
`v` (to any node). -/
def RespVoters (P : Params) (W : Cluster V) (t : Nat) (v : Int) (A : List NodeId) : Prop :=
  ∀ x ∈ A, P.eligible x = true ∧ ∃ d, W.sent (.publishResponse x d ⟨t, v⟩)

/-- An *election record* of node `L` for term `t`: the base `(bt, bv)` is of an older term, `(x, y)` realizes it, and
`J`, a quorum of both `x` and `y`, consists of eligible nodes that each sent `L` a term-`t` join with a last accepted
(term, version) `Below` the base. Both a node that has just won its election (its accepted state is the base) and the
first publication of a term (the publisher's state when it won) carry one. -/
def ElectionRecord (P : Params) (W : Cluster V) (L : NodeId) (t bt : Nat) (bv : Int) (x y : VotingConfiguration)
    (J : List NodeId) : Prop :=
  bt < t ∧ Realizes P W bt bv x y ∧ BaseVoters P W L t bt bv J ∧ x.hasQuorum J = true ∧ y.hasQuorum J = true

/-- Node `b` *won* term `t`: it is cluster-manager-eligible, and it has currently won the election of its current
term `t`, or it has sent a publication of term `t`. -/
def Won (P : Params) (W : Cluster V) (b : NodeId) (t : Nat) : Prop :=
  P.eligible b = true ∧
    (((W.node b).electionWon = true ∧ (W.node b).currentTerm = t) ∨
      ∃ s pt pv, W.sent (.publishRequest b s pt pv) ∧ s.term = t)

/-- The inductive invariant. Field names are descriptive; each docstring names the conjunct of the design it
transcribes (labels P*, C1, J*, R*, N*, L*, listed in `NOTES_OpenSearchSafety.md`). Node facts about the persisted
state hold for cluster-manager-eligible nodes only (a node that is not eligible may restart with any persisted state);
facts about the transient state hold for every node (a node that is not eligible never receives a join, so never holds
votes or wins). -/
structure Inv (P : Params) (W : Cluster V) : Prop where
  -- Every node.
  /-- Every node's `localNode` is its own `DiscoveryNode` `P.dn n`. -/
  localNode_eq : ∀ n, (W.node n).localNode = P.dn n
  /-- (N4) A node that has not won its election has last published version 0 and holds no publish votes. -/
  idle_of_not_won : ∀ n, (W.node n).electionWon = false →
    (W.node n).lastPublishedVersion = 0 ∧ (W.node n).publishVotes = VoteCollection.empty
  /-- (N2) A node that has won its election has started a join since its last restart. -/
  won_started : ∀ n, (W.node n).electionWon = true → (W.node n).startedJoinSinceLastReboot = true
  /-- (N6) A node that holds join votes has started a join since its last restart. -/
  votes_started : ∀ n, (W.node n).joinVotes.nodes ≠ [] → (W.node n).startedJoinSinceLastReboot = true
  /-- (N10) A node that has started a join since its last restart is in a term ≥ 1. -/
  started_term_pos : ∀ n, (W.node n).startedJoinSinceLastReboot = true → 1 ≤ (W.node n).currentTerm
  /-- (N3) The join votes of a node that has won are a quorum of both its last committed and its last accepted
  configuration. -/
  won_quorum : ∀ n, (W.node n).electionWon = true →
    (W.node n).joinVotes.isQuorum (W.node n).lastCommittedConfiguration = true ∧
    (W.node n).joinVotes.isQuorum (W.node n).lastAcceptedConfiguration = true
  /-- (N3r: for the default election strategy, the reverse half of `invariant()`'s second assertion; it omits the
  strategy's additional constraint) The join votes of a node that has not won are not a quorum of both its last
  committed and its last accepted configuration. -/
  not_won_no_quorum : ∀ n, (W.node n).electionWon = false →
    ¬ ((W.node n).joinVotes.isQuorum (W.node n).lastCommittedConfiguration = true ∧
      (W.node n).joinVotes.isQuorum (W.node n).lastAcceptedConfiguration = true)
  /-- (N8) Every join vote node `n` holds is of an eligible node `m` that sent `n` a join for `n`'s current term, with
  a last accepted (term, version) `Below` `n`'s last accepted (term, version). -/
  joinVotes_sent : ∀ n m, m ∈ (W.node n).joinVotes.nodes → P.eligible m = true ∧
    ∃ j : Join, W.sent (.join j) ∧ j.sourceNode.id = m ∧ j.targetNode.id = n ∧
      j.term = (W.node n).currentTerm ∧
      Below j.lastAcceptedTerm j.lastAcceptedVersion (W.node n).lastAcceptedTerm (W.node n).lastAcceptedVersion
  /-- (N9) Every publish vote node `n` holds is of an eligible node `m` that sent `n` a `PublishResponse` for `n`'s
  current term and last published version. -/
  publishVotes_sent : ∀ n m, m ∈ (W.node n).publishVotes.nodes → P.eligible m = true ∧
    W.sent (.publishResponse m n ⟨(W.node n).currentTerm, (W.node n).lastPublishedVersion⟩)
  -- Cluster-manager-eligible nodes.
  /-- (N1) The last accepted term of an eligible node is at most its current term. -/
  term_le : ∀ n, P.eligible n = true → (W.node n).lastAcceptedTerm ≤ (W.node n).currentTerm
  /-- (N7) The accepted state of an eligible node is either a never-bootstrapped term-0 state with empty
  configurations, or its configurations `Realize` its key: a bootstrap state with a bootstrap configuration, or a sent
  publication's term, version and configurations (the last committed one possibly replaced by the last accepted one,
  if the publication is committed). Nothing else of the state (payload, metadata version, cluster-manager node,
  cluster-UUID flags) is related to the publication, since a restart may rebuild it. -/
  accepted_realizes : ∀ n, P.eligible n = true →
    ((W.node n).lastAcceptedTerm = 0 ∧
      (W.node n).lastCommittedConfiguration = VotingConfiguration.EMPTY_CONFIG ∧
      (W.node n).lastAcceptedConfiguration = VotingConfiguration.EMPTY_CONFIG) ∨
    Realizes P W (W.node n).lastAcceptedTerm (W.node n).lastAcceptedVersion
      (W.node n).lastCommittedConfiguration (W.node n).lastAcceptedConfiguration
  -- Joins and publish responses.
  /-- Every join comes from the `DiscoveryNode` of its source and is addressed to an eligible node. -/
  join_wf : ∀ j : Join, W.sent (.join j) →
    j.sourceNode = P.dn j.sourceNode.id ∧ P.eligible j.targetNode.id = true
  /-- (J1) An eligible node's joins are for terms at most its current term. -/
  join_term_le : ∀ j : Join, W.sent (.join j) → P.eligible j.sourceNode.id = true →
    j.term ≤ (W.node j.sourceNode.id).currentTerm
  /-- (J2) An eligible node sends at most one join per term. -/
  join_unique : ∀ j j' : Join, W.sent (.join j) → W.sent (.join j') → P.eligible j.sourceNode.id = true →
    j.sourceNode.id = j'.sourceNode.id → j.term = j'.term → j = j'
  /-- (J3) An eligible node's join for a term later than one of its publish responses carries a last accepted
  (term, version) at least that of the response: it accepted before it voted. -/
  join_after_response : ∀ (j : Join) (a d : NodeId) (r : PublishResponse), W.sent (.join j) →
    W.sent (.publishResponse a d r) → j.sourceNode.id = a → P.eligible a = true → r.term < j.term →
    KeyLE r.term r.version j.lastAcceptedTerm j.lastAcceptedVersion
  /-- (R1) An eligible node's publish responses are for terms at most its current term, and for (term, version)s at
  most its last accepted (term, version). -/
  response_le : ∀ (a d : NodeId) (r : PublishResponse), W.sent (.publishResponse a d r) → P.eligible a = true →
    r.term ≤ (W.node a).currentTerm ∧
    KeyLE r.term r.version (W.node a).lastAcceptedTerm (W.node a).lastAcceptedVersion
  /-- (R2) Every publish response answers a publication of its (term, version) sent by the node it is addressed to. -/
  response_published : ∀ (a d : NodeId) (r : PublishResponse), W.sent (.publishResponse a d r) →
    ∃ s pt pv, W.sent (.publishRequest d s pt pv) ∧ s.term = r.term ∧ s.version = r.version
  -- Publications.
  /-- (P1) Every publication is sent by an eligible node, has term ≥ 1 (so the Zen1 branch of
  `handlePublishRequest` is dead), a parent of at most its term and of a smaller version, and, if its parent is a
  bootstrap state (term 0), a bootstrap configuration as last committed configuration. -/
  pub_wf : ∀ src s pt pv, W.sent (.publishRequest src s pt pv) →
    P.eligible src = true ∧ 1 ≤ s.term ∧ pt ≤ s.term ∧ pv < s.version ∧
    (pt = 0 → P.initConfs s.lastCommittedConfiguration)
  /-- (P1, P5) The parent of a publication, if not a bootstrap state, is a publication (of key `(pt, pv)`), and the
  configurations follow the reconfiguration discipline: the last committed configuration is the parent's, or, if the
  parent is committed, the parent's last accepted one (reconfiguration rule R1); and the last accepted configuration
  changes only if the last committed configuration is the parent's last accepted one (reconfiguration rule R2). -/
  pub_parent : ∀ src s pt pv, W.sent (.publishRequest src s pt pv) → 1 ≤ pt →
    ∃ src' s' pt' pv', W.sent (.publishRequest src' s' pt' pv') ∧ s'.term = pt ∧ s'.version = pv ∧
      (s.lastCommittedConfiguration = s'.lastCommittedConfiguration ∨
        (s.lastCommittedConfiguration = s'.lastAcceptedConfiguration ∧ Committed W pt pv)) ∧
      (s.lastAcceptedConfiguration ≠ s'.lastAcceptedConfiguration →
        s.lastCommittedConfiguration = s'.lastAcceptedConfiguration)
  /-- (P2) Two publications with the same key are the same message (source, state and parent). -/
  pub_unique : ∀ src s pt pv src' s' pt' pv', W.sent (.publishRequest src s pt pv) →
    W.sent (.publishRequest src' s' pt' pv') → s.term = s'.term → s.version = s'.version →
    src = src' ∧ s = s' ∧ pt = pt' ∧ pv = pv'
  /-- Every publication descends from a root (a term-0 key): the chain of its ancestors is finite. -/
  pub_rooted : ∀ src s pt pv, W.sent (.publishRequest src s pt pv) → ∃ v₀, Descends W 0 v₀ s.term s.version
  /-- (P4) Two publications of the same term are related by descent. -/
  pub_same_term : ∀ src s pt pv src' s' pt' pv', W.sent (.publishRequest src s pt pv) →
    W.sent (.publishRequest src' s' pt' pv') → s.term = s'.term →
    Descends W s.term s.version s'.term s'.version ∨ Descends W s'.term s'.version s.term s.version
  /-- (P6) The eligible nodes that sent the publisher a join for the publication's term include a quorum of both of
  the publication's configurations. -/
  pub_voters : ∀ src s pt pv, W.sent (.publishRequest src s pt pv) →
    ∃ J, JoinVoters P W src s.term J ∧ s.lastCommittedConfiguration.hasQuorum J = true ∧
      s.lastAcceptedConfiguration.hasQuorum J = true
  /-- (P7) The first publication of a term (its parent is of an older term) carries the election record of its
  publisher: the parent key, realized by the publication's last committed configuration and some `y` (the parent's
  last accepted configuration), with a quorum of joins `Below` the parent. -/
  pub_election : ∀ src s pt pv, W.sent (.publishRequest src s pt pv) → pt < s.term →
    ∃ y J, ElectionRecord P W src s.term pt pv s.lastCommittedConfiguration y J
  -- Commits.
  /-- (C1, with the weakening forced by `handleCommit` at a leader, D1) Every commit is of a sent publication whose
  publish responses from eligible nodes include a quorum `A` of its last accepted configuration and either of its last
  committed configuration, or (D1) its parent is committed and has the same last accepted configuration. -/
  commit_quorum : ∀ c : ApplyCommitRequest, W.sent (.applyCommit c) →
    ∃ src s pt pv, W.sent (.publishRequest src s pt pv) ∧ s.term = c.term ∧ s.version = c.version ∧
      ∃ A, RespVoters P W c.term c.version A ∧ s.lastAcceptedConfiguration.hasQuorum A = true ∧
        (s.lastCommittedConfiguration.hasQuorum A = true ∨
          (Committed W pt pv ∧ ∃ src' s' pt' pv', W.sent (.publishRequest src' s' pt' pv') ∧ s'.term = pt ∧
            s'.version = pv ∧ s'.lastAcceptedConfiguration = s.lastAcceptedConfiguration))
  -- Leaders.
  /-- (L1) For each term `t`, at most one node `b` has `Won P W b t`. -/
  won_unique : ∀ a b t, Won P W a t → Won P W b t → a = b
  /-- (L2) A node that published in a term is past that term, or still in it and either still elected or restarted
  since (so it cannot win that term again). -/
  pub_source_term : ∀ src s pt pv, W.sent (.publishRequest src s pt pv) →
    s.term < (W.node src).currentTerm ∨
    (s.term = (W.node src).currentTerm ∧
      ((W.node src).electionWon = true ∨ (W.node src).startedJoinSinceLastReboot = false))
  /-- (L3) Every publication of an elected node's current term, whoever sent it, has a version at most the node's last
  published version, (current term, last published version) descends from it, and the node's join votes are a quorum
  of both of its configurations. -/
  leader_pubs : ∀ n, (W.node n).electionWon = true → ∀ src s pt pv, W.sent (.publishRequest src s pt pv) →
    s.term = (W.node n).currentTerm →
    s.version ≤ (W.node n).lastPublishedVersion ∧
    Descends W s.term s.version (W.node n).currentTerm (W.node n).lastPublishedVersion ∧
    (W.node n).joinVotes.isQuorum s.lastCommittedConfiguration = true ∧
    (W.node n).joinVotes.isQuorum s.lastAcceptedConfiguration = true
  /-- (L4) An elected node with a publication in flight (last published version ≠ last accepted version) sent it on
  top of its current accepted key; its last published configuration is that publication's last accepted one; and its
  last committed configuration is the publication's, or (D1: the node applied the commit of its accepted state) the
  publication's last accepted configuration, its accepted state being committed with that same last accepted
  configuration. -/
  leader_inflight : ∀ n, (W.node n).electionWon = true →
    (W.node n).lastPublishedVersion ≠ (W.node n).lastAcceptedVersion →
    ∃ s, W.sent (.publishRequest n s (W.node n).lastAcceptedTerm (W.node n).lastAcceptedVersion) ∧
      s.term = (W.node n).currentTerm ∧ s.version = (W.node n).lastPublishedVersion ∧
      (W.node n).lastPublishedConfiguration = s.lastAcceptedConfiguration ∧
      ((W.node n).lastCommittedConfiguration = s.lastCommittedConfiguration ∨
        ((W.node n).lastCommittedConfiguration = s.lastAcceptedConfiguration ∧
          Committed W (W.node n).lastAcceptedTerm (W.node n).lastAcceptedVersion ∧
          (W.node n).lastAcceptedConfiguration = s.lastAcceptedConfiguration))
  /-- (L5) An elected node with no publication in flight has either accepted a publication of its term (and its last
  published configuration is its last accepted one), or has an accepted state of an older term and no publication of
  its term exists. -/
  leader_settled : ∀ n, (W.node n).electionWon = true →
    (W.node n).lastPublishedVersion = (W.node n).lastAcceptedVersion →
    ((W.node n).lastAcceptedTerm = (W.node n).currentTerm ∧
      (W.node n).lastPublishedConfiguration = (W.node n).lastAcceptedConfiguration) ∨
    ((W.node n).lastAcceptedTerm < (W.node n).currentTerm ∧
      ∀ src s pt pv, W.sent (.publishRequest src s pt pv) → s.term ≠ (W.node n).currentTerm)

end OpenSearchSafety


