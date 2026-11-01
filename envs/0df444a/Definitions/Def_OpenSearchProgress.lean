-- Prove2me | Definitions.Def_OpenSearchProgress
-- name    : OpenSearchProgress
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-11-01T01:00:27.292947+00:00
-- url     : https://prove2.me/theorems/0cdef1da-8e68-428f-b453-47b78f2adba0
-- title:
--   OpenSearch cluster coordination in a stable period: the steps and executions of a stable election and of a stable publication
-- statement:
--   Stable periods of the cluster model of the `OpenSearchSafety` mission (OpenSearch revision `b2a54ba5c0defba3d1d20423e911d4bf920bab19`), whose `Params`, `Cluster`, `Message`, `Step`, `RestartState`, `Reachable` and `Committed` are used as they are, over the per-node `CoordinationState` of the `OpenSearchCoordination` mission. A stable period is a window in which one node runs for election (or publishes) and the steps excluded below do not occur, while every other step of the cluster remains possible. Each stable step is one of the nine kinds of `Step` (`bootstrap`, `startJoin`, `join`, `clientValue`, `publish`, `respond`, `commit`, `restart`, `restartAny`), with the same hypotheses and the same effect, and possibly an extra hypothesis.
--
--   **`ElectionStep P c t Q kt kv W W'`** — a step of a stable election period for the candidate `c` in term `t` with voters `Q` (a list of node ids), where `(kt, kv)` stands for the term and version of `c`'s accepted state when the period starts:
--   - `bootstrap` at a node `n` only if `n ≠ c` and `n ∉ Q`;
--   - `startJoin` (any node handling a request from a cluster-manager-eligible `src` for a term `t'`) only if `t' < t`, or `src = c` and `t' = t`: no start-join request in a term at least `t` other than `c`'s own request for `t`;
--   - `join`, `respond` and `commit` as in `Step`;
--   - `publish` (a node `n` handling a sent publication of a state `s`) only if, when `n = c` or `n ∈ Q`, `s` is no fresher than `(kt, kv)`: `s.term < kt`, or `s.term = kt` and `s.version ≤ kv` (`c` and the voters do not accept a stale publication of a former cluster-manager that is fresher than `c`'s state);
--   - `restart` of a cluster-manager-eligible node `n` only if `n ≠ c` and `n ∉ Q`; `restartAny` (a node that is not cluster-manager-eligible) as in `Step`;
--   - no `clientValue` step: no new publication.
--
--   **`ElectionExec P c t Q kt kv W W'`** — `W'` is reached from `W` by finitely many, possibly zero, `ElectionStep`s.
--
--   **`PublicationStep P c t Q W W'`** — a step of a stable publication period for the cluster-manager `c` of term `t` with acknowledging nodes `Q`:
--   - `startJoin` at a node `n` with `n = c` or `n ∈ Q` only for terms `t' ≤ t` (at other nodes, any term);
--   - `clientValue` only at nodes `n ≠ c`: `c` does not publish again;
--   - `restart` of a cluster-manager-eligible node `n` only if `n ≠ c`;
--   - `bootstrap`, `join`, `publish`, `respond`, `commit` and `restartAny` as in `Step`.
--
--   **`PublicationExec P c t Q W W'`** — `W'` is reached from `W` by finitely many, possibly zero, `PublicationStep`s.
--
--   **Formalization Note.** Every stable step is a `Step` of the safety model, so a stable execution from a reachable cluster stays reachable and the safety theorems apply along it. Messages are still never removed: within a stable period a sent message may be handled any number of times, in any order, or never; the four universal theorems (`election_vote_accepted`, `election_won`, `publication_acks_accepted`, `publication_committed`) hold for every finite stable execution, that is, every prefix of a longer one, and the two existence theorems (`election_possible`, `publication_possible`) exhibit one; there is no fairness assumption. A stable period is a hypothesis of the theorems, not a property of the Java system: nothing here says that a real cluster reaches such a period, for how long it lasts, or how long its steps take. The parameters `(kt, kv)` of the election period are instantiated in the theorems with `c`'s last accepted term and version at the start. A voter may be the candidate itself, and `Q` may contain `c` in a publication period. Only the `OpenSearchSafety` definitions are imported (Lean core).
-- source:
--   OpenSearch b2a54ba5c0defba3d1d20423e911d4bf920bab19: Coordinator (handlePublishRequest lines 454-526 with ensureTermAtLeast at 512, startElection 583-602, ensureTermAtLeast 635-641, joinLeaderInTerm 643-657, handleJoin 1267-1287 with handleJoinIgnoringExceptions 1289-1299, publish 1350 with the handleClientValue call at 1404, CoordinatorPublication.handlePublishResponse 1871-1875): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/Coordinator.java; CoordinationState (isPublishQuorum lines 156-158, handleStartJoin 213-255, handleJoin 264-339, handleClientValue 348-407, handlePublishRequest 416-460, handlePublishResponse 471-515, handleCommit 523-573) as transcribed by the OpenSearchCoordination mission: https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/CoordinationState.java; the cluster model, the safety vocabulary and the inductive invariant of the OpenSearchSafety mission (Step, Reachable, Committed, Inv, reachable_inv); for why progress needs a stable period: M. J. Fischer, N. A. Lynch, M. S. Paterson, Impossibility of distributed consensus with one faulty process, J. ACM 32(2), 1985, and C. Dwork, N. Lynch, L. Stockmeyer, Consensus in the presence of partial synchrony, J. ACM 35(2), 1988

import Definitions.Def_OpenSearchSafety

/-!
# OpenSearch cluster coordination: progress under stability

Safety holds in every execution. Progress cannot: in an asynchronous network a message may never be delivered, and
competing candidates can keep raising terms (this is what pre-voting and the randomized election scheduler mitigate).
The theorems of this mission state progress for the executions of a *stable period*: a window in which one node runs
for election (or publishes) and none of the steps that the relations below exclude occurs, while every other step of
the cluster remains possible — deliveries in any order, duplicates, other nodes' joins, acceptances and commits,
restarts of other nodes. Under their hypotheses, they show that in every such execution the candidate, once in the
election term, accepts and counts every voter's join for that term, and every acknowledging node in the
cluster-manager's term has acknowledged its publication or accepts it, while the cluster-manager accepts and counts
every acknowledgement of it sent by an acknowledging node; that once all of a quorum's votes (acknowledgements) are
counted, the election is won (the publication committed); and that such executions exist. No theorem states that the
start-joins an election or a publication needs stay enabled.
-/

namespace OpenSearchProgress

open OpenSearchCoordination OpenSearchSafety

variable {V : Type}

/-- A step of a stable election period for candidate `c` in term `t` with voters `Q`, `(kt, kv)` being the term and
version of `c`'s accepted state when the period starts: any step of the cluster except a start-join in a term at least
`t` other than `c`'s own request for `t`, any new publication, a bootstrap of `c` or of a voter, a restart of `c` or of
a voter that is cluster-manager-eligible (`restartAny`, the restart of a node that is not eligible, is not restricted),
and the acceptance by `c` or a voter of a publication fresher than `(kt, kv)` (a stale publication of a former
cluster-manager arriving during the election). -/
inductive ElectionStep (P : Params) (c : NodeId) (t : Nat) (Q : List NodeId) (kt : Nat) (kv : Int) :
    Cluster V → Cluster V → Prop where
  | bootstrap (W : Cluster V) (n : NodeId) (X : VotingConfiguration) (s : ClusterState V)
      (cs' : CoordinationState V) (hX : P.initConfs X) (hnq : n ≠ c ∧ n ∉ Q)
      (hcontract : (W.node n).initialStateContract s)
      (hconf : s.lastCommittedConfiguration = X ∧ s.lastAcceptedConfiguration = X)
      (h : (W.node n).setInitialState s = .ok cs') :
      ElectionStep P c t Q kt kv W (W.set n cs')
  | startJoin (W : Cluster V) (n src : NodeId) (t' : Nat) (cs' : CoordinationState V) (j : Join)
      (hsrc : P.eligible src = true) (hstable : t' < t ∨ (src = c ∧ t' = t))
      (h : (W.node n).handleStartJoin ⟨P.dn src, t'⟩ = .ok (cs', j)) :
      ElectionStep P c t Q kt kv W ((W.set n cs').send (.join j))
  | join (W : Cluster V) (n : NodeId) (j : Join) (cs' : CoordinationState V) (b : Bool)
      (hsent : W.sent (.join j)) (hdest : j.targetNode.id = n)
      (h : (W.node n).handleJoin P.strategy j = .ok (cs', b)) :
      ElectionStep P c t Q kt kv W (W.set n cs')
  | publish (W : Cluster V) (n src : NodeId) (s : ClusterState V) (pt : Nat) (pv : Int)
      (cs' : CoordinationState V) (r : PublishResponse) (hsent : W.sent (.publishRequest src s pt pv))
      (hfresh : n = c ∨ n ∈ Q → s.term < kt ∨ (s.term = kt ∧ s.version ≤ kv))
      (h : (W.node n).handlePublishRequest ⟨s⟩ = .ok (cs', r)) :
      ElectionStep P c t Q kt kv W ((W.set n cs').send (.publishResponse n src r))
  | respond (W : Cluster V) (n src : NodeId) (r : PublishResponse) (cs' : CoordinationState V)
      (o : Option ApplyCommitRequest) (hsent : W.sent (.publishResponse src n r))
      (h : (W.node n).handlePublishResponse (P.dn src) r = .ok (cs', o)) :
      ElectionStep P c t Q kt kv W (match o with
        | none => W.set n cs'
        | some a => (W.set n cs').send (.applyCommit a))
  | commit (W : Cluster V) (n : NodeId) (a : ApplyCommitRequest) (cs' : CoordinationState V)
      (hsent : W.sent (.applyCommit a)) (h : (W.node n).handleCommit a = .ok cs') :
      ElectionStep P c t Q kt kv W (W.set n cs')
  | restart (W : Cluster V) (n : NodeId) (s' : ClusterState V) (hn : P.eligible n = true)
      (hnq : n ≠ c ∧ n ∉ Q) (hs : RestartState (W.node n).lastAcceptedState s') :
      ElectionStep P c t Q kt kv W (W.set n (CoordinationState.init (W.node n).localNode (W.node n).currentTerm s'))
  | restartAny (W : Cluster V) (n : NodeId) (t' : Nat) (s' : ClusterState V) (hn : P.eligible n = false) :
      ElectionStep P c t Q kt kv W (W.set n (CoordinationState.init (W.node n).localNode t' s'))

end OpenSearchProgress

namespace OpenSearchProgress

open OpenSearchCoordination OpenSearchSafety

variable {V : Type}

/-- The executions of a stable election period: finite sequences of `ElectionStep`s. -/
inductive ElectionExec (P : Params) (c : NodeId) (t : Nat) (Q : List NodeId) (kt : Nat) (kv : Int) :
    Cluster V → Cluster V → Prop where
  | refl (W : Cluster V) : ElectionExec P c t Q kt kv W W
  | step (W W' W'' : Cluster V) : ElectionExec P c t Q kt kv W W' → ElectionStep P c t Q kt kv W' W'' →
      ElectionExec P c t Q kt kv W W''

/-- A step of a stable publication period for the cluster-manager `c` of term `t` with acknowledging nodes `Q`: any step
of the cluster except a start-join in a term above `t` at `c` or at a node of `Q`, a further publication by `c`, and a
restart of `c` if it is cluster-manager-eligible (`restartAny`, the restart of a node that is not eligible, is not
restricted). -/
inductive PublicationStep (P : Params) (c : NodeId) (t : Nat) (Q : List NodeId) : Cluster V → Cluster V → Prop where
  | bootstrap (W : Cluster V) (n : NodeId) (X : VotingConfiguration) (s : ClusterState V)
      (cs' : CoordinationState V) (hX : P.initConfs X)
      (hcontract : (W.node n).initialStateContract s)
      (hconf : s.lastCommittedConfiguration = X ∧ s.lastAcceptedConfiguration = X)
      (h : (W.node n).setInitialState s = .ok cs') :
      PublicationStep P c t Q W (W.set n cs')
  | startJoin (W : Cluster V) (n src : NodeId) (t' : Nat) (cs' : CoordinationState V) (j : Join)
      (hsrc : P.eligible src = true) (hstable : (n = c ∨ n ∈ Q) → t' ≤ t)
      (h : (W.node n).handleStartJoin ⟨P.dn src, t'⟩ = .ok (cs', j)) :
      PublicationStep P c t Q W ((W.set n cs').send (.join j))
  | join (W : Cluster V) (n : NodeId) (j : Join) (cs' : CoordinationState V) (b : Bool)
      (hsent : W.sent (.join j)) (hdest : j.targetNode.id = n)
      (h : (W.node n).handleJoin P.strategy j = .ok (cs', b)) :
      PublicationStep P c t Q W (W.set n cs')
  | clientValue (W : Cluster V) (n : NodeId) (s : ClusterState V) (cs' : CoordinationState V)
      (p : PublishRequest V) (hn : n ≠ c) (hcontract : (W.node n).clientValueContract s)
      (h : (W.node n).handleClientValue s = .ok (cs', p)) :
      PublicationStep P c t Q W ((W.set n cs').send (.publishRequest n p.acceptedState (W.node n).lastAcceptedTerm
        (W.node n).lastAcceptedVersion))
  | publish (W : Cluster V) (n src : NodeId) (s : ClusterState V) (pt : Nat) (pv : Int)
      (cs' : CoordinationState V) (r : PublishResponse) (hsent : W.sent (.publishRequest src s pt pv))
      (h : (W.node n).handlePublishRequest ⟨s⟩ = .ok (cs', r)) :
      PublicationStep P c t Q W ((W.set n cs').send (.publishResponse n src r))
  | respond (W : Cluster V) (n src : NodeId) (r : PublishResponse) (cs' : CoordinationState V)
      (o : Option ApplyCommitRequest) (hsent : W.sent (.publishResponse src n r))
      (h : (W.node n).handlePublishResponse (P.dn src) r = .ok (cs', o)) :
      PublicationStep P c t Q W (match o with
        | none => W.set n cs'
        | some a => (W.set n cs').send (.applyCommit a))
  | commit (W : Cluster V) (n : NodeId) (a : ApplyCommitRequest) (cs' : CoordinationState V)
      (hsent : W.sent (.applyCommit a)) (h : (W.node n).handleCommit a = .ok cs') :
      PublicationStep P c t Q W (W.set n cs')
  | restart (W : Cluster V) (n : NodeId) (s' : ClusterState V) (hn : P.eligible n = true) (hnc : n ≠ c)
      (hs : RestartState (W.node n).lastAcceptedState s') :
      PublicationStep P c t Q W (W.set n (CoordinationState.init (W.node n).localNode (W.node n).currentTerm s'))
  | restartAny (W : Cluster V) (n : NodeId) (t' : Nat) (s' : ClusterState V) (hn : P.eligible n = false) :
      PublicationStep P c t Q W (W.set n (CoordinationState.init (W.node n).localNode t' s'))

/-- The executions of a stable publication period. -/
inductive PublicationExec (P : Params) (c : NodeId) (t : Nat) (Q : List NodeId) : Cluster V → Cluster V → Prop where
  | refl (W : Cluster V) : PublicationExec P c t Q W W
  | step (W W' W'' : Cluster V) : PublicationExec P c t Q W W' → PublicationStep P c t Q W' W'' →
      PublicationExec P c t Q W W''

end OpenSearchProgress


