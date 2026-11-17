-- Prove2me | Definitions.Def_ForgetAlt_Supplement_Congest
-- name    : ForgetAlt_Supplement_Congest
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:16:40.712618+00:00
-- url     : https://prove2.me/theorems/63cabb42-adc0-497d-ba9f-2479c1f4a612
-- title:
--   Randomized CONGEST algorithms for approximate maximum matching
-- statement:
--   In the **CONGEST model** a simple connected graph $G$ with $n$ vertices is the communication network. Vertices carry distinct integer identifiers of $O(\log n)$ bits. Computation proceeds in synchronous rounds: in each round every vertex sends a (possibly different) message of $O(\log n)$ bits to each neighbour, receives all messages sent to it in that round, and updates its state by unbounded local computation from its state, its private random bits and the received messages. All vertices know $n$, or a common polynomial upper bound $N$ on $n$.
--
--   A **randomized CONGEST algorithm** consists of
--
--   1. a local state space and a bandwidth constant $c$ (every delivered message has at most $c\,(\lfloor\log_2 n\rfloor+1)$ bits; longer messages are truncated);
--   2. a round budget $R(N,\varepsilon)$ that depends only on the global knowledge $(N,\varepsilon)$, where $N$ is $n$ or the known upper bound on it;
--   3. an initial state computed from $N$, $\varepsilon$, the vertex's identifier, the identifiers of its neighbours and its private infinite sequence of fair coins;
--   4. a message function (state, neighbour identifier) $\mapsto$ bit string, and a state update from the messages received in the round, each labelled by its sender's identifier;
--   5. a final report: the identifier of the vertex's partner, or none.
--
--   The run **succeeds** if after $R(N,\varepsilon)$ rounds the reports are consistent ($u$ reports $v$ exactly when $v$ reports $u$, and every report names a vertex) and the reported pairs form a matching $M$ of $G$ with
--   $$|M|\ \ge\ (1-\varepsilon)\,\mu(G).$$
--   The coin sequences of all vertices are independent fair coins.
--
--   This is the distributed model of the first part of Theorem 1.3.
--
--   **Formalization Note** Vertices are `Fin n`; the coins form one tape `Fin n × ℕ → Bool` under the infinite product of fair coins (`Measure.infinitePi`). Edges are identified by their endpoints' identifiers. Matchings and $\mu(G)$ are those of the published `LoadBalMatch_Main_Matching`.
-- source:
--   Izumi–Kitamura–Yamaguchi, Forgetting Alternation and Blossoms, STOC 2027 submission (manuscript sha256 b656488c…), Section 3.7, “CONGEST model”, printed p.34 (PDF p.35); Theorem 1.3, printed p.51 (PDF p.52)

import Mathlib
import Definitions.Def_LoadBalMatch_Main_Matching

namespace ForgetAlt.Supplement

/-!
# Randomized CONGEST algorithms for approximate maximum matching

Izumi–Kitamura–Yamaguchi, *Forgetting Alternation and Blossoms*, STOC 2027 submission
(manuscript sha256 b656488c…), Section 3.7, "CONGEST model", printed p.34 (PDF p.35): "The system
is modeled by a simple connected undirected graph G of n vertices and m edges. Vertices and edges
are uniquely identified by O(log n)-bit integer values, and the computation follows round-based
synchronous message passing. In one round, each vertex v sends and receives O(log n)-bit messages
through each of its incident edges, and executes local computation following its internal state,
local random bits, and all the received messages. A vertex can send different messages to
different neighbors in one round … We assume that all vertices know n, or a common polynomial
upper bound on n".

**Formalization Notes.**
* A `CongestAlg` is one program run by every vertex, with an arbitrary local state type (local
  computation is unbounded). A vertex starts from the global knowledge `(N, ε)`, where `N` is the
  number `n` of vertices or a common upper bound on it (the run functions take `N` as an
  argument; the theorems say which `N` are allowed), its own
  identifier, the set of its neighbours' identifiers (KT1; a KT0 vertex learns them in one round,
  so this changes the round count by at most one) and its private infinite fair-coin tape.
* In each round every vertex computes, from its state, one message for each neighbour (addressed by
  the neighbour's identifier); the message is a bit string, of which only the first
  `bandwidth · (⌊log₂ n⌋ + 1)` bits are delivered (the `O(log n)`-bit bandwidth, `bandwidth` a
  constant of the algorithm). Every vertex then updates its state from the messages received in
  that round, labelled by the sender's identifier (the empty string from non-neighbours).
* The number of rounds `rounds N ε` depends only on the knowledge. The bandwidth is measured
  in the true `n`. After it each vertex outputs its
  partner's identifier or `none`.
* Edges are identified by the identifier pairs of their endpoints.
* The randomness is the family of tapes `Fin n × ℕ → Bool` with the product of fair coins.
* `Succeeds`: the reports are consistent (`u` reports `v` iff `v` reports `u`, and every report
  names a vertex), and the reported pairs form a matching of `G` with at least `(1 − ε)·µ(G)` edges
  (`IsMatchingIn`, `matchingNumber` of the published `LoadBalMatch_Main_Matching`).
-/

open LoadBalMatch.Main

/-- A randomized CONGEST algorithm. -/
structure CongestAlg where
  /-- The local state of a vertex. -/
  State : Type
  /-- The bandwidth constant: messages carry at most `bandwidth · (⌊log₂ n⌋ + 1)` bits. -/
  bandwidth : ℕ
  /-- The round budget, from the global knowledge `(N, ε)`. -/
  rounds : ℕ → ℝ → ℕ
  /-- The initial state from the known `N`, `ε`, the own identifier, the neighbours' identifiers and the
  private coin tape. -/
  init : ℕ → ℝ → ℕ → Finset ℕ → (ℕ → Bool) → State
  /-- The message sent to the neighbour with the given identifier. -/
  send : State → ℕ → List Bool
  /-- The state update from the messages received, indexed by the sender's identifier. -/
  recv : State → (ℕ → List Bool) → State
  /-- The final report: the partner's identifier, or `none`. -/
  output : State → Option ℕ

namespace CongestAlg

variable (A : CongestAlg) {n : ℕ} (G : SimpleGraph (Fin n)) (ident : Fin n → ℕ) (ε : ℝ)

/-- The number of bits a message may carry on `n`-vertex graphs. -/
def msgBits (n : ℕ) : ℕ := A.bandwidth * (Nat.log 2 n + 1)

/-- The identifiers of the neighbours of `v`. -/
noncomputable def nbrIds (v : Fin n) : Finset ℕ := by
  classical
  exact (Finset.univ.filter (fun u => G.Adj v u)).image ident

/-- The initial configuration on the coin tapes `ω`, every vertex knowing the value `N` (the
number of vertices, or a common upper bound on it) and `ε`. -/
noncomputable def initConfig (N : ℕ) (ω : Fin n × ℕ → Bool) : Fin n → A.State :=
  fun v => A.init N ε (ident v) (nbrIds G ident v) (fun i => ω (v, i))

/-- The messages received by `v` in a round from the configuration `st`: from the neighbour with
identifier `j`, the first `msgBits n` bits of what it sends to `v`; the empty string otherwise. -/
noncomputable def received (st : Fin n → A.State) (v : Fin n) : ℕ → List Bool := by
  classical
  exact fun j => if h : ∃ u, G.Adj v u ∧ ident u = j then
    (A.send (st h.choose) (ident v)).take (A.msgBits n) else []

/-- One synchronous round. -/
noncomputable def round (st : Fin n → A.State) : Fin n → A.State :=
  fun v => A.recv (st v) (A.received G ident st v)

/-- The reports after `rounds N ε` rounds on the coin tapes `ω`, `N` the known value. -/
noncomputable def reports (N : ℕ) (ω : Fin n × ℕ → Bool) : Fin n → Option ℕ :=
  fun v => A.output ((A.round G ident)^[A.rounds N ε] (A.initConfig G ident ε N ω) v)

/-- The set of reported pairs `{u, v}` with `u` reporting `v`. -/
noncomputable def reportedPairs (out : Fin n → Option ℕ) : Finset (Sym2 (Fin n)) := by
  classical
  exact Finset.univ.filter (fun e => ∃ u v, e = s(u, v) ∧ out u = some (ident v))

/-- The reports form a `(1 − ε)`-approximate maximum matching of `G`. -/
def IsApproxMatchingReport (out : Fin n → Option ℕ) : Prop :=
  (∀ u j, out u = some j → ∃ v, ident v = j) ∧
    (∀ u v, out u = some (ident v) → out v = some (ident u)) ∧
    IsMatchingIn G (reportedPairs ident out) ∧
    (1 - ε) * (matchingNumber G : ℝ) ≤ ((reportedPairs ident out).card : ℝ)

/-- The run on the coin tapes `ω`, every vertex knowing `N`, succeeds. -/
def Succeeds (N : ℕ) (ω : Fin n × ℕ → Bool) : Prop :=
  IsApproxMatchingReport G ident ε (A.reports G ident ε N ω)

end CongestAlg

/-- The law of the coin tapes of `n` vertices: independent fair coins. -/
noncomputable def tapeMeasure (n : ℕ) : MeasureTheory.Measure (Fin n × ℕ → Bool) :=
  MeasureTheory.Measure.infinitePi (fun _ : Fin n × ℕ => (PMF.uniformOfFintype Bool).toMeasure)

end ForgetAlt.Supplement


