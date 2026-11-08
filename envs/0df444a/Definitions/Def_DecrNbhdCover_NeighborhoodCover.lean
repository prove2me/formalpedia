-- Prove2me | Definitions.Def_DecrNbhdCover_NeighborhoodCover
-- name    : DecrNbhdCover_NeighborhoodCover
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:03:10.782199+00:00
-- url     : https://prove2.me/theorems/51f843dc-50af-4f19-93d6-c7e7b7e93abf
-- title:
--   The report log of a neighborhood cover, the clauses of Theorem 3.29, and the MaintainNC problem (Definition 3.18)
-- statement:
--   A collection of clusters is reported as words: a new cluster with the list of its vertices, a vertex deletion from a cluster, and a change of $\mathrm{CoveringCluster}(v)$. An id is never reused, so the clusters that $v$ ever belongs to are counted by ids.
--
--   Theorem 3.29's clauses concern a graph with $n$ vertices and $m$ edges, $0<\epsilon<1$, $D>0$: a sparsity bound over the run, the bound on $\mathrm{dist}_G$ inside clusters, $B_G(v,D)\subseteq\mathrm{CoveringCluster}(v)$ at all times, short-path queries, and the total update time.
--
--   In the **strong MaintainNC problem** the input has integers $n,\mu>0$, a decremental graph $G$ with at most $n$ vertices and maximum degree at most $\mu$, $0<\epsilon<1/400$ and $16\cdot2^{1/\epsilon^{4c}}<D\le2^{1/\epsilon^{16c}}n\log n$. The goal is a collection of clusters of $G$ such that every vertex ever belongs to at most $\max\{n^\epsilon,4\log n\}$ clusters, with $B_G(v,D)\subseteq\mathrm{CoveringCluster}(v)$ at all times, updated only by vertex deletions and new clusters, all reported, and short-path queries $(C,v,v')$ answered by a $v$-$v'$ path in $G$ of length at most $\alpha D$, in time $\tilde O(|E(P)|)$. The **weak problem** has any $D>0$, an integer $0<d\le D$, and a partial $(\epsilon,d,D)$-emulator $H$ for $G$ with dynamic degree bound $\mu$, and answers by a path in $H$ with no consecutively repeated regular vertices.
--
--   **Formalization Note** At $n=1$, $n\log n=0$ makes the range of $D$ empty in the strong problem: the source's own corner.
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), Theorem 3.29, p.29 (PDF 33); Definition 3.18, pp.22–23 (PDF 26–27); §1, pp.2–5

import Mathlib
import Definitions.Def_DecrNbhdCover_Emulator
import Definitions.Def_DecrNbhdCover_Streams
import Definitions.Def_DecrNbhdCover_Session

set_option autoImplicit false

namespace DecrNbhdCover

open DynConnWC
open scoped ENNReal

/-! # Neighborhood covers: the report log, Theorem 3.29, and the MaintainNC problem (Definition 3.18)

Chuzhoy, Mosenzon (STOC 2027 submission, sha256 4278ef58…), Theorem 3.29, p.29; Definition 3.18, pp.22–23.

**Formalization Note.** The program reports the collection of clusters as words: `0, id, k, v₁, …, v_k` (a new cluster with this list of vertices),
`1, id, v` (vertex `v` is deleted from cluster `id`), `2, v, id` (now `CoveringCluster(v) = id`). So the collection changes only by the two updates the paper allows,
and each is reported as it happens: a pointer change is a write, so reporting it costs what maintaining it costs. `ClusterState.step` refuses an id used before, a vertex
out of range, a deletion of a non-member and a pointer to no cluster, so an id is never reused and "clusters that `v` ever belongs to" counts ids. Queries are `1, id, v, v′`, answered
with `k, e₁, …, e_k`. Updates are `0, e` (edge deletion) and `2, v` (vertex deletion). `ε` and `D` are rationals given by numerator and denominator; paths may be non-simple.
`NCHolds` gathers the clauses common to Theorem 3.29 and Definition 3.18. -/

/-- A report on the collection of clusters. -/
inductive ClusterReport where
  | new (id : ℕ) (vs : List ℕ)
  | del (id v : ℕ)
  | cover (v id : ℕ)

/-- The words of a report. -/
def ClusterReport.words : ClusterReport → List ℕ
  | .new id vs => 0 :: id :: vs.length :: vs
  | .del id v => [1, id, v]
  | .cover v id => [2, v, id]

/-- The collection of clusters as reported so far. `init id` is the vertex set a cluster was created with (`none` if the id is unused), `cur id` is its current vertex set, and `ptr v`
the current `CoveringCluster(v)`. -/
structure ClusterState where
  init : ℕ → Option (Finset ℕ)
  cur : ℕ → Option (Finset ℕ)
  ptr : ℕ → Option ℕ

namespace ClusterState

/-- No clusters and no pointers. -/
def empty : ClusterState := ⟨fun _ => none, fun _ => none, fun _ => none⟩

/-- The effect of a report, for vertices below `n`; `none` on an illegal report. -/
def step (n : ℕ) (s : ClusterState) : ClusterReport → Option ClusterState
  | .new id vs =>
    if s.init id = none ∧ ∀ v ∈ vs, v < n then
      some { s with
        init := Function.update s.init id (some vs.toFinset)
        cur := Function.update s.cur id (some vs.toFinset) }
    else none
  | .del id v =>
    match s.cur id with
    | some c => if v ∈ c then some { s with cur := Function.update s.cur id (some (c.erase v)) } else none
    | none => none
  | .cover v id =>
    if (s.cur id).isSome ∧ v < n then some { s with ptr := Function.update s.ptr v (some id) } else none

/-- The number of clusters that `v` ever belongs to. -/
noncomputable def everCount (s : ClusterState) (v : ℕ) : ℕ :=
  {id | ∃ c, s.init id = some c ∧ v ∈ c}.ncard

/-- At this moment the clusters are clusters of `G`, and for every vertex `v` of `G`, the reported `CoveringCluster(v)` is a current cluster containing `BG(v, D)`. -/
def Covers (s : ClusterState) (G : Graph ℕ ℕ) (D : ℝ) : Prop :=
  (∀ id c, s.cur id = some c → (c : Set ℕ) ⊆ G.V) ∧
    ∀ v ∈ G.V, ∃ id c, s.ptr v = some id ∧ s.cur id = some c ∧ G.ball v D ⊆ (c : Set ℕ)

end ClusterState

/-- An operation on a decremental graph: an update or a short-path query. -/
inductive GOp where
  | upd (u : GUpdate)
  | query (id v v' : ℕ)

/-- The words of an operation. -/
def GOp.words : GOp → List ℕ
  | .upd (.delE e) => [0, e]
  | .upd (.delV v) => [2, v]
  | .query id v v' => [1, id, v, v']

/-- The update part of an operation, as a list. -/
def GOp.gPart : GOp → List GUpdate
  | .upd u => [u]
  | .query _ _ _ => []

/-- Whether an operation is a query. -/
def GOp.isQ : GOp → Bool
  | .upd _ => false
  | .query _ _ _ => true

/-- The protocol of Theorem 3.29 and of strong MaintainNC, for vertices below `n`. -/
def gProtocol (n : ℕ) : Protocol GOp ClusterReport ClusterState where
  opWords := GOp.words
  isQuery := GOp.isQ
  enc := ClusterReport.words
  step := ClusterState.step n
  st₀ := ClusterState.empty

/-- The clusters of the run at time `t` obey the covering clause and the path answers obey `qOk`, the sparsity bound `spars` holds, query windows take at most `polylog` per edge, and the total update
time is at most `timeB`. Here `Gt t` is the graph after `t` operations, `queryOf` recognizes queries, and `qOk t v v′ es` is what the answer `es` must satisfy. -/
structure NCHolds {Op : Type} (π : Protocol Op ClusterReport ClusterState) (W : ℕ) (P : Program) (init : List ℕ)
    (σ : List Op) (n₀ : ℕ) (Gt : ℕ → Graph ℕ ℕ) (D spars : ℝ) (queryOf : Op → Option (ℕ × ℕ × ℕ))
    (qOk : ℕ → ℕ → ℕ → List ℕ → Prop) (qBound : ℝ) (timeB : ℝ) : Prop where
  /-- The run reaches the end marker. -/
  runs : RunsThrough W P (π.blocks init σ)
  /-- At every time, the log parses, the covering clause holds, and every vertex below `n₀` has been in at most `spars` clusters. -/
  log : ∀ t ≤ σ.length, ∃ s, π.state W P init σ t = some s ∧ s.Covers (Gt t) D ∧
    ∀ v < n₀, (s.everCount v : ℝ) ≤ spars
  /-- Short-path queries. -/
  query : ∀ (t : ℕ) (o : Op) (id v v' : ℕ), σ[t]? = some o → queryOf o = some (id, v, v') →
    ∃ es, π.answer W P init σ t = some es ∧ qOk t v v' es ∧
      (π.opTime W P init σ t : ℝ) ≤ qBound * ((es.length : ℝ) + 1)
  /-- The total update time. -/
  time : (π.updateTime W P init σ : ℝ) ≤ timeB

/-- `v` and `v′` are currently in cluster `id`. -/
def ClusterState.InCluster (s : ClusterState) (id v v' : ℕ) : Prop :=
  ∃ c, s.cur id = some c ∧ v ∈ c ∧ v' ∈ c

/-! ## Theorem 3.29 -/

/-- The input of Theorem 3.29: the graph on `n` vertices with its edge list, `ϵ`, and `D`. -/
structure GoalInput where
  n : ℕ
  edges : List (ℕ × ℕ × ℕ)
  eps : ℚ
  D : ℚ

namespace GoalInput

variable (I : GoalInput)

/-- `n ≥ 1`, the edge list is valid, `0 < ϵ < 1` and `D > 0`. -/
structure Ok : Prop where
  n_pos : 1 ≤ I.n
  edges_ok : EdgesOk I.n I.edges
  eps_pos : 0 < I.eps
  eps_lt : I.eps < 1
  D_pos : 0 < I.D

/-- The initialization words `n, m, (u_e, v_e, ℓ_e)_e, ϵ-num, ϵ-den, D-num, D-den`. -/
def words : List ℕ :=
  I.n :: edgeWords I.edges ++ ratWords I.eps ++ ratWords I.D

/-- The initial graph. -/
def G₀ : Graph ℕ ℕ := ofEdges I.n I.edges

/-- The number of edges. -/
def m : ℕ := I.edges.length

/-- The largest edge length. -/
def L : ℕ := maxWord (I.edges.map (fun t => t.2.2))

/-- `⌈log₂(2 + n + m + L + the four numerators and denominators of ϵ and D)⌉`. -/
def logSize : ℕ :=
  Nat.clog 2 (2 + I.n + I.m + I.L + I.eps.num.toNat + I.eps.den + I.D.num.toNat + I.D.den)

/-- The graph after the first `t` operations. -/
def Gt (σ : List GOp) (t : ℕ) : Graph ℕ ℕ :=
  gAt I.G₀ (σ.map GOp.gPart) t

/-- The operation sequence is valid: each one is an edge deletion of an edge present, or a query on a current cluster containing both vertices, as the run has reported so far. -/
def Valid (W : ℕ) (P : Program) (σ : List GOp) : Prop :=
  ∀ (t : ℕ) (o : GOp), σ[t]? = some o →
    match o with
    | .upd (.delE e) => e ∈ (I.Gt σ t).E
    | .upd (.delV _) => False
    | .query id v v' => ∃ s, (gProtocol I.n).state W P I.words σ t = some s ∧ s.InCluster id v v'

end GoalInput

/-- The six clauses of Theorem 3.29 (see the theorem's Formalization Note), for a run of `P` on `I` and `σ`, with universal constant `C`. -/
structure GoalHolds (C W : ℕ) (P : Program) (I : GoalInput) (σ : List GOp) : Prop where
  /-- The covering clause, the sparsity clause, the path answers and the total update time. -/
  nc : NCHolds (gProtocol I.n) W P I.words σ I.n (I.Gt σ) (I.D : ℝ)
    (min ((I.n : ℝ) ^ ((C : ℝ) * (I.eps : ℝ))) (((max 1 I.m : ℕ) : ℝ) ^ ((C : ℝ) * (I.eps : ℝ))) *
      expEps C (I.eps : ℝ))
    (fun o => match o with
      | .query id v v' => some (id, v, v')
      | .upd _ => none)
    (fun t v v' es => (I.Gt σ t).WalkFromTo v es v' ∧
      ((I.Gt σ t).walkLen es : ℝ) ≤ expEps C (I.eps : ℝ) * (I.D : ℝ))
    (polylog C I.n I.m)
    ((C : ℝ) * ((I.n : ℝ) + (I.m : ℝ) ^ (1 + (C : ℝ) * (I.eps : ℝ)) * expEps C (I.eps : ℝ)))
  /-- The diameter clause: at all times, any two vertices of a current cluster are at distance at most `2^{C/ϵ^C}·D` in the current graph. -/
  diam : ∀ t ≤ σ.length, ∀ s, (gProtocol I.n).state W P I.words σ t = some s →
    ∀ id c, s.cur id = some c → ∀ v ∈ c, ∀ v' ∈ c,
      (((I.Gt σ t).dist v v' : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal (expEps C (I.eps : ℝ) * (I.D : ℝ))

/-! ## Definition 3.18: MaintainNC -/

/-- The input of the strong MaintainNC problem. `N₀` is the initial number of vertices, at most `n`. -/
structure StrongNCInput where
  n : ℕ
  mu : ℕ
  N₀ : ℕ
  edges : List (ℕ × ℕ × ℕ)
  eps : ℚ
  D : ℚ

namespace StrongNCInput

variable (I : StrongNCInput)

/-- The conditions of Definition 3.18 for the strong problem, for the constant `c`. -/
structure Ok (c : ℕ) : Prop where
  n_pos : 0 < I.n
  mu_pos : 0 < I.mu
  N_pos : 1 ≤ I.N₀
  N_le : I.N₀ ≤ I.n
  edges_ok : EdgesOk I.N₀ I.edges
  deg : (ofEdges I.N₀ I.edges).DegLe I.mu
  eps_pos : 0 < I.eps
  eps_lt : I.eps < 1 / 400
  D_gt : 16 * (2 : ℝ) ^ (1 / (I.eps : ℝ) ^ (4 * c)) < (I.D : ℝ)
  D_le : (I.D : ℝ) ≤ (2 : ℝ) ^ (1 / (I.eps : ℝ) ^ (16 * c)) * ((I.n : ℝ) * Real.logb 2 (I.n : ℝ))

/-- The initialization words. -/
def words : List ℕ :=
  [I.n, I.mu, I.N₀] ++ edgeWords I.edges ++ ratWords I.eps ++ ratWords I.D

/-- The graph after the first `t` operations. -/
def Gt (σ : List GOp) (t : ℕ) : Graph ℕ ℕ :=
  gAt (ofEdges I.N₀ I.edges) (σ.map GOp.gPart) t

/-- Valid operations: a present edge or vertex is deleted; a query names a current cluster containing both vertices. -/
def Valid (W : ℕ) (P : Program) (σ : List GOp) : Prop :=
  ∀ (t : ℕ) (o : GOp), σ[t]? = some o →
    match o with
    | .upd u => u.Ok (I.Gt σ t)
    | .query id v v' => ∃ s, (gProtocol I.N₀).state W P I.words σ t = some s ∧ s.InCluster id v v'

end StrongNCInput

/-- The bound `max{n^ϵ, 4 log n}` of Definition 3.18. -/
noncomputable def ncSparsity (n : ℕ) (eps : ℝ) : ℝ :=
  max ((n : ℝ) ^ eps) (4 * Real.logb 2 (n : ℝ))

/-- The clauses of the strong MaintainNC problem, with approximation factor `2^{C/ϵ^C}`, and the time bound of Theorem 3.28. -/
def StrongNCHolds (C W : ℕ) (P : Program) (I : StrongNCInput) (σ : List GOp) : Prop :=
  NCHolds (gProtocol I.N₀) W P I.words σ I.N₀ (I.Gt σ) (I.D : ℝ)
    (ncSparsity I.n (I.eps : ℝ))
    (fun o => match o with
      | .query id v v' => some (id, v, v')
      | .upd _ => none)
    (fun t v v' es => (I.Gt σ t).WalkFromTo v es v' ∧
      ((I.Gt σ t).walkLen es : ℝ) ≤ expEps C (I.eps : ℝ) * (I.D : ℝ))
    (polylog C I.N₀ I.edges.length)
    ((C : ℝ) * (I.n : ℝ) ^ (1 + (C : ℝ) * Real.sqrt (I.eps : ℝ)) * (I.mu : ℝ) ^ C * expEps C (I.eps : ℝ))

/-- An operation of the weak problems: a step of updates to `G` and `H`, or a query. -/
inductive WeakOp where
  | batch (gs : List GUpdate) (hs : List HUpdate)
  | query (id v v' : ℕ)

/-- The words of an operation. -/
def WeakOp.words : WeakOp → List ℕ
  | .batch gs hs => 0 :: batchWords gs hs
  | .query id v v' => [1, id, v, v']

/-- The updates of `G`. -/
def WeakOp.gPart : WeakOp → List GUpdate
  | .batch gs _ => gs
  | .query _ _ _ => []

/-- The updates of `H`. -/
def WeakOp.hPart : WeakOp → List HUpdate
  | .batch _ hs => hs
  | .query _ _ _ => []

/-- Whether an operation is a query. -/
def WeakOp.isQ : WeakOp → Bool
  | .batch _ _ => false
  | .query _ _ _ => true

/-- The protocol of weak MaintainNC, for vertices below `n`. -/
def weakProtocol (n : ℕ) : Protocol WeakOp ClusterReport ClusterState where
  opWords := WeakOp.words
  isQuery := WeakOp.isQ
  enc := ClusterReport.words
  step := ClusterState.step n
  st₀ := ClusterState.empty

/-- The input of the weak MaintainNC problem. -/
structure WeakNCInput where
  n : ℕ
  mu : ℕ
  N₀ : ℕ
  edges : List (ℕ × ℕ × ℕ)
  h₀ : List (List (ℕ × ℕ))
  eps : ℚ
  d : ℕ
  D : ℚ

namespace WeakNCInput

variable (I : WeakNCInput)

/-- The conditions of Definition 3.18 for the weak problem that do not concern the update stream. -/
structure Ok : Prop where
  n_pos : 0 < I.n
  mu_pos : 0 < I.mu
  N_pos : 1 ≤ I.N₀
  N_le : I.N₀ ≤ I.n
  edges_ok : EdgesOk I.N₀ I.edges
  deg : (ofEdges I.N₀ I.edges).DegLe I.mu
  h_ok : hInitOk I.N₀ I.h₀
  eps_pos : 0 < I.eps
  eps_lt : I.eps < 1 / 400
  d_pos : 0 < I.d
  d_le : (I.d : ℚ) ≤ I.D

/-- The initialization words. -/
def words : List ℕ :=
  [I.n, I.mu, I.N₀, I.d] ++ edgeWords I.edges ++ hInitWords I.h₀ ++ ratWords I.eps ++ ratWords I.D

/-- `G` after the first `t` operations. -/
def Gt (σ : List WeakOp) (t : ℕ) : Graph ℕ ℕ :=
  gAt (ofEdges I.N₀ I.edges) (σ.map WeakOp.gPart) t

/-- `H` after the first `t` operations. -/
noncomputable def Ht (σ : List WeakOp) (t : ℕ) : HState :=
  hAt (hInit I.N₀ I.h₀) (σ.map WeakOp.hPart) t

/-- The promise on the input stream: each step is nonempty and has at most one update of `G`, all updates are valid, `H` is a partial `(ϵ, d, D)`-emulator for `G` at all times, with dynamic degree bound `μ`. -/
structure Promise (σ : List WeakOp) : Prop where
  steps : ∀ (t : ℕ) (gs : List GUpdate) (hs : List HUpdate), σ[t]? = some (.batch gs hs) →
    gs.length ≤ 1 ∧ (gs ≠ [] ∨ hs ≠ []) ∧ gsOk (I.Gt σ t) gs ∧ hsOk (I.Ht σ t) hs
  partial' : ∀ t ≤ σ.length, IsPartial (I.Gt σ t) (I.Ht σ t).g (I.eps : ℝ) I.d (I.D : ℝ)
  deg : (I.Ht σ σ.length).EverDegLe I.mu

/-- A query names a current cluster containing both vertices. -/
def QueriesOk (W : ℕ) (P : Program) (σ : List WeakOp) : Prop :=
  ∀ (t : ℕ) (id v v' : ℕ), σ[t]? = some (.query id v v') →
    ∃ s, (weakProtocol I.N₀).state W P I.words σ t = some s ∧ s.InCluster id v v'

end WeakNCInput

/-- The clauses of the weak MaintainNC problem, with approximation factor `2^{C/ϵ^C}`, and the time bound of Theorem 3.19. -/
def WeakNCHolds (C W : ℕ) (P : Program) (I : WeakNCInput) (σ : List WeakOp) : Prop :=
  NCHolds (weakProtocol I.N₀) W P I.words σ I.N₀ (I.Gt σ) (I.D : ℝ)
    (ncSparsity I.n (I.eps : ℝ))
    (fun o => match o with
      | .query id v v' => some (id, v, v')
      | .batch _ _ => none)
    (fun t v v' es => (I.Ht σ t).g.NoRepeatPath v es v' ∧
      ((I.Ht σ t).g.walkLen es : ℝ) ≤ expEps C (I.eps : ℝ) * (I.D : ℝ))
    (polylog C I.N₀ I.edges.length)
    ((C : ℝ) * (I.N₀ : ℝ) * (I.n : ℝ) ^ ((C : ℝ) * Real.sqrt (I.eps : ℝ)) *
      ((I.D : ℝ) * (I.mu : ℝ) / (I.d : ℝ)) ^ C * expEps C (I.eps : ℝ))

end DecrNbhdCover


