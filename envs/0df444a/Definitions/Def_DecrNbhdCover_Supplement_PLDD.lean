-- Prove2me | Definitions.Def_DecrNbhdCover_Supplement_PLDD
-- name    : DecrNbhdCover_Supplement_PLDD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:27:44.753261+00:00
-- url     : https://prove2.me/theorems/937b93d6-e27e-464c-afd5-743964f97060
-- title:
--   The $k$-PLDD problem (Definition 3.30) and $D$-covered vertices
-- statement:
--   Let $G$ be a graph, $D\ge1$ an integer and $\Pi$ a partition of $V(G)$. A vertex $v$ is **$D$-covered** by $\Pi$ if some cluster $C\in\Pi$ has $B_G(v,D)\subseteq C$.
--
--   The input of the **$k$-PLDD problem** is an $n$-vertex, $m$-edge graph $G$ with positive integer lengths under edge deletions, and integers $k,D>0$. The algorithm maintains $k$ partitions $\Pi_1,\dots,\Pi_k$ of $V(G)$. With approximation factor $\alpha$:
--
--   1. For every cluster $C\in\bigcup_i\Pi_i$, at all times, the induced subgraph $G[C]$ has diameter at most $\alpha D$: $\mathrm{dist}_{G[C]}(v,v')\le\alpha D$ for all $v,v'\in C$.
--   2. For every vertex $v$, the number of indices $i$ such that at some time $v$ was not $D$-covered by $\Pi_i$ is $O(\log n)$.
--   3. After initialization the partitions change only by **cluster splitting**: for $C\in\Pi_i$ and $C'\subseteq C$, insert $C'$ into $\Pi_i$ and delete the vertices of $C'$ from $C$; the algorithm lists all vertices of $C'$.
--   4. (Path-reporting.) A query $(C,v,v')$ with $v,v'\in C\in\bigcup_i\Pi_i$ returns a $v$-$v'$ path of length at most $\alpha D$, in $\tilde O(|E(P)|)$ time.
--
--   The item states these clauses with $\alpha=C\,k\,(\log_2(2+n+m))^C$, the bound $C\log_2(2+n)$ in clause 2, and total update time $C\,(n+m^{1+f(m)})\,k$ for a function $f$.
--
--   **Formalization Note** The partitions are reported as words. Clusters are created only in the initialization window, and afterwards only splits are legal reports. Cluster ids are never reused, and a cluster emptied by a split stays in the record. "At any time" means after each window. The query path is a walk in $G$; the page does not say it lies in $G[C]$.
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), §3.12 and Definition 3.30, pp.29–30 (PDF 33–34)

import Mathlib
import Definitions.Def_DecrNbhdCover_Supplement_Common

set_option autoImplicit false

namespace DecrNbhdCover.Supplement

open DynConnWC
open scoped ENNReal

/-! # The k-PLDD problem (Definition 3.30)

Chuzhoy, Mosenzon (STOC 2027 submission, sha256 4278ef58…), §3.12 and Definition 3.30, pp.29–30 (PDF 33–34).

"Consider a graph G, an integral parameter D ≥ 1, and a partition Π of V(G). We say that a vertex v ∈ V(G) is D-covered by the partition
Π if there is a cluster C ∈ Π with BG(v, D) ⊆ C."

**Formalization Note.** The program reports the partitions as words. In the initialization window: `0, i, id, k, v₁, …, v_k` creates
cluster `id` of partition `Π_i` with these vertices, and `1` ends the initialization. After that only cluster splitting is allowed:
`2, i, id, id′, k, v₁, …, v_k` takes the vertices `v₁, …, v_k` (all in cluster `id` of `Π_i`) out of `id` into the new cluster `id′` of `Π_i`,
listing all vertices of the new cluster. Cluster ids are never reused. That each `Π_i` is a partition of `V(G)` is a stated clause; a
cluster left empty by a split stays in the record and is harmless. "At any time" refers to the moments after each window. Operations:
`0, e` (delete edge `e`), `1, id, v, v′` (short-path query). Input words: `n, k, D`, then the edge list. -/

/-- A report on the partitions. -/
inductive PLDDReport where
  | new (i id : ℕ) (vs : List ℕ)
  | endInit
  | split (i id id' : ℕ) (vs : List ℕ)

/-- The words of a report. -/
def PLDDReport.words : PLDDReport → List ℕ
  | .new i id vs => 0 :: i :: id :: vs.length :: vs
  | .endInit => [1]
  | .split i id id' vs => 2 :: i :: id :: id' :: vs.length :: vs

/-- The partitions as reported so far: whether initialization has ended, the partition index of each cluster id, and its current
vertex set (`none` for an unused id). -/
structure PLDDState where
  started : Bool
  part : ℕ → Option ℕ
  cur : ℕ → Option (Finset ℕ)

/-- The effect of a report, for vertices below `n` and `k` partitions; `none` on an illegal report. New clusters are created only
before the end of initialization, and splits only after it. -/
def PLDDState.step (n k : ℕ) (s : PLDDState) : PLDDReport → Option PLDDState
  | .new i id vs =>
    if s.started = false ∧ s.cur id = none ∧ i < k ∧ ∀ v ∈ vs, v < n then
      some { s with part := Function.update s.part id (some i), cur := Function.update s.cur id (some vs.toFinset) }
    else none
  | .endInit => if s.started = false then some { s with started := true } else none
  | .split i id id' vs =>
    match s.cur id with
    | some c =>
      if s.started = true ∧ s.part id = some i ∧ s.cur id' = none ∧ id ≠ id' ∧ ∀ v ∈ vs, v ∈ c then
        some { s with
          part := Function.update s.part id' (some i)
          cur := Function.update (Function.update s.cur id (some (c \ vs.toFinset))) id' (some vs.toFinset) }
      else none
    | none => none

/-- `v` is `D`-covered by the partition `Π_i` of the record `s`: some cluster of `Π_i` contains `BG(v, D)`. -/
def DCovered (G : Graph ℕ ℕ) (s : PLDDState) (i v : ℕ) (D : ℝ) : Prop :=
  ∃ id c, s.part id = some i ∧ s.cur id = some c ∧ G.ball v D ⊆ (c : Set ℕ)

/-- At this moment the record holds `k` partitions of `V(G)` whose clusters have strong diameter at most `a`: for any two vertices of
a cluster `C`, `dist_{G[C]}(v, v′) ≤ a`. -/
structure PartitionsAt (G : Graph ℕ ℕ) (k : ℕ) (s : PLDDState) (a : ℝ) : Prop where
  started : s.started = true
  sub : ∀ id c, s.cur id = some c → (c : Set ℕ) ⊆ G.V
  index : ∀ id c, s.cur id = some c → ∃ i, i < k ∧ s.part id = some i
  cover : ∀ i < k, ∀ v ∈ G.V, ∃ id c, s.part id = some i ∧ s.cur id = some c ∧ v ∈ c
  disj : ∀ i id₁ id₂ c₁ c₂ v, s.part id₁ = some i → s.part id₂ = some i → s.cur id₁ = some c₁ →
    s.cur id₂ = some c₂ → v ∈ c₁ → v ∈ c₂ → id₁ = id₂
  diam : ∀ id c, s.cur id = some c → ∀ v ∈ c, ∀ v' ∈ c,
    (((G.induced (c : Set ℕ)).dist v v' : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal a

/-- An operation: an edge deletion, or a short-path query. -/
inductive PLDDOp where
  | del (e : ℕ)
  | query (id v v' : ℕ)

namespace PLDDOp

/-- The words of an operation. -/
def words : PLDDOp → List ℕ
  | .del e => [0, e]
  | .query id v v' => [1, id, v, v']

/-- The updates of `G`. -/
def gPart : PLDDOp → List GUpdate
  | .del e => [.delE e]
  | .query _ _ _ => []

/-- Whether an operation is a query. -/
def isQ : PLDDOp → Bool
  | .del _ => false
  | .query _ _ _ => true

end PLDDOp

/-- The protocol of the k-PLDD problem. -/
def plddProtocol (n k : ℕ) : Protocol PLDDOp PLDDReport PLDDState where
  opWords := PLDDOp.words
  isQuery := PLDDOp.isQ
  enc := PLDDReport.words
  step := PLDDState.step n k
  st₀ := ⟨false, fun _ => none, fun _ => none⟩

/-- The input of the k-PLDD problem. -/
structure PLDDInput where
  n : ℕ
  edges : List (ℕ × ℕ × ℕ)
  k : ℕ
  D : ℕ

namespace PLDDInput

variable (I : PLDDInput)

/-- The number of edges. -/
def m : ℕ := I.edges.length

/-- The conditions of Definition 3.30: `G` has `n ≥ 1` vertices, and `k, D` are positive integers. -/
structure Ok : Prop where
  n_pos : 1 ≤ I.n
  edges_ok : EdgesOk I.n I.edges
  k_pos : 1 ≤ I.k
  D_pos : 1 ≤ I.D

/-- The initialization words. -/
def words : List ℕ :=
  [I.n, I.k, I.D] ++ edgeWords I.edges

/-- `G` after the first `t` operations. -/
def Gt (σ : List PLDDOp) (t : ℕ) : Graph ℕ ℕ :=
  gAt (ofEdges I.n I.edges) (σ.map PLDDOp.gPart) t

/-- Valid operations: a present edge is deleted; a query names a current cluster containing both vertices. -/
def Valid (W : ℕ) (P : Program) (σ : List PLDDOp) : Prop :=
  ∀ (t : ℕ) (o : PLDDOp), σ[t]? = some o →
    match o with
    | .del e => e ∈ (I.Gt σ t).E
    | .query id v v' => ∃ s c, (plddProtocol I.n I.k).state W P I.words σ t = some s ∧
        s.cur id = some c ∧ v ∈ c ∧ v' ∈ c

/-- The indices `i < k` such that at some time `v` was not `D`-covered by `Π_i`. -/
def uncovered (W : ℕ) (P : Program) (σ : List PLDDOp) (v : ℕ) : Set ℕ :=
  {i | i < I.k ∧ ∃ t ≤ σ.length, ∃ s, (plddProtocol I.n I.k).state W P I.words σ t = some s ∧
    ¬ DCovered (I.Gt σ t) s i v (I.D : ℝ)}

end PLDDInput

/-- The approximation factor `Õ(k)`, as `C·k·log₂(2 + n + m)^C`. -/
noncomputable def plddAlpha (C n m k : ℕ) : ℝ :=
  (C : ℝ) * (k : ℝ) * Real.logb 2 (2 + (n : ℝ) + (m : ℝ)) ^ C

/-- The clauses of a path-reporting algorithm for the k-PLDD problem with approximation factor `α = C·k·log₂(2+n+m)^C`, `O(log n)`
read as `C·log₂(2 + n)`, and total update time `C·(n + m^{1+f(m)})·k`. -/
structure PLDDHolds (f : ℕ → ℝ) (C W : ℕ) (P : Program) (I : PLDDInput) (σ : List PLDDOp) : Prop where
  runs : RunsThrough W P ((plddProtocol I.n I.k).blocks I.words σ)
  /-- At all times the record holds `k` partitions of `V(G)` whose clusters have strong diameter at most `α·D`. -/
  log : ∀ t ≤ σ.length, ∃ s, (plddProtocol I.n I.k).state W P I.words σ t = some s ∧
    PartitionsAt (I.Gt σ t) I.k s (plddAlpha C I.n I.m I.k * (I.D : ℝ))
  /-- Every vertex was ever left not `D`-covered by at most `C·log₂(2 + n)` of the partitions. -/
  cover : ∀ v < I.n, ((I.uncovered W P σ v).ncard : ℝ) ≤ (C : ℝ) * lg (I.n : ℝ)
  /-- Short-path queries: a walk in `G` of length at most `α·D`. -/
  query : ∀ (t id v v' : ℕ), σ[t]? = some (.query id v v') →
    ∃ es, (plddProtocol I.n I.k).answer W P I.words σ t = some es ∧
      (I.Gt σ t).WalkFromTo v es v' ∧
      ((I.Gt σ t).walkLen es : ℝ) ≤ plddAlpha C I.n I.m I.k * (I.D : ℝ) ∧
      ((plddProtocol I.n I.k).opTime W P I.words σ t : ℝ) ≤ polylog C I.n I.m * ((es.length : ℝ) + 1)
  time : ((plddProtocol I.n I.k).updateTime W P I.words σ : ℝ) ≤
    (C : ℝ) * ((I.n : ℝ) + (I.m : ℝ) ^ (1 + f I.m)) * (I.k : ℝ)

end DecrNbhdCover.Supplement


