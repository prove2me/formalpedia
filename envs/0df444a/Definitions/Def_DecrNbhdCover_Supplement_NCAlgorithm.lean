-- Prove2me | Definitions.Def_DecrNbhdCover_Supplement_NCAlgorithm
-- name    : DecrNbhdCover_Supplement_NCAlgorithm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:29:23.319992+00:00
-- url     : https://prove2.me/theorems/7ca4af07-bfef-4f13-923d-000945731598
-- title:
--   $(\alpha,s,T)$-neighborhood-cover algorithms (Definition 9.1)
-- statement:
--   Let $\alpha,s,T:\mathbb N\to\mathbb N$. An **$(\alpha,s,T)$-neighborhood-cover algorithm** is a deterministic algorithm whose input is a graph $G$ with positive integer lengths that initially has $n$ vertices and $m\ge1$ edges, under an online sequence of edge deletions, and a distance parameter $D>0$. It has the following properties.
--
--   1. At initialization it reports the values $\alpha(m)$ and $s(m)$.
--   2. It maintains a collection $\mathcal C$ of clusters of $G$ such that every vertex ever belongs to at most $s(m)$ clusters, and at all times every vertex $v$ has a reported cluster $\mathrm{CoveringCluster}(v)\in\mathcal C$ with $B_G(v,D)\subseteq\mathrm{CoveringCluster}(v)$.
--   3. After initialization, $\mathcal C$ changes only by insertion of a new cluster (all its vertices are reported), deletion of a vertex from a cluster, and insertion of a vertex into a cluster that never contained it. Every update is reported.
--   4. A short-path query $(C,u,v)$ with distinct $u,v\in C\in\mathcal C$ returns a (possibly non-simple) $u$-$v$ path $P$ in $G$ of length at most $\alpha(m)\cdot D$, in at most $C_A(\log_2(2+n+m))^{C_A}(|E(P)|+1)$ steps.
--   5. The total update time is at most $C_A\,(n+m\cdot T(m))$.
--
--   The constant $C_A$ of clauses 4 and 5 belongs to the algorithm. This is the interface that the reduction of Theorems 9.2 and 9.3 uses as a black box.
--
--   **Formalization Note** The algorithm is a program of the word RAM of the mission with no `rand` instruction, required to work at every word size $W\ge C_A\lceil\log_2(2+\text{largest input word}+\alpha(m)+s(m)+T(m))\rceil$. $D$ is a rational. Cluster ids are never reused, and the record keeps for each cluster the set of vertices it ever contained. Monotonicity of $\alpha,s,T$ is a hypothesis of the theorems, not of this definition. There is no diameter clause other than through the query, as on the page.
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), Definition 9.1, p.67 (PDF 71)

import Mathlib
import Definitions.Def_DecrNbhdCover_Supplement_Common

set_option autoImplicit false

namespace DecrNbhdCover.Supplement

open DynConnWC
open scoped ENNReal

/-! # Neighborhood-cover algorithms (Definition 9.1)

Chuzhoy, Mosenzon (STOC 2027 submission, sha256 4278ef58…), Definition 9.1, p.67 (PDF 71).

"Let α, s, T : N → N be nondecreasing functions. An (α, s, T)-neighborhood-cover algorithm is a deterministic algorithm, whose input is a
graph G with positive integral edge lengths that initially has n vertices and m ≥ 1 edges, and undergoes an online sequence of edge
deletions, together with a distance parameter D > 0. At initialization, the algorithm reports the values α(m) and s(m). It then maintains a
collection C of clusters of G with the following properties: for every vertex v ∈ V(G), the total number of clusters of C that v ever
belongs to is at most s(m); and for every vertex v ∈ V(G), at all times there is a cluster CoveringCluster(v) ∈ C with BG(v, D) ⊆
CoveringCluster(v); the algorithm explicitly maintains, for every vertex v ∈ V(G), a pointer to such a cluster. Once the collection C is
initialized, it may only undergo the following updates: insertion of a new cluster; deletion of a vertex from a cluster; and insertion of a
vertex v into a cluster that never contained v. The algorithm explicitly reports every such update; when a new cluster is inserted into C,
it reports all its vertices. The algorithm must support short-path queries: given a cluster C ∈ C and a pair u, v ∈ C of distinct vertices,
return a (possibly non-simple) u-v path P in G of length at most α(m) · D, in time Õ(|E(P)|). The total update time of the algorithm must be
O(n + m · T(m))."

**Formalization Note.** A program on the word RAM of the mission, without `rand`, at unit cost per instruction. Input words: `n`, the edge
list, `D` as a rational. Reports: `0, a, b` (the values `α(m) = a`, `s(m) = b`, once); `1, id, k, v₁, …, v_k` (new cluster); `2, id, v`
(delete `v` from cluster `id`); `3, id, v` (insert `v` into cluster `id`, which never contained it); `4, v, id` (now
`CoveringCluster(v) = id`). Cluster ids are never reused, and the record keeps for each cluster the set of vertices it ever contained, so
"clusters that `v` ever belongs to" counts ids. Operations: `0, e` (delete edge `e`) and `1, id, u, v` (short-path query, answered with
`k, e₁, …, e_k`). The constants hidden in `Õ(|E(P)|)` and `O(n + m·T(m))` are one constant `C_A` of the algorithm, which also bounds the word
size it needs: `C_A·⌈log₂(2 + largest input word + α(m) + s(m) + T(m))⌉`. -/

/-- A report of a neighborhood-cover algorithm. -/
inductive NCAReport where
  | params (a b : ℕ)
  | new (id : ℕ) (vs : List ℕ)
  | del (id v : ℕ)
  | ins (id v : ℕ)
  | cover (v id : ℕ)

/-- The words of a report. -/
def NCAReport.words : NCAReport → List ℕ
  | .params a b => [0, a, b]
  | .new id vs => 1 :: id :: vs.length :: vs
  | .del id v => [2, id, v]
  | .ins id v => [3, id, v]
  | .cover v id => [4, v, id]

/-- The collection as reported so far: the reported values `α(m), s(m)`, the vertices each cluster ever contained (`none` for an unused
id), its current vertices, and the pointers `CoveringCluster(v)`. -/
structure NCAState where
  params : Option (ℕ × ℕ)
  ever : ℕ → Option (Finset ℕ)
  cur : ℕ → Option (Finset ℕ)
  ptr : ℕ → Option ℕ

namespace NCAState

/-- The effect of a report, for vertices below `n`; `none` on an illegal report. -/
def step (n : ℕ) (s : NCAState) : NCAReport → Option NCAState
  | .params a b => if s.params = none then some { s with params := some (a, b) } else none
  | .new id vs =>
    if s.ever id = none ∧ ∀ v ∈ vs, v < n then
      some { s with ever := Function.update s.ever id (some vs.toFinset),
                    cur := Function.update s.cur id (some vs.toFinset) }
    else none
  | .del id v =>
    match s.cur id with
    | some c => if v ∈ c then some { s with cur := Function.update s.cur id (some (c.erase v)) } else none
    | none => none
  | .ins id v =>
    match s.cur id, s.ever id with
    | some c, some e =>
      if v ∉ e ∧ v < n then
        some { s with cur := Function.update s.cur id (some (insert v c)),
                      ever := Function.update s.ever id (some (insert v e)) }
      else none
    | _, _ => none
  | .cover v id =>
    if (s.cur id).isSome ∧ v < n then some { s with ptr := Function.update s.ptr v (some id) } else none

/-- The number of clusters that `v` ever belongs to. -/
noncomputable def everCount (s : NCAState) (v : ℕ) : ℕ :=
  {id | ∃ e, s.ever id = some e ∧ v ∈ e}.ncard

end NCAState

/-- An operation: an edge deletion or a short-path query. -/
inductive NCAOp where
  | del (e : ℕ)
  | query (id u v : ℕ)

namespace NCAOp

/-- The words of an operation. -/
def words : NCAOp → List ℕ
  | .del e => [0, e]
  | .query id u v => [1, id, u, v]

/-- The updates of `G`. -/
def gPart : NCAOp → List GUpdate
  | .del e => [.delE e]
  | .query _ _ _ => []

/-- Whether an operation is a query. -/
def isQ : NCAOp → Bool
  | .del _ => false
  | .query _ _ _ => true

end NCAOp

/-- The protocol of a neighborhood-cover algorithm, for vertices below `n`. -/
def ncaProtocol (n : ℕ) : Protocol NCAOp NCAReport NCAState where
  opWords := NCAOp.words
  isQuery := NCAOp.isQ
  enc := NCAReport.words
  step := NCAState.step n
  st₀ := ⟨none, fun _ => none, fun _ => none, fun _ => none⟩

/-- An input of a neighborhood-cover algorithm. -/
structure NCAInput where
  n : ℕ
  edges : List (ℕ × ℕ × ℕ)
  D : ℚ

namespace NCAInput

variable (I : NCAInput)

/-- The number of edges. -/
def m : ℕ := I.edges.length

/-- The conditions of Definition 9.1: `m ≥ 1` and `D > 0`. -/
structure Ok : Prop where
  edges_ok : EdgesOk I.n I.edges
  m_pos : 1 ≤ I.m
  D_pos : 0 < I.D

/-- The initialization words. -/
def words : List ℕ :=
  I.n :: edgeWords I.edges ++ ratWords I.D

/-- `G` after the first `t` operations. -/
def Gt (σ : List NCAOp) (t : ℕ) : Graph ℕ ℕ :=
  gAt (ofEdges I.n I.edges) (σ.map NCAOp.gPart) t

/-- Valid operations: a present edge is deleted; a query names a current cluster and two distinct vertices of it. -/
def Valid (W : ℕ) (A : Program) (σ : List NCAOp) : Prop :=
  ∀ (t : ℕ) (o : NCAOp), σ[t]? = some o →
    match o with
    | .del e => e ∈ (I.Gt σ t).E
    | .query id u v => u ≠ v ∧ ∃ s c, (ncaProtocol I.n).state W A I.words σ t = some s ∧
        s.cur id = some c ∧ u ∈ c ∧ v ∈ c

end NCAInput

/-- The clauses of Definition 9.1 for one run, with the functions `α, s, T` and the constant `C_A`. -/
structure NCAHolds (α s T : ℕ → ℕ) (CA W : ℕ) (A : Program) (I : NCAInput) (σ : List NCAOp) : Prop where
  runs : RunsThrough W A ((ncaProtocol I.n).blocks I.words σ)
  /-- At initialization, the algorithm reports `α(m)` and `s(m)`. -/
  params : ∃ st, (ncaProtocol I.n).state W A I.words σ 0 = some st ∧ st.params = some (α I.m, s I.m)
  /-- At all times: the clusters are clusters of `G`, every `CoveringCluster(v)` is a current cluster containing `BG(v, D)`, and every
  vertex has ever belonged to at most `s(m)` clusters. -/
  log : ∀ t ≤ σ.length, ∃ st, (ncaProtocol I.n).state W A I.words σ t = some st ∧
    (∀ id c, st.cur id = some c → (c : Set ℕ) ⊆ (I.Gt σ t).V) ∧
    (∀ v ∈ (I.Gt σ t).V, ∃ id c, st.ptr v = some id ∧ st.cur id = some c ∧ (I.Gt σ t).ball v (I.D : ℝ) ⊆ (c : Set ℕ)) ∧
    ∀ v < I.n, st.everCount v ≤ s I.m
  /-- Short-path queries: a walk in `G` of length at most `α(m)·D`, in time `C_A·log₂(2+n+m)^{C_A}·(|E(P)| + 1)`. -/
  query : ∀ (t id u v : ℕ), σ[t]? = some (.query id u v) →
    ∃ es, (ncaProtocol I.n).answer W A I.words σ t = some es ∧
      (I.Gt σ t).WalkFromTo u es v ∧
      ((I.Gt σ t).walkLen es : ℝ) ≤ (α I.m : ℝ) * (I.D : ℝ) ∧
      ((ncaProtocol I.n).opTime W A I.words σ t : ℝ) ≤ polylog CA I.n I.m * ((es.length : ℝ) + 1)
  /-- The total update time `C_A·(n + m·T(m))`. -/
  time : ((ncaProtocol I.n).updateTime W A I.words σ : ℝ) ≤ (CA : ℝ) * ((I.n : ℝ) + (I.m : ℝ) * (T I.m : ℝ))

/-- `A` is an `(α, s, T)`-neighborhood-cover algorithm with constant `C_A` (Definition 9.1). -/
def IsNCAlgorithm (α s T : ℕ → ℕ) (CA : ℕ) (A : Program) : Prop :=
  NoRand A ∧ ∀ I : NCAInput, I.Ok → ∀ (W : ℕ) (σ : List NCAOp),
    CA * Nat.clog 2 (2 + (ncaProtocol I.n).inputMax I.words σ + α I.m + s I.m + T I.m) ≤ W →
    I.Valid W A σ → NCAHolds α s T CA W A I σ

end DecrNbhdCover.Supplement


