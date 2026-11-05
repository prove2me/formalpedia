-- Prove2me | Definitions.Def_MultiStageAlloc_Decomposition
-- name    : MultiStageAlloc_Decomposition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:31:41.980215+00:00
-- url     : https://prove2.me/theorems/9ee38cd0-3d16-4f8b-aa92-dc3b10f09d0b
-- title:
--   The structural decomposition of Proposition 2: $G^\prime_k$, its pairs $(U^{(l)}_k,V^{(l)}_k)$ and the prices $c^{(l)}_k$
-- statement:
--   Let $x$ be an allocation of stage $k$ and let $y$ be the levels before it. The graph $G'_k$ joins $i$ and $j$ when $x_{ij}>0$. The set $V^{(0)}_k$ consists of the offline vertices with level exactly $1$, and $U^{(0)}_k$ of the vertices of $U_k$ with $x_{ij}>0$ for some $j\in V^{(0)}_k$.
--
--   For $l\ge 1$, the pairs $(U^{(l)}_k,V^{(l)}_k)$ are the connected components of the subgraph of $G'_k$ induced on $(U_k\setminus U^{(0)}_k)\cup(V\setminus V^{(0)}_k)$. The **price** of an offline vertex is $w_j(1-f_k(\text{level of }j))$. The value $c^{(l)}_k$ is the price of an offline vertex of the pair, and $0$ if the pair has no offline vertex.
--
--   This construction is the content of Proposition 2, which the dual assignment in the proof of Theorem 1 is built from.
--
--   **Formalization Note** The index $l\in[0:L_k]$ is an option on the connected components, with `none` for $l=0$. The value $0$ on a pair with no offline vertex is part of the correction to Proposition 2, because the printed $c^{(l)}_k$ is undefined there.
-- source:
--   Feng & Niazadeh, Batching and Optimal Multi-stage Bipartite Allocations, arXiv:2211.16581v1, Proposition 2, pp.20–21

import Mathlib
import Definitions.Def_MultiStageAlloc_StageProgram

namespace MultiStageAlloc

variable {U V : Type*} [Fintype U] [Fintype V] {K : ℕ}

/-- **The graph `G'_k`** of Proposition 2, arXiv:2211.16581v1, p.20, on the vertex set `U ⊕ V`: `i` and
`j` are adjacent iff `x_ij > 0`. For a stage-`k` allocation, positive entries lie on `E_k`. -/
def supportGraph (x : U → V → ℝ) : SimpleGraph (U ⊕ V) :=
  SimpleGraph.fromRel (fun a b => ∃ i j, a = Sum.inl i ∧ b = Sum.inr j ∧ 0 < x i j)

/-- **`V^(0)_k`**, the offline vertices fully matched given `y`, arXiv:2211.16581v1, p.20:
`y_j + ∑_i x_ij / n_j = 1`. -/
def fullOffline (I : Instance U V K) (y : V → ℝ) (x : U → V → ℝ) : Set V :=
  {j | level I y x j = 1}

/-- **`U^(0)_k`**, the vertices of `U_k` adjacent in `G'_k` to `V^(0)_k`, arXiv:2211.16581v1, p.20. -/
def fullOnline (I : Instance U V K) (k : ℕ) (y : V → ℝ) (x : U → V → ℝ) : Set U :=
  {i | I.batch i = k ∧ ∃ j ∈ fullOffline I y x, 0 < x i j}

/-- **The vertex set of the induced subgraph `G'_k[U_k \ U^(0)_k, V \ V^(0)_k]`**,
arXiv:2211.16581v1, p.21. -/
def residualVertices (I : Instance U V K) (k : ℕ) (y : V → ℝ) (x : U → V → ℝ) : Set (U ⊕ V) :=
  {a | (∃ i, a = Sum.inl i ∧ I.batch i = k ∧ i ∉ fullOnline I k y x) ∨
       (∃ j, a = Sum.inr j ∧ j ∉ fullOffline I y x)}

/-- **The connected components of `G'_k[U_k \ U^(0)_k, V \ V^(0)_k]`**, the indices `l ∈ [L_k]` of
Proposition 2, arXiv:2211.16581v1, p.21. -/
abbrev Component (I : Instance U V K) (k : ℕ) (y : V → ℝ) (x : U → V → ℝ) : Type _ :=
  ((supportGraph x).induce (residualVertices I k y x)).ConnectedComponent

/-- **The index set `l ∈ [0 : L_k]`** of Proposition 2: `none` is `l = 0`, the pair
`(U^(0)_k, V^(0)_k)`; `some C` is the component `C`. -/
abbrev PairIndex (I : Instance U V K) (k : ℕ) (y : V → ℝ) (x : U → V → ℝ) : Type _ :=
  Option (Component I k y x)

open Classical in
/-- The index of the pair containing an online vertex: its component if it is in the residual
graph, and `0` otherwise (for `i ∈ U_k`, that is exactly `i ∈ U^(0)_k`). -/
noncomputable def onlinePair (I : Instance U V K) (k : ℕ) (y : V → ℝ) (x : U → V → ℝ) (i : U) :
    PairIndex I k y x :=
  if h : Sum.inl i ∈ residualVertices I k y x then
    some (SimpleGraph.connectedComponentMk _ ⟨Sum.inl i, h⟩)
  else none

open Classical in
/-- The index of the pair containing an offline vertex: its component if it is in the residual
graph, and `0` otherwise (that is exactly `j ∈ V^(0)_k`). -/
noncomputable def offlinePair (I : Instance U V K) (k : ℕ) (y : V → ℝ) (x : U → V → ℝ) (j : V) :
    PairIndex I k y x :=
  if h : Sum.inr j ∈ residualVertices I k y x then
    some (SimpleGraph.connectedComponentMk _ ⟨Sum.inr j, h⟩)
  else none

/-- **`U^(l)_k`**, arXiv:2211.16581v1, pp.20–21: the online vertices of pair `l`, all in `U_k`. -/
def pairU (I : Instance U V K) (k : ℕ) (y : V → ℝ) (x : U → V → ℝ) (l : PairIndex I k y x) : Set U :=
  {i | I.batch i = k ∧ onlinePair I k y x i = l}

/-- **`V^(l)_k`**, arXiv:2211.16581v1, pp.20–21: the offline vertices of pair `l`. -/
def pairV (I : Instance U V K) (k : ℕ) (y : V → ℝ) (x : U → V → ℝ) (l : PairIndex I k y x) : Set V :=
  {j | offlinePair I k y x j = l}

/-- **The price of an offline vertex** `w_j (1 - f_k(y_j + ∑_i x_ij / n_j))`, Proposition 2(1),
arXiv:2211.16581v1, p.21. -/
noncomputable def levelPrice (I : Instance U V K) (k : ℕ) (y : V → ℝ) (x : U → V → ℝ) (j : V) : ℝ :=
  I.w j * (1 - regPoly K k (level I y x j))

open Classical in
/-- **`c^(l)_k`**, Proposition 2(1), arXiv:2211.16581v1, p.21: the price of an offline vertex of the
pair `l`, and `0` if the pair has no offline vertex.

**Formalization Note.** The page defines `c^(l)_k` by the price of "`j ∈ V^(l)_k`", which is undefined
on a component made of one online vertex. The value `0` there is part of the corrected statement of
Proposition 2. The vertex is picked by choice; Proposition 2(1) says the choice is immaterial. -/
noncomputable def pairPrice (I : Instance U V K) (k : ℕ) (y : V → ℝ) (x : U → V → ℝ)
    (l : PairIndex I k y x) : ℝ :=
  if h : (pairV I k y x l).Nonempty then levelPrice I k y x h.some else 0

end MultiStageAlloc


