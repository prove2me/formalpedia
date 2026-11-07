-- Prove2me | Definitions.Def_SoftmaxAttnFD_CanonicalCells
-- name    : SoftmaxAttnFD_CanonicalCells
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:02:22.824617+00:00
-- url     : https://prove2.me/theorems/0e916d75-dfb2-432a-946d-92723cbd9513
-- title:
--   Faces, pulling chains, canonical cells and conflict sets
-- statement:
--   For a set $T$ of constraints of $P=P(\Sigma')$, the **face** is $F_T=P\cap\bigcap_{H\in T}\partial H$. The least vertex $v_F$ of a face is its lexicographically first vertex of $P$.
--
--   A **pulling chain** with owner $s\in\Sigma'$ is a sequence of active sets $T_0=\{s\}$, $T_{i+1}=T_i\cup\{H_i\}$ with $H_i\notin T_i$ a constraint of $P$, for $i<d-1$, with each face $F_{T_i}$ nonempty and $v_{F_{T_i}}\notin F_{T_{i+1}}$. By Lemma B.1(b), under general position these are exactly the chains of faces of Definition B.7, where each $F^{(i)}$ is a facet of $F^{(i-1)}$ omitting its least vertex.
--
--   A **canonical cell** is the pair of the owner $s$ and the tuple of $d$ projected least vertices $\bar v_{F^{(0)}},\dots,\bar v_{F^{(d-1)}}$; its simplex is the convex hull $\Delta$ of the tuple. The **conflict set** relative to a ground set $\Sigma$ is
--   $$C_\Delta=\{s'\in\Sigma:\ \tilde f_{s'}(u)>\tilde f_{s_\Delta}(u)\text{ for some }u\in\Delta\}.$$
-- source:
--   Huang, Chen, Softmax Attention with Any Temperature in Fixed Dimension, arXiv:2611.06055 (sha256 a60f7609…), Definitions 6.6, B.7, pp.24, 51; Lemma B.1, p.45

import Definitions.Def_SoftmaxAttnFD_Envelope

namespace SoftmaxAttnFD

/-- The face `F_T = P ∩ ⋂_{H ∈ T} ∂H` (arXiv:2611.06055, sha256 a60f7609…, Lemma B.1, p.45). -/
def Family.face {d : ℕ} (F : Family d) (S' : Finset ℕ) (T : Finset (Con d)) : Set (Pt d) :=
  {x | x ∈ F.polytope S' ∧ ∀ t ∈ T, x.2 = evalSrc (F.con t) x.1}

/-- Strict lexicographic order on the coordinates `(u₁, …, u_{d−1}, z)` (Definition B.7, p.51). -/
def LexLT {d : ℕ} (v w : Pt d) : Prop :=
  Pi.Lex (· < ·) (· < ·) v.1 w.1 ∨ (v.1 = w.1 ∧ v.2 < w.2)

/-- `v` is the least vertex `v_F` of the face `F_T` of `P(Σ′)` (Definition B.7, p.51): a vertex of
`P(Σ′)` lying in `F_T` that precedes all other such vertices. -/
def Family.IsLeastVertex {d : ℕ} (F : Family d) (S' : Finset ℕ) (T : Finset (Con d))
    (v : Pt d) : Prop :=
  v ∈ (F.polytope S').extremePoints ℝ ∧ v ∈ F.face S' T ∧
    ∀ w ∈ (F.polytope S').extremePoints ℝ, w ∈ F.face S' T → w ≠ v → LexLT v w

/-- A pulling chain with owner `s` (Definition B.7, p.51), given by active sets `T 0 ⊂ … ⊂ T (d−1)`
and least vertices `v 0, …, v (d−1)`.

**Formalization Note** The page's faces are `F^{(i)} = F_{T i}`. `T 0 = {s}` is the facet of source
`s`. A facet of `F_T` that omits `v_{F_T}` is `F_{T ∪ {H}}` with `H ∉ T`, nonempty and omitting that
vertex; by Lemma B.1(b), p.45, under general position these are exactly the page's facets. Indices are
natural numbers, read only below `d`. -/
structure Family.IsPullingChain {d : ℕ} (F : Family d) (S' : Finset ℕ) (s : ℕ)
    (T : ℕ → Finset (Con d)) (v : ℕ → Pt d) : Prop where
  owner_mem : s ∈ S'
  start : T 0 = {Sum.inr s}
  least : ∀ i < d, F.IsLeastVertex S' (T i) (v i)
  step : ∀ i, i + 1 < d → ∃ H : Con d, IsConOf S' H ∧ H ∉ T i ∧ T (i + 1) = insert H (T i) ∧
    v i ∉ F.face S' (T (i + 1))

/-- `(s, vs)` is a canonical cell of `P(Σ′)` (Definitions 6.6, B.7, pp.24, 51): `s` is the owner and
`vs` the projected vertices `v̄_{F^{(0)}}, …, v̄_{F^{(d−1)}}` of a pulling chain. The simplex itself is
`cellSet vs`. -/
def Family.IsCanonicalCell {d : ℕ} (F : Family d) (S' : Finset ℕ) (s : ℕ)
    (vs : Fin d → Fin (d - 1) → ℝ) : Prop :=
  ∃ (T : ℕ → Finset (Con d)) (v : ℕ → Pt d),
    F.IsPullingChain S' s T v ∧ ∀ i : Fin d, vs i = (v i.val).1

/-- The projected simplex `∆ = conv{v̄_{F^{(0)}}, …, v̄_{F^{(d−1)}}}`. -/
def cellSet {d : ℕ} (vs : Fin d → Fin (d - 1) → ℝ) : Set (Fin (d - 1) → ℝ) :=
  convexHull ℝ (Set.range vs)

/-- The conflict set `C_∆ = {s′ ∈ Σ : f̃_{s′}(u) > f̃_{s_∆}(u) for some u ∈ ∆}` of a cell with owner `s`
relative to the ground set `Σ` (Definition 6.6, p.24). -/
def Family.conflictSet {d : ℕ} (F : Family d) (S : Finset ℕ) (s : ℕ)
    (vs : Fin d → Fin (d - 1) → ℝ) : Set ℕ :=
  {s' | s' ∈ S ∧ ∃ u ∈ cellSet vs, evalSrc (F.src s) u < evalSrc (F.src s') u}

end SoftmaxAttnFD


