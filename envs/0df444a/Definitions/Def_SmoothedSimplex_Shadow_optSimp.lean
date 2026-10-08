-- Prove2me | Definitions.Def_SmoothedSimplex_Shadow_optSimp
-- name    : SmoothedSimplex_Shadow_optSimp
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T12:46:53.153174+00:00
-- url     : https://prove2.me/theorems/cd969edd-7d9d-465e-af97-b73b96c81834
-- title:
--   Definition 3.2.1 — $\mathrm{optSimp}_z(a_1,\dots,a_n)$ (with $y=\mathbf 1$)
-- statement:
--   Let $z,a_1,\dots,a_n\in\mathbb R^d$. Write $[n]=\{1,\dots,n\}$, and for $I\subseteq[n]$ let $A_I$ be the matrix with columns $a_i$, $i\in I$. Then $\mathrm{optSimp}_z(a_1,\dots,a_n)$ is the set of index sets $I\in\binom{[n]}{d}$ such that
--
--   1. $A_I$ has full rank,
--   2. the simplex $\triangle(A_I)=\mathrm{ConvHull}(a_i : i\in I)$ is a facet of $\mathrm{ConvHull}(0,a_1,\dots,a_n)$, and
--   3. $z\in\mathrm{Cone}(A_I)=\{\sum_{i\in I}\alpha_i a_i:\alpha_i\ge0\}$.
--
--   Polar picture: $\mathrm{ConvHull}(0,a_1,\dots,a_n)$ is the polar of the polyhedron $\{x:\langle a_i|x\rangle\le1\ \forall i\}$, and $I\in\mathrm{optSimp}_z$ exactly when the vertex $x=A_I^{-T}\mathbf 1$ maximizes $\langle z|x\rangle$ over it (the paper's Proposition 3.2.2). For data in general position $\mathrm{optSimp}_z$ is empty or a single index set.
--
--   **Formalization Note** Indices are `Fin n` (0-based). Full rank is linear independence of $(a_i)_{i\in I}$ together with $|I|=d$. "Facet" is encoded as: $\mathrm{ConvHull}(A_I)$ is an exposed face of $\mathrm{ConvHull}(\{0,a_1,\dots,a_n\})$; with linear independence this face is $(d-1)$-dimensional and avoids the origin. This is the definition itself, not the duality characterisation. Only the case $y=\mathbf 1$ of the paper's definition is needed in this mission.
-- source:
--   Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7, Definition 3.2.1, printed p. 30 (PDF p. 30); Cone and △ from §2.1, p. 14

import Mathlib

namespace SmoothedSimplex.Shadow

/-- `optSimp_z(a₁, …, aₙ)` with `y = 1` (Spielman & Teng, arXiv:cs/0111050v7, Definition 3.2.1,
printed p. 30, PDF p. 30): the set of `I ∈ ([n] choose d)` such that `A_I` has full rank,
`△((aᵢ)_{i∈I})` is a facet of `ConvHull(0, a₁, …, aₙ)`, and `z ∈ Cone((aᵢ)_{i∈I})`.

**Formalization Note.**
* Indices are `Fin n` (0-based); the paper's `[n] = {1, …, n}`.
* "`A_I` has full rank" is linear independence of `(aᵢ)_{i∈I}` with `|I| = d`.
* "`△(A_I)` is a facet of `ConvHull(0, a₁, …, aₙ)`" is: `convexHull (A_I)` is an exposed face of
  `convexHull ({0} ∪ {a₁, …, aₙ})`. Together with linear independence this makes it a
  `(d−1)`-dimensional proper face (it does not contain `0`), i.e. a facet; for polytopes faces
  and exposed faces coincide.
* `Cone(A_I) = {∑_{i∈I} αᵢ aᵢ : αᵢ ≥ 0}` (§2.1, p. 14).
* This is the definition, not the dual characterisation of Proposition 3.2.2. -/
def IsOptSimp {d n : ℕ} (z : EuclideanSpace ℝ (Fin d)) (a : Fin n → EuclideanSpace ℝ (Fin d))
    (I : Finset (Fin n)) : Prop :=
  I.card = d ∧
  LinearIndependent ℝ (fun i : I => a i) ∧
  IsExposed ℝ (convexHull ℝ (insert 0 (Set.range a))) (convexHull ℝ (a '' (I : Set (Fin n)))) ∧
  ∃ α : Fin n → ℝ, (∀ i, 0 ≤ α i) ∧ z = ∑ i ∈ I, α i • a i

open Classical in
/-- `optSimp_z(a₁, …, aₙ)` as a finite set of index sets: see `IsOptSimp`. -/
noncomputable def optSimp {d n : ℕ} (z : EuclideanSpace ℝ (Fin d))
    (a : Fin n → EuclideanSpace ℝ (Fin d)) : Finset (Finset (Fin n)) :=
  Finset.univ.filter (fun I => IsOptSimp z a I)

end SmoothedSimplex.Shadow


