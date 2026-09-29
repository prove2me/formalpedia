-- Prove2me | Definitions.Def_ChanPangGQVI_Existence_GICP
-- name    : ChanPangGQVI_Existence_GICP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:36:10.509449+00:00
-- url     : https://prove2.me/theorems/77d9ec1e-7435-4f0f-b93f-fa770e495ee8
-- title:
--   Dual cone, the map K(x) = m(x) + L(x), and solutions of the generalized implicit complementarity problem GICP(L, m, f)
-- statement:
--   Work in $\mathbb R^n$ with the Euclidean inner product. The **dual cone** of a set $S$ is
--
--   $$
--   S^* = \{\, y\in\mathbb R^n : y^T x \ge 0 \text{ for all } x\in S \,\}.
--   $$
--
--   Let $m$ be a point-to-point mapping of $\mathbb R^n$ and let $L$ be a cone-valued mapping: each $L(x)$ is a convex cone (containing the origin). Equation (1) of the paper defines the point-to-set mapping
--
--   $$
--   K(x) = m(x)+L(x) = \{\, x' : x' = m(x)+z \text{ for some } z\in L(x) \,\}.
--   $$
--
--   For a further point-to-set mapping $f$, the **generalized implicit complementarity problem** $\mathrm{GICP}(L,m,f)$ asks for vectors $x$ and $y$ with
--
--   $$
--   x\in m(x)+L(x),\qquad y\in f(x)\cap L(x)^*,\qquad y^T\big(x-m(x)\big)=0 .
--   $$
--
--   Such a pair $(x,y)$ is a solution of $\mathrm{GICP}(L,m,f)$. With $L(x)=\mathbb R^n_+$ and single-valued affine $f$ it is the implicit complementarity problem; with $L$ constant and $m\equiv 0$ it is Saigal's generalized complementarity problem.
--
--   **Formalization Note** Cones are Mathlib `PointedCone ℝ _` (convex, containing $0$), as footnote 1 of the paper ("All cones are convex") and the proof of Proposition 2.1 require. The three objects are `dualConeSet`, `coneTranslate m L` and `IsGICPSolution L m f x y`.
-- source:
--   Chan and Pang, The generalized quasi-variational inequality problem, Math. Oper. Res. 7 (1982), p. 212, Section 2 (dual cone, footnote 1, equation (1)); p. 213 (definition of GICP(L, m, f))

import Mathlib

open scoped RealInnerProductSpace

namespace ChanPangGQVI.Existence

/-- Chan and Pang 1982, p. 212, §2: the dual cone of a set `S ⊆ ℝⁿ`,
`S* = {y ∈ ℝⁿ : yᵀ x ≥ 0 for all x ∈ S}`. -/
def dualConeSet {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {y | ∀ x ∈ S, 0 ≤ ⟪y, x⟫}

/-- Chan and Pang 1982, p. 212, equation (1): for a point-to-point mapping `m` and a
cone-valued mapping `L` of `ℝⁿ`, `K(x) = m(x) + L(x) = {x' : x' = m(x) + y for some y ∈ L(x)}`.
Cones are convex and contain the origin (footnote 1, p. 212), hence `PointedCone ℝ _`. -/
def coneTranslate {n : ℕ} (m : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (L : EuclideanSpace ℝ (Fin n) → PointedCone ℝ (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x' | ∃ z ∈ L x, x' = m x + z}

/-- Chan and Pang 1982, p. 213, §2: a solution of the generalized implicit complementarity
problem `GICP(L, m, f)` is a pair `(x, y)` with `x ∈ m(x) + L(x)`, `y ∈ f(x) ∩ L(x)*` and
`yᵀ (x - m(x)) = 0`. -/
def IsGICPSolution {n : ℕ}
    (L : EuclideanSpace ℝ (Fin n) → PointedCone ℝ (EuclideanSpace ℝ (Fin n)))
    (m : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (x y : EuclideanSpace ℝ (Fin n)) : Prop :=
  x ∈ coneTranslate m L x ∧ y ∈ f x ∧ y ∈ dualConeSet (L x : Set (EuclideanSpace ℝ (Fin n))) ∧
    ⟪y, x - m x⟫ = 0

end ChanPangGQVI.Existence


