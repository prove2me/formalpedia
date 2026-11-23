-- Prove2me | Definitions.Def_CubicNewton_Nonconvex_Supplement_CubicDual
-- name    : CubicNewton_Nonconvex_Supplement_CubicDual
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T08:01:18.128803+00:00
-- url     : https://prove2.me/theorems/d0a9a0f6-e691-44d4-8e0b-5bc9e94845b3
-- title:
--   Section 5.1 — primal cubic function $v_u$, dual function $v_l$, domain $\mathcal D$, direction $h(r)$
-- statement:
--   Let $g\in\mathbb R^n$, let $H$ be a linear operator on $\mathbb R^n$ and $M\in\mathbb R$. Define
--   $$v_u(h)=\langle g,h\rangle+\tfrac12\langle Hh,h\rangle+\tfrac M6\|h\|^3,\qquad v_l(r)=-\tfrac12\Big\langle\Big(H+\tfrac{Mr}2I\Big)^{-1}g,g\Big\rangle-\tfrac M{12}r^3,$$
--   $$\mathcal D=\Big\{r\in\mathbb R:\ H+\tfrac{Mr}2I\succ0,\ r\ge0\Big\},\qquad h(r)=-\Big(H+\tfrac{Mr}2I\Big)^{-1}g .$$
--   Here $\succ0$ means positive definite. $v_u$ is the cubic subproblem (5.1) that computes the step $T_M(x)$, and $v_l$ is its one-dimensional dual (Theorem 10). The notation $v_u(g;h)$ and $h(g;r)$ is used when $g$ varies (Lemma 9).
--
--   **Formalization Note** The inverse is `ContinuousLinearMap.inverse`, which is the actual inverse whenever $H+\frac{Mr}2I$ is invertible (in particular on $\mathcal D$) and $0$ otherwise; the theorems use it only where the operator is invertible.
--   Differences from the source:
--   - encoding: inverse of H + (Mr/2)I in the dual formulas → ContinuousLinearMap.inverse, with value 0 outside the invertible locus; reason: all theorem evaluations and their local derivatives occur at invertible shifts; the definitions specialize exactly to the source for symmetric H and M > 0 on the stated domain
-- source:
--   Nesterov & Polyak, Cubic regularization of Newton method and its global performance, Math. Program. Ser. A 108 (2006) 177–205, DOI 10.1007/s10107-006-0706-8, p. 198, Section 5.1 (definitions of v_u, v_l, 𝒟 and h(r))

import Mathlib

open scoped RealInnerProductSpace

namespace CubicNewton.Nonconvex.Supplement

/-- The primal cubic function of Section 5.1 (Nesterov–Polyak 2006, p. 198):
`v_u(g; h) = ⟨g, h⟩ + ½⟨H h, h⟩ + (M/6)‖h‖³`, the cubic subproblem (5.1). -/
noncomputable def vu {n : ℕ} (g : EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (M : ℝ)
    (h : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ⟪g, h⟫ + 1 / 2 * ⟪H h, h⟫ + M / 6 * ‖h‖ ^ 3

/-- The shifted operator `H + (M r / 2) I`. -/
noncomputable def shiftedOp {n : ℕ}
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (M r : ℝ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  H + (M * r / 2) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))

/-- The dual domain `𝒟 = {r ∈ ℝ : H + (M r/2) I ≻ 0, r ≥ 0}` (p. 198), with `≻ 0` meaning
positive definite: `⟨(H + (M r/2) I) w, w⟩ > 0` for every `w ≠ 0`. -/
def dualDomain {n : ℕ} (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (M : ℝ) :
    Set ℝ :=
  {r | 0 ≤ r ∧ ∀ w : EuclideanSpace ℝ (Fin n), w ≠ 0 → 0 < ⟪shiftedOp H M r w, w⟫}

/-- The direction `h(r) = −(H + (M r/2) I)⁻¹ g` (p. 198), also written `h(g; r)` (p. 200).
`ContinuousLinearMap.inverse` is the actual inverse whenever `H + (M r/2) I` is invertible, in
particular for every `r ∈ 𝒟`; it is `0` otherwise, and the statements only use it where the
operator is invertible. -/
noncomputable def hDir {n : ℕ} (g : EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (M r : ℝ) :
    EuclideanSpace ℝ (Fin n) :=
  -(ContinuousLinearMap.inverse (shiftedOp H M r) g)

/-- The dual function `v_l(r) = −½⟨(H + (M r/2) I)⁻¹ g, g⟩ − (M/12) r³` (p. 198). -/
noncomputable def vl {n : ℕ} (g : EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (M r : ℝ) : ℝ :=
  -(1 / 2) * ⟪ContinuousLinearMap.inverse (shiftedOp H M r) g, g⟫ - M / 12 * r ^ 3

end CubicNewton.Nonconvex.Supplement


