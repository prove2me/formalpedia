-- Prove2me | Definitions.Def_PADMPriv_Supplement_lapNoise
-- name    : PADMPriv_Supplement_lapNoise
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:48:28.478208+00:00
-- url     : https://prove2.me/theorems/567af883-3539-494d-b305-7e7c200c347d
-- title:
--   The joint Laplace noise law $L_m(0_m,\lambda)$ on $\mathbb R^m$
-- statement:
--   The noise law of PADM-$L_\lambda$ (Section 4.3). For an integer $m$ and a scale $\lambda>0$, $L_m(0_m,\lambda)$ is the law of a random vector $z=(z_1,\dots,z_m)\in\mathbb R^m$ whose coordinates are independent and each follows the Laplace law $L(0,\lambda)$ with density
--   $$
--   p_\lambda(x)=\frac{1}{2\lambda}\,e^{-|x|/\lambda},\qquad x\in\mathbb R .
--   $$
--   Each coordinate has mean $0$ and variance $2\lambda^2$, so $\mathbb E\|z\|_2^2=2m\lambda^2$.
--
--   This is the noise of the Laplace mechanism in private PADM: at step $k$ the user adds $z_{(k)}\sim L_m(0_m,\lambda)$, and the iterate moves by $z_{(k)}/2$ (update (20)).
--
--   **Formalization Note** The product of $m$ copies of the published one-dimensional law `PrivLearn.Generic.laplace s`, transported from `Fin m → ℝ` to `EuclideanSpace ℝ (Fin m)`. The scale is called `s` because `λ` is a Lean keyword. For `s ≤ 0` the formula gives the zero measure; every statement using this law assumes `0 < s`, as the paper does. The module also provides the σ-finiteness instance needed to form product measures.
-- source:
--   Li–Lai–Weng, Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization, STOC 2027 submission (manuscript sha256 d58edbe0…0f3d), Section 4.3, p.10 (density in Lemma A8, p.25)

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy

namespace PADMPriv.Supplement

open MeasureTheory

/-- The joint Laplace noise law `L_m(0_m, λ)` on `ℝᵐ` of PADM-L_λ, Li–Lai–Weng, *Exact Feasibility
and Privacy Amplification for Linearly Constrained Optimization*, STOC 2027 submission manuscript
(sha256 d58edbe0…0f3d), Section 4.3, p.10: every coordinate of the noise vector is drawn
independently from the Laplace law `L(0, λ)` with density `(1/2λ) e^{−|x|/λ}` (Lemma A8, p.25).

**Formalization Note** The product of `m` copies of the published one-dimensional Laplace law
`PrivLearn.Generic.laplace s` (density `(1/2s)e^{−|x|/s}`), transported from `Fin m → ℝ` to
`EuclideanSpace ℝ (Fin m)` by the measurable equivalence `WithLp.toLp 2`. The scale is named `s` (`λ` is a Lean keyword). It is a probability
measure only for `s > 0`, as the paper assumes ("with some `λ > 0`"); every statement using it
assumes a positive scale. -/
noncomputable def lapNoise (m : ℕ) (s : ℝ) : Measure (EuclideanSpace ℝ (Fin m)) :=
  (Measure.pi fun _ : Fin m => PrivLearn.Generic.laplace s).map
    (MeasurableEquiv.toLp 2 (Fin m → ℝ))

instance lapNoise_sigmaFinite (m : ℕ) (s : ℝ) : SigmaFinite (lapNoise m s) := by
  unfold lapNoise PrivLearn.Generic.laplace
  exact (MeasurableEquiv.toLp 2 (Fin m → ℝ)).sigmaFinite_map

end PADMPriv.Supplement


