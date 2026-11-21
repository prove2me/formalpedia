-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoFormulaScalar_F000
-- name    : LevyStochCalc_Brownian_ItoFormulaScalar_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:38:22.069681+00:00
-- url     : https://prove2.me/theorems/545d5bbb-ea08-4b45-a707-52c9007aac97
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoFormulaScalar
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoFormulaScalar. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoMartingaleRiemann_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoQuadVarRiemann_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoQuadVarRiemann_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula for a scalar Itô process

For a continuous adapted version `X` of `X₀ + ∫ b ds + ∫ H dW` with bounded coefficients and
`f` twice differentiable with bounded derivatives and a Lipschitz second derivative,

  `f(X_T) − f(X_0) = ∫_0^T f'(X_s) b_s ds + ∫_0^T f'(X_s) H_s dW_s
      + ½ ∫_0^T f''(X_s) H_s² ds`

almost surely. The proof telescopes the second-order Taylor expansion over a uniform grid and
bounds the four resulting errors, all of which vanish as the mesh does.

## Main statements

* `LevyStochCalc.Brownian.Ito.itoGridError` — the `L¹` error of the grid approximation, as a
  function of the mesh.
* `LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_itoFormula_le` — that error bounds the
  `L¹` defect of Itô's formula on every uniform grid.
* `LevyStochCalc.Brownian.Ito.IsItoVersion.itoFormula` — Itô's formula.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The mean value theorem in the form used here: a bound on the derivative is a Lipschitz
constant. -/
theorem abs_sub_le_of_hasDerivAt_bound {g g' : ℝ → ℝ} (hg : ∀ x, HasDerivAt g (g' x) x)
    {K : ℝ} (hK : ∀ x, |g' x| ≤ K) (x y : ℝ) : |g x - g y| ≤ K * |x - y| := by
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := g) (f' := g') (s := Set.univ) (C := K)
    (fun z _ => (hg z).hasDerivWithinAt)
    (fun z _ => by rw [Real.norm_eq_abs]; exact hK z)
    convex_univ (Set.mem_univ y) (Set.mem_univ x)
  rwa [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
section Formula

variable {P : Measure Ω} [IsProbabilityMeasure P] {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}
  {H : Ω → ℝ → ℝ} {hm : Measurable (Function.uncurry H)}
  {hp : Probability.ProgressivelyMeasurable ℱ H}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → ℝ} {bdrift : Ω → ℝ → ℝ} {X : ℝ → Ω → ℝ}
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

end Formula

end LevyStochCalc.Brownian.Ito


