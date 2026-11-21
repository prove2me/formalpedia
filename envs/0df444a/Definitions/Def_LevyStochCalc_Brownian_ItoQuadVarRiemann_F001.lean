-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoQuadVarRiemann_F001
-- name    : LevyStochCalc_Brownian_ItoQuadVarRiemann_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:35:43.113686+00:00
-- url     : https://prove2.me/theorems/6fde55e6-83d4-4ef9-9b29-962e24e1c855
-- title:
--   LevyStochCalc source module: LevyStochCalc.Brownian.ItoQuadVarRiemann
-- statement:
--   Exact source-faithful declarations from LevyStochCalc.Brownian.ItoQuadVarRiemann in the pinned LevyStochCalc project.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoProcessVersion_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoQuadVarSum_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoQuadVarSum_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoQuadVarSum_F003
import Definitions.Def_LevyStochCalc_Brownian_ItoTimeRiemann_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The quadratic-variation Riemann sum of the Itô formula

Squaring the increments of a continuous Itô process across a uniform grid and weighting them by
a bounded Lipschitz function of the process gives a Riemann sum for `∫_0^T φ(X_s)·H_s² ds`. The
drift square and the cross term are `O(1/m)` and `O(m^{-1/2})`, the compensated squares are
`O(m^{-1/2})` by the martingale-difference bound, and the compensator itself is a frozen-weight
Riemann sum for the density `H²`.

## Main statements

* `LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_sum_drift_sq_le` — the drift-square sum.
* `LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_sum_cross_le` — the cross term.
* `LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_sum_quadVar_le` — the compensated
  squares.
* `LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_quadVarRiemann_sub_le` — the four
  pieces together.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section QuadVarRiemann

variable {P : Measure Ω} [IsProbabilityMeasure P] {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}
  {H : Ω → ℝ → ℝ} {hm : Measurable (Function.uncurry H)}
  {hp : Probability.ProgressivelyMeasurable ℱ H}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → ℝ} {bdrift : Ω → ℝ → ℝ} {X : ℝ → Ω → ℝ}
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

include hCH in
/-- The square of a version's increment splits into the drift square, the cross term, the
compensated square, and the compensator. -/
theorem IsItoVersion.sq_sub_ae
    (h : IsItoVersion W ℱ hℱ H hm hp hq X₀ bdrift X)
    (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    ∀ᵐ ω ∂P, (X v ω - X u ω) ^ 2
      = (∫ s in Set.Ioc u v, bdrift ω s ∂volume) ^ 2
        + 2 * (∫ s in Set.Ioc u v, bdrift ω s ∂volume)
            * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
              - stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω)
        + quadVarIncrement W ℱ hℱ H hm hp hq u v ω
        + ∫ s in Set.Ioc u v, H ω s ^ 2 ∂volume := by
  filter_upwards [h.ae_eq v (hu.trans huv), h.ae_eq u hu] with ω hv hu'
  have hHsq : (∫ s in Set.Icc (0 : ℝ) v, H ω s ^ 2 ∂volume)
      - ∫ s in Set.Icc (0 : ℝ) u, H ω s ^ 2 ∂volume
      = ∫ s in Set.Ioc u v, H ω s ^ 2 ∂volume := by
    refine setIntegral_Icc_sub_Icc (B := C ^ 2)
      ((Measurable.of_uncurry_left hm).pow_const 2) (fun s => ?_) hu huv
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hCH ω s) 2
  rw [hv, hu', itoProcess_sub W ℱ hℱ H hm hp hq X₀ bdrift hbm hB hu huv ω]
  unfold quadVarIncrement
  rw [hHsq]
  ring
end QuadVarRiemann

end LevyStochCalc.Brownian.Ito


