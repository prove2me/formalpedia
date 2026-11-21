-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoFormulaScalar_F001
-- name    : LevyStochCalc_Brownian_ItoFormulaScalar_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:40:35.28256+00:00
-- url     : https://prove2.me/theorems/af822aa3-9b96-4030-8740-55c37a4cf591
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

/-- The `L¹` error of the uniform-grid approximation in Itô's formula, as a function of the
mesh. -/
noncomputable def itoGridError (B C T K K₂ : ℝ) (x : ℝ) : ℝ :=
  K * (4 * (B ^ 3 * T * x ^ 2
      + (C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2 * (T * Real.sqrt x)))
    + K₂ * B * (T * (B * x + C * Real.sqrt x))
    + Real.sqrt (C ^ 2 * (K₂ ^ 2 * (T * (2 * (B * x) ^ 2 + 2 * (C ^ 2 * x)))))
    + 1 / 2 * (K₂ * (B ^ 2 * T * x)
        + 2 * K₂ * B * C * T * Real.sqrt x
        + Real.sqrt (K₂ ^ 2 * ((2 * (6 + gaussianFourthMoment) + 2) * C ^ 4) * (T * x))
        + K * C ^ 2 * (T * (B * x + C * Real.sqrt x)))
@[simp] theorem itoGridError_zero (B C T K K₂ : ℝ) : itoGridError B C T K K₂ 0 = 0 := by
  simp [itoGridError]
theorem continuous_itoGridError (B C T K K₂ : ℝ) :
    Continuous (itoGridError B C T K K₂) := by
  unfold itoGridError
  fun_prop
theorem tendsto_itoGridError (B C T K K₂ : ℝ) :
    Filter.Tendsto (fun m : ℕ => itoGridError B C T K K₂ (T / (m : ℝ)))
      Filter.atTop (𝓝 0) := by
  have hx : Filter.Tendsto (fun m : ℕ => T / (m : ℝ)) Filter.atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat T
  have hcomp := ((continuous_itoGridError B C T K K₂).tendsto 0).comp hx
  rwa [itoGridError_zero] at hcomp
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


