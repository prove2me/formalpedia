-- Prove2me | Definitions.Def_LevyStochCalc_Ito_PicardOutputWeighting_F003
-- name    : LevyStochCalc_Ito_PicardOutputWeighting_F003
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:43:42.533072+00:00
-- url     : https://prove2.me/theorems/f0dd4497-6638-4d73-84d4-2347b4d1d729
-- title:
--   LevyStochCalc source module: LevyStochCalc.Ito.PicardOutputWeighting
-- statement:
--   Exact source-faithful declarations from LevyStochCalc.Ito.PicardOutputWeighting in the pinned LevyStochCalc project.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardOutputModification_F001
import Definitions.Def_LevyStochCalc_Ito_PicardOutputModification_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Bielecki weighting and the per-component difference bounds

The Bielecki norm with rate `β` dominates the second moment at each time of `[0, T]` after
reweighting by `e^{2βs}`, and the doubly-integrated energy over `[0, t]` by
`e^{2βt}/(2β)`, the factor `1/(2β)` being what makes the Picard rate small for large `β`.
Combined with the Lipschitz bounds on the coefficients this bounds the drift, diffusion and
jump components of the difference of two Picard steps by the energy of the difference of the
two frozen paths.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
variable {n d : ℕ} {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]

section Weighting

omit [MeasurableSpace Ω] [MeasureTheory.IsProbabilityMeasure P] in
/-- The `γ` clause of `IsLipschitz`, read on a single coordinate along two processes. This is
where the `ℝ≥0∞` form of the clause is used: the `.toReal` form it replaced would give nothing
when the jump energy is infinite. -/
theorem gamma_lip_componentwise {ν : MeasureTheory.Measure E}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E) {L : ℝ}
    (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (X Y : ℝ → Ω → (Fin n → ℝ)) (i : Fin n) (s : ℝ) (ω : Ω) :
    ∫⁻ e, (‖coeffs.γ s (X s ω) e i - coeffs.γ s (Y s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν
      ≤ ENNReal.ofReal (L ^ 2) * (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 := by
  calc ∫⁻ e, (‖coeffs.γ s (X s ω) e i - coeffs.γ s (Y s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν
      ≤ ∫⁻ e, (‖coeffs.γ s (X s ω) e - coeffs.γ s (Y s ω) e‖₊ : ℝ≥0∞) ^ 2 ∂ν := by
        refine lintegral_mono fun e => ?_
        have hco : |coeffs.γ s (X s ω) e i - coeffs.γ s (Y s ω) e i|
            ≤ ‖coeffs.γ s (X s ω) e - coeffs.γ s (Y s ω) e‖ := by
          simpa [Real.norm_eq_abs, Pi.sub_apply] using
            norm_le_pi_norm (coeffs.γ s (X s ω) e - coeffs.γ s (Y s ω) e) i
        rw [sq_coe_nnnorm_real, sq_coe_nnnorm]
        refine ENNReal.ofReal_le_ofReal ?_
        nlinarith [hco, abs_nonneg (coeffs.γ s (X s ω) e i - coeffs.γ s (Y s ω) e i),
          sq_abs (coeffs.γ s (X s ω) e i - coeffs.γ s (Y s ω) e i),
          norm_nonneg (coeffs.γ s (X s ω) e - coeffs.γ s (Y s ω) e)]
    _ ≤ ENNReal.ofReal (L ^ 2 * ‖X s ω - Y s ω‖ ^ 2) := hLip.2.2.2 s (X s ω) (Y s ω)
    _ = ENNReal.ofReal (L ^ 2) * (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 := by
        rw [ENNReal.ofReal_mul (sq_nonneg L), sq_coe_nnnorm]
end Weighting

end LevyStochCalc.Ito.Picard


