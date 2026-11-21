-- Prove2me | Definitions.Def_LevyStochCalc_Ito_PicardIntegrandBounds_F001
-- name    : LevyStochCalc_Ito_PicardIntegrandBounds_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:21:20.72433+00:00
-- url     : https://prove2.me/theorems/775c5470-aab7-4cab-b88f-8f2529d42c2c
-- title:
--   Source declarations: LevyStochCalc.Ito.PicardIntegrandBounds
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.PicardIntegrandBounds. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardIntegrandBounds_F000
import Definitions.Def_SourceProof_ba444e4a7f686c4937645db3
import Definitions.Def_SourceProof_bdaa282fd363a3be48f8fdce

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Square integrability of the Picard integrands along a state process

Linear growth of the coefficients, read off the Lipschitz hypothesis by comparison with the
state `0`, turns the bounds at that single state recorded by `IsRegular` into bounds along a
state process: whenever the state has finite energy over every horizon, the drift, diffusion
and jump integrands evaluated along it are square integrable at every horizon, and a member of
the process space frozen at `T` has that energy. Composing a jointly measurable coefficient
with a measurable, respectively progressively measurable, state process supplies the matching
measurability of the integrands.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- **The diffusion integrand along the frozen process is square integrable at every horizon.**
This is the hypothesis `picardStep` asks for and that `sup_L2` alone cannot supply. -/
theorem lintegral_sq_sigma_stop_lt_top {n d : ℕ} {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] {ν : MeasureTheory.Measure E}
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (Y : SBoundedProcess (n := n) P ℱ T) (hT : 0 ≤ T)
    (i : Fin n) (j : Fin d) {T' : ℝ} (hT' : 0 < T') :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coeffs.σ s (Y.stop.X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
  _root_.Prove2MeSourceProof.h_bdaa282fd363a3be48f8fdce coeffs hReg hLip Y.stop.measurable_path
    (fun b => lt_of_le_of_lt (_root_.Prove2MeSourceProof.h_ba444e4a7f686c4937645db3 Y hT b)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top Y.sup_L2))) i j hT'
/-- The Euclidean sum of squares dominates the squared supremum norm, as extended reals. -/
theorem ofReal_sq_norm_le_sum {n : ℕ} (x : Fin n → ℝ) :
    ENNReal.ofReal (‖x‖ ^ 2) ≤ ∑ i, (‖x i‖₊ : ℝ≥0∞) ^ 2 := by
  refine (ENNReal.ofReal_le_ofReal (sq_norm_le_sum_sq x)).trans ?_
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
  exact le_of_eq (Finset.sum_congr rfl fun i _ => (sq_coe_nnnorm_real (x i)).symm)
end LevyStochCalc.Ito.Picard


