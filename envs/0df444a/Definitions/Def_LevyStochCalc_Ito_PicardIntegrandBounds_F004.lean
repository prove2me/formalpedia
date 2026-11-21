-- Prove2me | Definitions.Def_LevyStochCalc_Ito_PicardIntegrandBounds_F004
-- name    : LevyStochCalc_Ito_PicardIntegrandBounds_F004
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:27:26.321481+00:00
-- url     : https://prove2.me/theorems/780c40fc-7b33-47fe-ac4a-c88764ce0b54
-- title:
--   Source declarations: LevyStochCalc.Ito.PicardIntegrandBounds
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.PicardIntegrandBounds. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardBieleckiContractionTight_F000
import Definitions.Def_LevyStochCalc_Ito_PicardBieleckiContraction_F000
import Definitions.Def_LevyStochCalc_Ito_PicardBieleckiNorm_F001
import Definitions.Def_LevyStochCalc_Ito_PicardSelfMap_F000
import Definitions.Def_LevyStochCalc_Ito_PicardStepMap_F000
import Definitions.Def_LevyStochCalc_Ito_PicardStepMap_F001
import Definitions.Def_LevyStochCalc_Ito_PicardStochasticLipschitz_F000
import Definitions.Def_SourceProof_946b446a671aae16e8dcf40a
import Definitions.Def_SourceProof_ba444e4a7f686c4937645db3
import Mathlib.Algebra.Order.Chebyshev

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

/-- **The drift integrand along the frozen process is square integrable at every horizon.** -/
theorem lintegral_sq_mu_stop_lt_top {n d : ℕ} {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] {ν : MeasureTheory.Measure E}
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (Y : SBoundedProcess (n := n) P ℱ T) (hT : 0 ≤ T)
    (i : Fin n) {T' : ℝ} (hT' : 0 < T') :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coeffs.μ s (Y.stop.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
  _root_.Prove2MeSourceProof.h_946b446a671aae16e8dcf40a coeffs hReg hLip
    (fun b => lt_of_le_of_lt (_root_.Prove2MeSourceProof.h_ba444e4a7f686c4937645db3 Y hT b)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top Y.sup_L2))) i hT'
/-- Joint measurability of the drift integrand along a jointly measurable state process. -/
theorem measurable_mu_comp_state {n d : ℕ} {ν : MeasureTheory.Measure E}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {X : ℝ → Ω → (Fin n → ℝ)} (hX : Measurable (Function.uncurry X)) (i : Fin n) :
    Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i) :=
  ((measurable_pi_apply i).comp hReg.1).comp
    (measurable_snd.prodMk (hX.comp (measurable_snd.prodMk measurable_fst)))
end LevyStochCalc.Ito.Picard


