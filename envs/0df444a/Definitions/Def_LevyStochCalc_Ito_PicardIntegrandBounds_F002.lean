-- Prove2me | Definitions.Def_LevyStochCalc_Ito_PicardIntegrandBounds_F002
-- name    : LevyStochCalc_Ito_PicardIntegrandBounds_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:32:55.883179+00:00
-- url     : https://prove2.me/theorems/92abcbea-6831-47a7-b7b1-cab3571d0012
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
import Definitions.Def_SourceProof_35d8365844de2771203e553f
import Definitions.Def_SourceProof_ba444e4a7f686c4937645db3
import Definitions.Def_SourceProof_e303374519c4de703021a2f6
import Definitions.Def_SourceProof_e554e55fb9c1def6b7e8b55b
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

/-- **The jump integrand along the frozen process is square integrable at every horizon.**
This is the hypothesis `picardStep` asks for and that `sup_L2` alone cannot supply. -/
theorem lintegral_sq_gamma_stop_lt_top {n d : ℕ} {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] {ν : MeasureTheory.Measure E}
    [MeasureTheory.SigmaFinite ν]
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (Y : SBoundedProcess (n := n) P ℱ T) (hT : 0 ≤ T)
    (i : Fin n) {T' : ℝ} (hT' : 0 < T') :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖coeffs.γ s (Y.stop.X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ :=
  _root_.Prove2MeSourceProof.h_e554e55fb9c1def6b7e8b55b coeffs hReg hLip Y.stop.measurable_path
    (fun b => lt_of_le_of_lt (_root_.Prove2MeSourceProof.h_ba444e4a7f686c4937645db3 Y hT b)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top Y.sup_L2))) i hT'
/-- Composing a jointly measurable coefficient with a progressively measurable state process
gives a progressively measurable integrand. -/
theorem progressivelyMeasurable_comp_state {n : ℕ}
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {X : ℝ → Ω → (Fin n → ℝ)}
    (hX : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ (fun ω s => X s ω i))
    {f : ℝ → (Fin n → ℝ) → ℝ} (hf : Measurable (Function.uncurry f)) :
    Probability.ProgressivelyMeasurable ℱ (fun ω s => f s (X s ω)) := by
  refine _root_.Prove2MeSourceProof.h_35d8365844de2771203e553f ?_
  intro t
  letI : MeasurableSpace Ω := ℱ t
  have hXm : Measurable fun q : Set.Iic t × Ω => (X (q.1 : ℝ) q.2 : Fin n → ℝ) :=
    measurable_pi_lambda _ fun i => ((_root_.Prove2MeSourceProof.h_e303374519c4de703021a2f6 (hX i)) t).measurable
  have hq : Measurable fun q : Set.Iic t × Ω => ((q.1 : ℝ), X (q.1 : ℝ) q.2) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk hXm
  exact (hf.comp hq).stronglyMeasurable
end LevyStochCalc.Ito.Picard


