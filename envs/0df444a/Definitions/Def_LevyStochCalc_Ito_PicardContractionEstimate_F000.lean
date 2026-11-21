-- Prove2me | Definitions.Def_LevyStochCalc_Ito_PicardContractionEstimate_F000
-- name    : LevyStochCalc_Ito_PicardContractionEstimate_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:57:02.635877+00:00
-- url     : https://prove2.me/theorems/6873ae19-f14c-4222-a438-0cb6d557139e
-- title:
--   Source declarations: LevyStochCalc.Ito.PicardContractionEstimate
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.PicardContractionEstimate. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardIntegrandBounds_F000
import Definitions.Def_LevyStochCalc_Ito_PicardLimit_F001
import Definitions.Def_LevyStochCalc_Ito_PicardOutputModification_F000
import Definitions.Def_LevyStochCalc_Ito_PicardOutputModification_F001
import Definitions.Def_LevyStochCalc_Ito_PicardOutputModification_F002
import Definitions.Def_LevyStochCalc_Ito_PicardOutputMoments_F000
import Definitions.Def_LevyStochCalc_Ito_PicardOutputMoments_F001
import Definitions.Def_LevyStochCalc_Ito_PicardOutputMoments_F002
import Definitions.Def_LevyStochCalc_Ito_PicardOutputMoments_F003
import Definitions.Def_LevyStochCalc_Ito_PicardOutputStepDiff_F000
import Definitions.Def_LevyStochCalc_Ito_PicardOutputWeighting_F000
import Definitions.Def_LevyStochCalc_Ito_PicardOutputWeighting_F001
import Definitions.Def_LevyStochCalc_Ito_PicardOutputWeighting_F002
import Definitions.Def_LevyStochCalc_Ito_PicardOutputWeighting_F003
import Mathlib.MeasureTheory.Function.Floor

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Picard contraction estimate

The contraction estimate of `bieleckiNorm_picardStep_diff_le` is stated for the Picard step along
two raw path maps. Along two processes of the space its hypotheses are supplied by the frozen
integrand lemmas, and the Bielecki norm of a difference is unchanged by freezing at the horizon, so
the estimate transfers to `picardStepOnStop`, from there through the modification
`picardSelfMap_ae_eq` to `picardSelfMap` itself, and in the same way to the step taken against a
raw state process. The iterates `picardIter` of the self-map are consequently geometrically
Bielecki-Cauchy, and at a weight making the contraction rate `< 1` they converge to
`bieleckiLimit`.

## Main statements

* `bieleckiNorm_picardStepOnStop_diff_le` — the estimate for the step along frozen processes.
* `bieleckiNorm_picardSelfMap_diff_le` — the estimate for the self-map.
* `bieleckiNorm_picardIter_sub_bieleckiLimit_le` — the iterates converge to `bieleckiLimit`.
* `bieleckiNorm_picardStepOnStop_sub_rawStop_le` — the estimate against a raw state process.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
variable {n d : ℕ} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}

/-! ### The difference of two frozen processes -/

/-- The squared norm of a difference is at most twice the sum of the squared norms. -/
theorem sq_nnnorm_sub_le {α : Type*} [SeminormedAddCommGroup α] (a b : α) :
    (‖a - b‖₊ : ℝ≥0∞) ^ 2 ≤ 2 * (‖a‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖b‖₊ : ℝ≥0∞) ^ 2 := by
  have hreal : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
    have h := norm_sub_le a b
    nlinarith [norm_nonneg a, norm_nonneg b, norm_nonneg (a - b), sq_nonneg (‖a‖ - ‖b‖)]
  calc (‖a - b‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖a - b‖ ^ 2) := sq_coe_nnnorm _
    _ ≤ ENNReal.ofReal (2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2) := ENNReal.ofReal_le_ofReal hreal
    _ = 2 * (‖a‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖b‖₊ : ℝ≥0∞) ^ 2 := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), sq_coe_nnnorm, sq_coe_nnnorm,
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
        norm_num
/-- The difference of two frozen processes is jointly measurable. -/
theorem measurable_uncurry_stop_sub (X Y : SBoundedProcess (n := n) P ℱ T) :
    Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => X.stop.X s ω - Y.stop.X s ω) :=
  (X.stop.measurable_path.comp (measurable_snd.prodMk measurable_fst)).sub
    (Y.stop.measurable_path.comp (measurable_snd.prodMk measurable_fst))
/-- The norm of the difference of two frozen processes is jointly measurable. -/
theorem measurable_uncurry_stop_sub_norm (X Y : SBoundedProcess (n := n) P ℱ T) :
    Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => ‖X.stop.X s ω - Y.stop.X s ω‖) :=
  (measurable_uncurry_stop_sub X Y).norm
/-- The `ω`-slice of the squared norms of a path map is measurable in time. -/
theorem measurable_sq_slice_time {Z : ℝ → Ω → (Fin n → ℝ)}
    (hZm : Measurable (Function.uncurry Z)) (ω : Ω) :
    Measurable fun s : ℝ => ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 :=
  Finset.measurable_sum _ fun i _ =>
    (ENNReal.continuous_coe.measurable.comp
      (((measurable_pi_apply i).comp
        (hZm.comp (measurable_id.prodMk measurable_const))).nnnorm)).pow_const 2
/-- The squared norms of a path map are jointly measurable. -/
theorem measurable_uncurry_sq {Z : ℝ → Ω → (Fin n → ℝ)}
    (hZm : Measurable (Function.uncurry Z)) :
    Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2) :=
  Finset.measurable_sum _ fun i _ =>
    (ENNReal.continuous_coe.measurable.comp
      (((measurable_pi_apply i).comp
        (hZm.comp (measurable_snd.prodMk measurable_fst))).nnnorm)).pow_const 2
/-- The energy of a path map over a window is measurable in the sample point. -/
theorem measurable_lintegral_sq {Z : ℝ → Ω → (Fin n → ℝ)}
    (hZm : Measurable (Function.uncurry Z)) (b : ℝ) :
    Measurable fun ω : Ω =>
      ∫⁻ s in Set.Icc (0 : ℝ) b, ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
  (measurable_uncurry_sq hZm).lintegral_prod_right'
    (ν := volume.restrict (Set.Icc (0 : ℝ) b))
/-! ### The contraction estimate for the step and the self-map -/

/-! ### The Picard iterates and their limit -/

variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
  (ℱ' : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) [ℱ'.IsRightContinuous]
  (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ')
  (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ')
  (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ' 0 ≤ ℱ' t)
  (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ' 0] s)
  (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
  (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)

/-! ### The limit of the iterates -/

/-! ### Bielecki bookkeeping for the fixed point -/

/-! ### The step against a raw state process -/

end LevyStochCalc.Ito.Picard


