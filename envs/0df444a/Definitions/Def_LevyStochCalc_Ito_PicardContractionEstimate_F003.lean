-- Prove2me | Definitions.Def_LevyStochCalc_Ito_PicardContractionEstimate_F003
-- name    : LevyStochCalc_Ito_PicardContractionEstimate_F003
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:57:31.132675+00:00
-- url     : https://prove2.me/theorems/25045a29-8ff3-446e-a59e-26d558cc812d
-- title:
--   Source declarations: LevyStochCalc.Ito.PicardContractionEstimate
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.PicardContractionEstimate. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardLimit_F001
import Definitions.Def_LevyStochCalc_Ito_PicardOutputStepDiff_F000

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

omit [IsProbabilityMeasure P] [ℱ'.IsRightContinuous] in
/-- Slice measurability suffices for the Bielecki subadditivity hypothesis. -/
theorem bieleckiNorm_inner_aemeasurable_of_slice {Y : ℝ → Ω → (Fin n → ℝ)}
    (h : ∀ (t : ℝ) (i : Fin n), Measurable fun ω => Y t ω i) (t : ℝ) :
    AEMeasurable (fun ω => (∑ i, (‖Y t ω i‖₊ : ℝ≥0∞) ^ 2) ^ ((1 : ℝ) / 2)) P :=
  ((Finset.measurable_sum _ fun i _ =>
    (ENNReal.continuous_coe.measurable.comp (h t i).nnnorm).pow_const 2).pow_const
      ((1 : ℝ) / 2)).aemeasurable
omit [ℱ'.IsRightContinuous] in
/-- The Bielecki norm of a difference is symmetric. -/
theorem bieleckiNorm_sub_comm (β T : ℝ) (A B : ℝ → Ω → (Fin n → ℝ)) :
    bieleckiNorm (P := P) β T (fun t ω i => A t ω i - B t ω i)
      = bieleckiNorm (P := P) β T (fun t ω i => B t ω i - A t ω i) := by
  unfold bieleckiNorm
  refine iSup_congr fun t => iSup_congr fun _ => ?_
  congr 2
  refine lintegral_congr fun ω => Finset.sum_congr rfl fun i _ => ?_
  simp only [show A t ω i - B t ω i = -(B t ω i - A t ω i) from by ring, nnnorm_neg]
/-! ### The step against a raw state process -/

end LevyStochCalc.Ito.Picard


