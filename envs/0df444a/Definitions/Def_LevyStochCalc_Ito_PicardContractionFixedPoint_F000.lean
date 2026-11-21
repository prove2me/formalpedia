-- Prove2me | Definitions.Def_LevyStochCalc_Ito_PicardContractionFixedPoint_F000
-- name    : LevyStochCalc_Ito_PicardContractionFixedPoint_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T22:51:41.022+00:00
-- url     : https://prove2.me/theorems/e0c3a7dd-d678-4864-9b15-f7d501d3dc57
-- title:
--   Source declarations: LevyStochCalc.Ito.PicardContractionFixedPoint
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.PicardContractionFixedPoint. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardContractionEstimate_F002
import Definitions.Def_LevyStochCalc_Ito_PicardContractionEstimate_F004

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The fixed point of the Picard step

The limit `picardLimit` of the Picard iterates is jointly measurable, progressively measurable and
of finite Bielecki norm, and the Bielecki distance between the step taken along it and the limit
itself vanishes, so the step and the limit agree almost surely at every time of the window. The
step contracts between two raw state processes and therefore respects almost sure equality of its
input, which promotes that agreement to the statement that the process built over the limit solves
the Picard equation along its own path.

## Main statements

* `picardLimit` — the limit of the Picard iterates.
* `bieleckiNorm_picardStepOnRawStop_picardLimit_eq_zero` — the limit is a fixed point in norm.
* `picardSelfMapRaw_picardLimit_ae_eq` — the fixed point is realised by a process of the space.
* `picardSelfMapRaw_isFixedPoint` — the fixed point solves its own Picard equation.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
variable {n d : ℕ} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}

variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
  (ℱ' : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) [ℱ'.IsRightContinuous]
  (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ')
  (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ')
  (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ' 0 ≤ ℱ' t)
  (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ' 0] s)
  (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
  (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)

/-! ### The fixed point -/

variable {L : ℝ}
  (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
  (x₀ : Fin n → ℝ)

/-- **The limit of the Picard iterates.** -/
noncomputable def picardLimit (hT : 0 < T) (X₀ : SBoundedProcess (n := n) P ℱ' T) :
    ℝ → Ω → (Fin n → ℝ) :=
  bieleckiLimit fun m =>
    (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ m).X
theorem measurable_picardLimit (hT : 0 < T) (X₀ : SBoundedProcess (n := n) P ℱ' T) :
    Measurable (Function.uncurry
      (picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀)) :=
  measurable_bieleckiLimit fun m =>
    (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ m).measurable_path
theorem progressivelyMeasurable_picardLimit (hT : 0 < T)
    (X₀ : SBoundedProcess (n := n) P ℱ' T) (i : Fin n) :
    Probability.ProgressivelyMeasurable ℱ'
      fun ω s => picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ s ω i :=
  progressivelyMeasurable_bieleckiLimit
    (fun m i' => (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ m).adapted i') i
omit [ℱ'.IsRightContinuous] hℱW hℱN hℱ0 hnull hReg in
/-- Slice measurability of a jointly measurable path map. -/
theorem measurable_slice_of_uncurry {Z : ℝ → Ω → (Fin n → ℝ)}
    (hZm : Measurable (Function.uncurry Z)) (t : ℝ) (i : Fin n) :
    Measurable fun ω => Z t ω i :=
  (measurable_pi_apply i).comp (Measurable.of_uncurry_left hZm)
/-! ### The step respects almost sure equality of its input -/

/-! ### The fixed point solves its own Picard equation -/

end LevyStochCalc.Ito.Picard


