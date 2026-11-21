-- Prove2me | Definitions.Def_SourceProof_eb8f90c564e2c0a8f493e6ac
-- name    : SourceProof_eb8f90c564e2c0a8f493e6ac
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:57:24.679163+00:00
-- url     : https://prove2.me/theorems/14313b9c-a954-4367-b6e1-3ebf9b1ddcfc
-- title:
--   LevyStochCalc source module: SourceProof_eb8f90c564e2c0a8f493e6ac
-- statement:
--   The original source theorem `LevyStochCalc.Ito.Picard.exists_bieleckiWeight_rate_lt_one` comes from the `LevyStochCalc.Ito.PicardContractionEstimate` module. The staged Lean declaration includes its source proof and dependency references.
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

omit [ℱ'.IsRightContinuous] hℱW hℱN hℱ0 hnull hReg in

theorem _root_.Prove2MeSourceProof.h_eb8f90c564e2c0a8f493e6ac (L : ℝ) (hT : 0 < T) :
    ∃ β : ℝ, 0 < β ∧
      (ENNReal.ofReal
        ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
          / (2 * β))) ^ ((1 : ℝ) / 2) < 1 := by
  set A : ℝ := 3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2) with hA
  have hAnn : 0 ≤ A := by
    have h1 : (0 : ℝ) ≤ (n : ℝ) * L ^ 2 * T := by positivity
    have h2 : (0 : ℝ) ≤ (n : ℝ) * ((d : ℝ) * L ^ 2) := by positivity
    have h3 : (0 : ℝ) ≤ (n : ℝ) * L ^ 2 := by positivity
    rw [hA]; linarith
  refine ⟨A / 2 + 1, by linarith, ?_⟩
  have hden : 0 < 2 * (A / 2 + 1) := by linarith
  have hlt : A / (2 * (A / 2 + 1)) < 1 := by
    rw [div_lt_one hden]; linarith
  refine ENNReal.rpow_lt_one ?_ (by norm_num)
  calc ENNReal.ofReal (A / (2 * (A / 2 + 1))) < ENNReal.ofReal 1 :=
        (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr hlt
    _ = 1 := ENNReal.ofReal_one
/-! ### Bielecki bookkeeping for the fixed point -/

/-! ### The step against a raw state process -/

end LevyStochCalc.Ito.Picard


