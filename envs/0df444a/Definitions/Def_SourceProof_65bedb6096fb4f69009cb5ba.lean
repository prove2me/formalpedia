-- Prove2me | Definitions.Def_SourceProof_65bedb6096fb4f69009cb5ba
-- name    : SourceProof_65bedb6096fb4f69009cb5ba
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T22:43:01.531559+00:00
-- url     : https://prove2.me/theorems/47db5901-8f21-4017-9318-015e6b3370db
-- title:
--   LevyStochCalc source module: SourceProof_65bedb6096fb4f69009cb5ba
-- statement:
--   The original source theorem `LevyStochCalc.Ito.Picard.bieleckiNorm_sub_lt_top` comes from the `LevyStochCalc.Ito.PicardContractionEstimate` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardContractionEstimate_F001

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

omit [ℱ'.IsRightContinuous] in

theorem _root_.Prove2MeSourceProof.h_65bedb6096fb4f69009cb5ba {β : ℝ} (hβ : 0 ≤ β)
    (X Y : SBoundedProcess (n := n) P ℱ' T) :
    bieleckiNorm (P := P) β T (fun t ω i => X.X t ω i - Y.X t ω i) < ⊤ := by
  have hneg : LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) 0 T (fun t ω => -(Y.X t ω))
      = LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) 0 T Y.X := by
    unfold LevyStochCalc.Ito.Picard.bieleckiNorm
    refine iSup_congr fun t => iSup_congr fun _ => ?_
    congr 2
    exact lintegral_congr fun ω => Finset.sum_congr rfl fun i _ => by simp
  have hEq : (fun t ω i => X.X t ω i - Y.X t ω i)
      = fun t (ω : Ω) => X.X t ω + (fun i => -(Y.X t ω i)) := by
    funext t ω i
    simp [Pi.add_apply, sub_eq_add_neg]
  have hnegm : Measurable (Function.uncurry fun t (ω : Ω) => -(Y.X t ω)) :=
    measurable_neg.comp Y.measurable_path
  have hadd := _root_.Prove2MeSourceProof.h_1a604e3d857ca06f911ef6c7 (P := P) 0 T X.X (fun t ω => -(Y.X t ω))
    (fun t => _root_.Prove2MeSourceProof.h_d9c9229a83986bc9d7b21f99 _ X.measurable_path t)
    (fun t => _root_.Prove2MeSourceProof.h_d9c9229a83986bc9d7b21f99 (fun t ω => -(Y.X t ω)) hnegm t)
  refine lt_of_le_of_lt (LevyStochCalc.Ito.Picard.bieleckiNorm_le_bieleckiNorm_zero hβ T _) ?_
  rw [hEq]
  refine lt_of_le_of_lt hadd ?_
  rw [hneg]
  exact ENNReal.add_lt_top.mpr ⟨X.sup_L2, Y.sup_L2⟩
/-! ### Bielecki bookkeeping for the fixed point -/

/-! ### The step against a raw state process -/

end LevyStochCalc.Ito.Picard


