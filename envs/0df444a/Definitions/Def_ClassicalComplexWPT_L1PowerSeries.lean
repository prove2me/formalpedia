-- Prove2me | Definitions.Def_ClassicalComplexWPT_L1PowerSeries
-- name    : ClassicalComplexWPT_L1PowerSeries
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T17:59:12.049672+00:00
-- url     : https://prove2.me/theorems/c46a5ba8-1aeb-4cad-a598-6f34cb3f3b1d
-- title:
--   L1 Power Series
-- statement:
--   Definitions and structural lemmas for L1 Power Series, from BochaoKong (BochaoKong/classical-complex-wpt; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Classical complex-analytic Weierstrass preparation theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1PowerSeries.lean

import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Mathlib.Analysis.Analytic.Constructions
import Theorems.Thm_ClassicalComplexWPT_monomial_zero
attribute [local simp] ClassicalComplexWPT.monomial_zero


set_option autoImplicit true
open scoped ENNReal NNReal Topology
noncomputable section
namespace ClassicalComplexWPT
abbrev L1Sequence := L1Coeff ℕ
noncomputable def coefficientEval (k : ℕ) : L1Sequence →L[ℂ] ℂ :=
  lp.evalCLM ℂ (fun _ : ℕ ↦ ℂ) 1 k
theorem norm_coefficientEval_le (k : ℕ) : ‖coefficientEval k‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro a
  change ‖a k‖ ≤ 1 * ‖a‖
  simpa using lp.norm_apply_le_norm (by norm_num) a k
noncomputable def l1OperatorSeries :
    FormalMultilinearSeries ℂ ℂ (L1Sequence →L[ℂ] ℂ) :=
  fun k ↦ (ContinuousMultilinearMap.mkPiAlgebraFin ℂ k ℂ).smulRight (coefficientEval k)
theorem norm_l1OperatorSeries_le (k : ℕ) : ‖l1OperatorSeries k‖ ≤ 1 := by
  rw [l1OperatorSeries, ContinuousMultilinearMap.norm_smulRight,
    ContinuousMultilinearMap.norm_mkPiAlgebraFin, one_mul]
  exact norm_coefficientEval_le k
theorem one_le_radius_l1OperatorSeries : 1 ≤ l1OperatorSeries.radius := by
  apply l1OperatorSeries.le_radius_of_bound 1
  intro k
  simpa using norm_l1OperatorSeries_le k
noncomputable def l1EvalOperator (w : ℂ) : L1Sequence →L[ℂ] ℂ :=
  l1OperatorSeries.sum w
theorem analyticAt_l1EvalOperator : AnalyticAt ℂ l1EvalOperator 0 := by
  exact (l1OperatorSeries.hasFPowerSeriesOnBall
    (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1) one_le_radius_l1OperatorSeries)).analyticAt
noncomputable def evalL1PowerSeries (a : L1Sequence) (w : ℂ) : ℂ :=
  l1EvalOperator w a
theorem analyticAt_evalL1PowerSeries (a : L1Sequence) :
    AnalyticAt ℂ (fun x : L1Sequence × ℂ ↦ evalL1PowerSeries x.1 x.2) (a, 0) := by
  let app : (L1Sequence →L[ℂ] ℂ) →L[ℂ] L1Sequence →L[ℂ] ℂ :=
    ContinuousLinearMap.flip (ContinuousLinearMap.apply ℂ ℂ)
  have happ : AnalyticAt ℂ (fun x : (L1Sequence →L[ℂ] ℂ) × L1Sequence ↦ app x.1 x.2)
      (l1EvalOperator 0, a) := app.analyticAt_bilinear _
  have hop : AnalyticAt ℂ (fun x : L1Sequence × ℂ ↦ l1EvalOperator x.2) (a, 0) :=
    analyticAt_l1EvalOperator.comp (f := fun x : L1Sequence × ℂ ↦ x.2) analyticAt_snd
  exact happ.comp₂ hop analyticAt_fst
theorem AnalyticAt.evalL1PowerSeries
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {q : E → L1Sequence} (hq : AnalyticAt ℂ q 0) (s : ℂ) :
    AnalyticAt ℂ
      (fun x : E × ℂ ↦ evalL1PowerSeries (q x.1) (s * x.2)) 0 := by
  have hq' : AnalyticAt ℂ (fun x : E × ℂ ↦ q x.1) 0 :=
    hq.comp (f := fun x : E × ℂ ↦ x.1) analyticAt_fst
  have hw' : AnalyticAt ℂ (fun x : E × ℂ ↦ s * x.2) 0 :=
    analyticAt_const.mul analyticAt_snd
  have hpair : AnalyticAt ℂ
      (fun x : E × ℂ ↦ (q x.1, s * x.2)) 0 := hq'.prod hw'
  have hout : AnalyticAt ℂ
      (fun x : L1Sequence × ℂ ↦ ClassicalComplexWPT.evalL1PowerSeries x.1 x.2)
      ((fun x : E × ℂ ↦ (q x.1, s * x.2)) 0) := by
    simpa using analyticAt_evalL1PowerSeries (q 0)
  have hcomp := hout.comp (f := fun x : E × ℂ ↦ (q x.1, s * x.2)) hpair
  simpa [Function.comp_def] using hcomp
end ClassicalComplexWPT


