-- Prove2me | Definitions.Def_OAIQ240Bp022
-- name    : OAIQ240Bp022
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T00:56:26.629945+00:00
-- url     : https://prove2.me/theorems/e60945f1-3bb9-4f76-bc60-b5025b118a70
-- title:
--   Definitions bundle OAIQ240Bp022 of the split of OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 8 declarations of OpenAI's Lean: 8 definitions. The definitions and types are `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.glf11`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.glf13`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.glf14`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.glf5`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.glf6`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.glf8`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.glf9`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.regularityTranslation`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`BallPacking_Continuation_ParameterizedImplicit`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Continuation/ParameterizedImplicit.lean), [`BallPacking_Fredholm_TranslationContinuity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/TranslationContinuity.lean).
--
--   **Imports.** It imports the published bundle `Def_BallPacking`; the bundles `OAIQ240Bp020` and `OAIQ240Bp021` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.fullLineEquation_local_chart_eq_bp240`, `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_isolatedFullLineZeros_compact`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.regularityTranslation_continuous_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.regularityTranslation_near_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.regularityTranslation_smooth_bp240`, `OAI_HigherDimensionalBallPacking_Rigidity_adapted_line_continuation_data`, `OAI_HigherDimensionalBallPacking_Rigidity_completed_line_closed`, `OAI_HigherDimensionalBallPacking_Rigidity_exact_line_homotopy_residual_energy_bound`, `OAI_HigherDimensionalBallPacking_Rigidity_exact_marked_zeroSet_compact`, `OAI_HigherDimensionalBallPacking_Rigidity_fullLineEndpointMap` and `OAI_HigherDimensionalBallPacking_Rigidity_fullLineProperPath`; the proofs of `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completed_markedCurve_contDiff_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.fullLineEquation_local_chart_eq_bp240`, `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_isolatedFullLineZeros_compact`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.regularityTranslation_continuous_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.regularityTranslation_near_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.regularityTranslation_smooth_bp240`, `OAI_HigherDimensionalBallPacking_Rigidity_adapted_line_continuation_data`, `OAI_HigherDimensionalBallPacking_Rigidity_completed_line_closed`, `OAI_HigherDimensionalBallPacking_Rigidity_exact_line_homotopy_residual_energy_bound`, `OAI_HigherDimensionalBallPacking_Rigidity_exact_line_local_energy_of_slope`, `OAI_HigherDimensionalBallPacking_Rigidity_exact_marked_line_czero_compactness`, `OAI_HigherDimensionalBallPacking_Rigidity_exact_marked_line_gradient_bound`, `OAI_HigherDimensionalBallPacking_Rigidity_exact_marked_line_uniform_defect_support`, `OAI_HigherDimensionalBallPacking_Rigidity_exact_marked_zeroSet_compact`, `OAI_HigherDimensionalBallPacking_Rigidity_fullLineEndpointMap`, `OAI_HigherDimensionalBallPacking_Rigidity_fullLineProperPath` and `OAI.HigherDimensionalBallPacking.Rigidity.fullLineProperPath_bp240`.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp020
import Definitions.Def_OAIQ240Bp021

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_TranslationContinuity
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
section
variable {n : ℕ}
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst4
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst6
variable {J : Phase n → End n} (hJ : ContDiff ℝ ∞ J) (hc : ∀ x, Compatible (J x)) {B : ℝ}
  (hstd : ∀ x, B<‖x‖ → J x=standardJ n) (b : ContDiffBump (0:ℂ)) (p q : Phase n)
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst10
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst11
variable (w : freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) {R : ℝ}
  (hRS : R+1≤b.rOut) (hsupp : w.val ∈ freeModel (E := Phase n) (Metric.closedBall (0:ℂ) R))
  (hesc : FreeEscapeNeighborhood b p (markedSlope p q w.val) w.val B)
  (hcr : ∀ z, fderiv ℝ (markedCurve p q w.val) z Complex.I =
    J (markedCurve p q w.val z) (fderiv ℝ (markedCurve p q w.val) z 1))

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst7
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst8
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst9
def regularityTranslation : ℂ → freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut) :=
  freeTranslation hRS (markedSlope p q w.val) ⟨w.val,hsupp⟩

end

end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Continuation_ParameterizedImplicit
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology
open Filter
open scoped BoundedContinuousFunction
open Set Function
section

variable {n : ℕ}
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.glf1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.glf2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.glf3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.glf4
variable {J : Phase n → End n} (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
  (hJc : HasCompactSupport (fun x => J x-standardJ n))
  (b b₁ : ContDiffBump (0:ℂ)) (p q : Phase n)
local instance glf5 : NormedAddCommGroup (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance glf6 : NormedSpace ℝ (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.glf7
local instance glf8 : NormedSpace ℝ (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance glf9 : AddCommGroup (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (glf5 (n := n) b).toAddCommGroup
local instance glf10_r6587ce_1 : Module ℝ (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (glf6 (n := n) b).toModule
local instance glf11 : AddCommGroup (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (glf7 (n := n) b).toAddCommGroup
local instance glf12_r6587ce_1 : Module ℝ (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (glf8 (n := n) b).toModule
local instance glf13 : TopologicalSpace (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) :=
  (glf5 (n := n) b).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
local instance glf14 : TopologicalSpace (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) :=
  (glf7 (n := n) b).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

end

end HigherDimensionalBallPacking.Rigidity.HolderCompletion

end

end OAI
end


