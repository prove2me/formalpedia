-- Prove2me | Definitions.Def_OAIQ240Bp021
-- name    : OAIQ240Bp021
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T00:50:22.567208+00:00
-- url     : https://prove2.me/theorems/779a2e9f-f9d3-4241-b5fd-1d880bd9219d
-- title:
--   Definitions bundle OAIQ240Bp021 of the split of OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 76 declarations of OpenAI's Lean: 74 definitions and 2 theorems. The definitions and types are `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.glf4`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmChartInst10`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmChartInst13`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmChartInst14`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmChartInst17`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmChartInst18`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmChartInst3`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmChartInst4`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmChartInst5`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmChartInst6`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmChartInst7`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmChartInst8`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmChartInst9`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmc2`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmc3`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmc4`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmc5`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmc6`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.isolatedFullLineZeros`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetObsInst1`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetObsInst2`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetObsInst3`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetObsInst4`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetObsInst5`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetObsInst6`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetObservations`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.pcConst1`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.pcConst3`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.pcConst5`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.realConstantJetCLM`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst10`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst11`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst3`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst4`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst5`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst6`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst7`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst8`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst9`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.subspaceObservations` and 34 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`BallPacking_Compactness_MarkedCurves`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Compactness/MarkedCurves.lean), [`BallPacking_Compactness_ResidualCauchy`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Compactness/ResidualCauchy.lean), [`BallPacking_Continuation_CompatibleHomotopy`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Continuation/CompatibleHomotopy.lean), [`BallPacking_Continuation_ParameterizedImplicit`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Continuation/ParameterizedImplicit.lean), [`BallPacking_Energy_ResidualEnergy`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Energy/ResidualEnergy.lean), [`BallPacking_Fredholm_FreeLinearization`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/FreeLinearization.lean), [`BallPacking_Fredholm_TranslationContinuity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/TranslationContinuity.lean).
--
--   **Imports.** It imports the published bundle `Def_BallPacking`; the bundles `OAIQ240Bp017`, `OAIQ240Bp018` and `OAIQ240Bp019` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ240Bp022`; the statements `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_actualFreeChart_contDiff`, `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_actualFreeChart_crSection_fderiv_eval`, `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_actualFreeChart_fderiv_fredholm`, `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_actualMarkedChart_contDiff`, `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_actualMarkedChart_derivative_eq_linearized`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualMarkedChart_derivative_eq_linearized_bp240`, `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_actualMarkedChart_value`, `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_completedFreeLinearized_fredholm`, `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_elliptic_freeTranslation_continuous`, `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_elliptic_freeTranslation_continuous_bp240`, `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_exists_jet_fredholm_observations_bp240`, `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_freeTranslation_observation_smoothAt`, `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_freeTranslation_observation_smoothAt_bp240`, `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_fullLineEquation_contDiff`, `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_fullLineEquation_local_chart_eq`, `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_isolatedFullLineZeros_compact`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.isolatedFullLineZeros_compact_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.translationVariation_observation_smooth_bp240`, `OAI_HigherDimensionalBallPacking_Rigidity_adapted_line_continuation_data`, `OAI.HigherDimensionalBallPacking.Rigidity.adapted_line_continuation_data_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.completed_line_closed_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.exact_line_homotopy_residual_energy_bound_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_zeroSet_compact_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.fullLineEndpointMap_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.fullLineProperPath_bp240` and `OAI_PackingSufficiencySupport_CubicModel_physicalArea_uniform`; the proofs of `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_actualFreeChart_contDiff`, `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_actualFreeChart_crSection_fderiv_eval`, `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_actualFreeChart_fderiv_fredholm`, `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_actualMarkedChart_contDiff`, `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_actualMarkedChart_derivative_eq_linearized`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualMarkedChart_derivative_eq_linearized_bp240`, `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_actualMarkedChart_value`, `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_completedFreeLinearized_fredholm`, `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_elliptic_freeTranslation_continuous`, `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_elliptic_freeTranslation_continuous_bp240`, `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_exists_jet_fredholm_observations_bp240`, `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_freeTranslation_observation_smoothAt`, `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_freeTranslation_observation_smoothAt_bp240`, `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_freeTranslation_principal_tendsto_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.fullLineEquation_contDiff_bp240`, `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_fullLineEquation_local_chart_eq`, `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_isolatedFullLineZeros_compact`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.isolatedFullLineZeros_compact_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.translationVariation_observation_smooth_bp240`, `OAI_HigherDimensionalBallPacking_Rigidity_adapted_line_continuation_data`, `OAI.HigherDimensionalBallPacking.Rigidity.adapted_line_continuation_data_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.completed_line_closed_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.exact_line_homotopy_residual_energy_bound_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.exact_line_local_energy_of_slope_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_line_czero_compactness_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_line_gradient_bound_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_line_uniform_defect_support_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_local_jet_cauchy_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_zeroSet_compact_bp240`, `OAI_HigherDimensionalBallPacking_Rigidity_fullLineEndpointMap`, `OAI.HigherDimensionalBallPacking.Rigidity.fullLineEndpointMap_bp240`, `OAI_HigherDimensionalBallPacking_Rigidity_fullLineProperPath`, `OAI_PackingSufficiencySupport_CubicModel_actual_cubic_representative_packing` and `OAI_PackingSufficiencySupport_CubicModel_physicalArea_uniform`.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp017
import Definitions.Def_OAIQ240Bp018
import Definitions.Def_OAIQ240Bp019

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_FreeLinearization
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped Topology BoundedContinuousFunction ContDiff
open Set Function Filter
namespace HolderCompletion
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance jetObsInst1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance jetObsInst2 : NormedSpace ℝ (COne ℂ E) := inferInstance

def jetObservations (s : Finset PlaneTest) : COne ℂ E →L[ℝ] (s → E) :=
  ContinuousLinearMap.pi (fun g => jetTestCLM g.val)

variable (S : Submodule ℝ (COne ℂ E))
local instance jetObsInst3 : NormedAddCommGroup S := inferInstance
local instance jetObsInst4 : NormedSpace ℝ S := inferInstance
local instance jetObsInst5 : AddCommGroup S := (jetObsInst3 S).toAddCommGroup
local instance jetObsInst6 : Module ℝ S := (jetObsInst4 S).toModule

def subspaceObservations (s : Finset PlaneTest) : S →L[ℝ] (s → E) :=
  (jetObservations s).comp S.subtypeL

end HolderCompletion

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.tcInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.tcInst2
local instance tcInst3 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance tcInst4_rf18ec1_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance tcInst5 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance tcInst6 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance tcInst7_rf18ec1_1 : NormedAddCommGroup (COne ℂ (E →L[ℝ] E)) := inferInstance
local instance tcInst8_rf18ec1_1 : NormedSpace ℝ (COne ℂ (E →L[ℝ] E)) := inferInstance
local instance tcInst9 : NormedAddCommGroup (HMap ℂ (E →L[ℝ] E)) := inferInstance
local instance tcInst10 : NormedSpace ℝ (HMap ℂ (E →L[ℝ] E)) := inferInstance

def translationError (A : COne ℂ (E →L[ℝ] E)) (a : E) (u : COne ℂ E) (t : ℂ) : HMap ℂ E :=
  bilinCLM (X := ℂ) (α := (1:ℝ)/3) (ContinuousLinearMap.apply (E := E) ℝ E).flip
    (holderTranslate t (jetValueCLM _ A)-jetValueCLM _ A)
    (const _ a+holderTranslate t (jetDirection 1 u))

variable {R S : ℝ} (hRS : R+1 ≤ S) (a : E)
  (u : freeModel (E := E) (Metric.closedBall (0:ℂ) R))
  (A : COne ℂ (E →L[ℝ] E))
  (hA : ∀ z ∉ Metric.closedBall (0:ℂ) S, cValue A z=complexI (E := E))
  (hcr : ∀ z, Complex.I • a+cDeriv u.val z Complex.I = cValue A z (a+cDeriv u.val z 1))
local instance tcInst11_rf18ec1_1 : NormedAddCommGroup (freeModel (E := E) (Metric.closedBall (0:ℂ) S)) := inferInstance
local instance tcInst12_rf18ec1_1 : NormedSpace ℝ (freeModel (E := E) (Metric.closedBall (0:ℂ) S)) := inferInstance
local instance tcInst13 : NormedAddCommGroup (supportedHolder (E := E) (Metric.closedBall (0:ℂ) S)) := inferInstance
local instance tcInst14 : NormedSpace ℝ (supportedHolder (E := E) (Metric.closedBall (0:ℂ) S)) := inferInstance

end
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance teInst1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance teInst2 : NormedSpace ℝ (COne ℂ E) := inferInstance

variable {J : E → E →L[ℝ] E} (hJ : BoundedCThree J) (b : ContDiffBump (0:ℂ)) (p a : E)
local instance teInst3_rf18ec1_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance teInst4_rf18ec1_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance teInst5 : NormedAddCommGroup (freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance teInst6 : NormedSpace ℝ (freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance

end

end HigherDimensionalBallPacking.Rigidity.HolderCompletion

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
section
variable {n : ℕ}
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst2
local instance srInst3 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance srInst4 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
local instance srInst5 : NormedAddCommGroup (HMap ℂ (Phase n)) := inferInstance
local instance srInst6 : NormedSpace ℝ (HMap ℂ (Phase n)) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst1
variable {J : Phase n → End n} (hJ : ContDiff ℝ ∞ J) (hc : ∀ x, Compatible (J x)) {B : ℝ}
  (hstd : ∀ x, B<‖x‖ → J x=standardJ n) (b : ContDiffBump (0:ℂ)) (p q : Phase n)
local instance srInst7 : NormedAddCommGroup (freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance srInst8 : NormedSpace ℝ (freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance srInst9 : AddCommGroup (freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (srInst7 (n := n) b).toAddCommGroup
local instance srInst10 : Module ℝ (freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (srInst8 (n := n) b).toModule
local instance srInst11 : TopologicalSpace (freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) :=
  (srInst7 (n := n) b).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

end
section
variable {n : ℕ}
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst4
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst6
variable {J : Phase n → End n} (hJ : ContDiff ℝ ∞ J) (hc : ∀ x, Compatible (J x)) {B : ℝ}
  (hstd : ∀ x, B < ‖x‖ → J x=standardJ n) (b : ContDiffBump (0:ℂ)) (p q : Phase n)
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst7
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst8
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst9
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst10
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst11
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst12
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst13
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst14
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst15
variable (u : markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut))
  (he : ∀ᶠ h in 𝓝 (0 : markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)),
    ∀ z : ℂ, b.rIn ≤ ‖z‖ → B < ‖markedCurve p q (u.val+h.val) z‖ ∧
      B < ‖truncatedCurve b p q u.val h.val z‖)

include he in
lemma marked_escape_base : ∀ z ∉ Metric.closedBall (0:ℂ) b.rOut, B < ‖markedCurve p q u.val z‖ := by
  intro z hz
  have hz' : b.rIn ≤ ‖z‖ := by
    have hz'' : b.rOut < ‖z‖ := by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hz
    exact (b.rIn_lt_rOut.trans hz'').le
  have hh := (he.self_of_nhds z hz').1
  simpa only [Submodule.coe_zero,add_zero] using hh

end

end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Energy_ResidualEnergy
attribute [-instance] _root_.OAI.HigherDimensionalBallPacking.Rigidity.squareMeasure_finite _root_.OAI.HigherDimensionalBallPacking.Rigidity.translatedSquare_finite _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
open HolderCompletion
variable {n : ℕ}

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.reInst2
def lineResidualEnergy (u : ℂ → Phase n) (z : Plane) : ℝ :=
  stdDot n (geometricResidual u (Complex.equivRealProdCLM.symm z))
    (geometricResidual u (Complex.equivRealProdCLM.symm z))


end
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Compactness_MarkedCurves
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open HolderCompletion
open scoped BoundedContinuousFunction
variable {n : ℕ}

def anchoredEnergyFamily (p : Phase n) (B θ : ℝ) : Set C(ℂ,Phase n) :=
  {u | u 0=p ∧ ContDiff ℝ ∞ u ∧
    ∀ c : ℂ,∀ k : ℕ,radialCurveEnergy (centeredCurve u c) ((1/16)^k)≤B*θ^k}

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.eljcInst2
local instance eljcInst3 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance eljcInst4 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance

end HigherDimensionalBallPacking.Rigidity

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open scoped BoundedContinuousFunction
open HolderCompletion
variable {n : ℕ}

local instance lrInst1 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance

local instance lrInst2_rf18ec1_1 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
local instance lrInst3_rf18ec1_1 : NormedAddCommGroup (HMap ℂ (Phase n)) := inferInstance
local instance lrInst4_rf18ec1_1 : NormedSpace ℝ (HMap ℂ (Phase n)) := inferInstance
def localResidual {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (c : ℂ) (r : ℝ) : HMap ℂ (Phase n) :=
  standardJetCR (cutoffCurveJet smallDiskBump (markedLocalCurve_smooth hu c r))

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Compactness_ResidualCauchy
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
open HolderCompletion
variable {n : ℕ}
local instance grcInst1 : NormedAddCommGroup (HMap ℂ (Phase n)) := inferInstance


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
open HolderCompletion
variable {n : ℕ}
local instance clcInst1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance clcInst2 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
open HolderCompletion
variable {n : ℕ}

local instance empInst1_rf18ec1_1 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance empInst2_rf18ec1_1 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
def exactMarkedZeroSet (J : Phase n → End n) (p q : Phase n) : Set (ℝ × COne ℂ (Phase n)) :=
  {v | v.1∈Icc (0:ℝ) 1 ∧ cValue v.2 0=0 ∧
    AffineLineCurve (lineHomotopy J v.1) p q (markedCurve p q v.2)}



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Continuation_CompatibleHomotopy
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
open HolderCompletion

variable {n : ℕ}
local instance fmp1 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance

local instance fmp2_rf18ec1_1 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
local instance fmp3_rf18ec1_1 : MetricSpace (COne ℂ (Phase n)) := (fmp1 (n := n)).toMetricSpace
def fullMarkedZeroSet (J : Phase n → End n) (p q : Phase n) : Set (ℝ × COne ℂ (Phase n)) :=
  {v | v.1∈Icc (0:ℝ) 1 ∧ (fullTime v.1,v.2)∈exactMarkedZeroSet J p q}

end HigherDimensionalBallPacking.Rigidity

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
section
section RealConstant
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
local instance pcConst1 : NormedAddCommGroup (COne ℂ F) := inferInstance
local instance pcConst2_rf18ec1_1 : NormedSpace ℝ (COne ℂ F) := inferInstance
local instance pcConst3 : NormedAddCommGroup (HMap ℂ F) := inferInstance
local instance pcConst4_rf18ec1_1 : NormedSpace ℝ (HMap ℂ F) := inferInstance
local instance pcConst5 : NormedAddCommGroup (HMap ℂ (ℂ →L[ℝ] F)) := inferInstance
local instance pcConst6_rf18ec1_1 : NormedSpace ℝ (HMap ℂ (ℂ →L[ℝ] F)) := inferInstance
lemma realConstantJet_norm (v : F) : ‖realConstantJet v‖≤‖v‖ := by
  change max ‖const _ v‖ ‖(0 : HMap ℂ (ℂ →L[ℝ] F))‖≤‖v‖
  rw [norm_zero]
  exact max_le (const_norm_le v) (norm_nonneg v)

def realConstantJetCLM : F →L[ℝ] COne ℂ F :=
  LinearMap.mkContinuous
    { toFun := realConstantJet
      map_add' := fun u v => by apply cValue_ext; intro z; rfl
      map_smul' := fun c v => by apply cValue_ext; intro z; rfl }
    1 (by intro v; change ‖realConstantJet v‖≤1*‖v‖; rw [one_mul]; exact realConstantJet_norm v)
end RealConstant

end
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmc1
local instance gmc2 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance gmc3 : NormedAddCommGroup (COne ℂ (ℝ × E)) := inferInstance
local instance gmc4 : NormedSpace ℝ (COne ℂ (ℝ × E)) := inferInstance
local instance gmc5 : NormedAddCommGroup (HMap ℂ (E →L[ℝ] E)) := inferInstance
local instance gmc6 : NormedSpace ℝ (HMap ℂ (E →L[ℝ] E)) := inferInstance

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmChartInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmChartInst2
local instance gmChartInst3 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance gmChartInst4 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance gmChartInst5 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance gmChartInst6 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance gmChartInst7 : NormedAddCommGroup (HMap ℂ (E →L[ℝ] E)) := inferInstance
local instance gmChartInst8 : NormedSpace ℝ (HMap ℂ (E →L[ℝ] E)) := inferInstance
variable (b b₁ : ContDiffBump (0:ℂ)) (p q : E)
local instance gmChartInst9 : NormedAddCommGroup (markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance gmChartInst10 : NormedSpace ℝ (markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance gmChartInst11_rf18ec1_1 : AddCommGroup (markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := (gmChartInst9 b).toAddCommGroup
local instance gmChartInst12_rf18ec1_1 : Module ℝ (markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := (gmChartInst10 b).toModule
local instance gmChartInst13 : NormedAddCommGroup (supportedHolder (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance gmChartInst14 : NormedSpace ℝ (supportedHolder (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance gmChartInst15_rf18ec1_1 : AddCommGroup (supportedHolder (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := (gmChartInst13 b).toAddCommGroup
local instance gmChartInst16_rf18ec1_1 : Module ℝ (supportedHolder (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := (gmChartInst14 b).toModule
local instance gmChartInst17 : NormedAddCommGroup (ℝ × markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance gmChartInst18 : NormedSpace ℝ (ℝ × markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance

end
section

variable {n : ℕ}
local instance glf1_rf18ec1_1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance glf2_rf18ec1_1 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace
local instance glf3_rf18ec1_1 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance glf4 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance

end

variable {n : ℕ}
variable (b : ContDiffBump (0:ℂ))

variable {J : Phase n → End n} (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
  (hJc : HasCompactSupport (fun x => J x-standardJ n))
  (b₁ : ContDiffBump (0:ℂ)) (p q : Phase n)
  (hb₁ : Metric.closedBall (0:ℂ) b.rOut⊆Metric.closedBall (0:ℂ) b₁.rIn)
  {B M δ : ℝ} (hstd : ∀ x,B<‖x‖ →J x=standardJ n) (hδ : 0<δ)
  (he : ∀ w∈markedBoundedDomain p q M δ,MarkedEscapeNeighborhood b p q w B)
  (hbound : ∀ v∈exactMarkedZeroSet J p q,v.2∈markedBoundedDomain p q M δ)

local instance gid1_rf18ec1_1 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance gid2_rf18ec1_1 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
local instance gid3_rf18ec1_1 : NormedAddCommGroup (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance gid4_rf18ec1_1 : NormedSpace ℝ (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance gid5_rf18ec1_1 : NormedAddCommGroup (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance gid6_rf18ec1_1 : NormedSpace ℝ (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
def isolatedFullLineZeros : Set (ℝ × markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) :=
  {v | v.1∈Icc (0:ℝ) 1 ∧ v.2∈fullLineDomain b p q M δ ∧
    fullLineEquation hJs hJ hJc b b₁ p q v=0}

end HigherDimensionalBallPacking.Rigidity.HolderCompletion

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
open HolderCompletion
section

variable {n : ℕ}
local instance lcdEnd1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance lcdEnd2 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace
local instance lcd1 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance lcd2 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance

variable (b : ContDiffBump (0:ℂ))
local instance lcd3 : NormedAddCommGroup (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance lcd4 : NormedSpace ℝ (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance lcd5 : NormedAddCommGroup (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance lcd6 : NormedSpace ℝ (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance

end
variable {n : ℕ} {J : Phase n → End n}
local instance alc1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance alc2 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end


