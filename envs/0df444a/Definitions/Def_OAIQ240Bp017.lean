-- Prove2me | Definitions.Def_OAIQ240Bp017
-- name    : OAIQ240Bp017
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T00:44:26.088131+00:00
-- url     : https://prove2.me/theorems/1ccb41a9-80f4-4c27-88ad-c011e9609158
-- title:
--   Definitions bundle OAIQ240Bp017 of the split of OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 73 declarations of OpenAI's Lean: 59 definitions, 1 inductive type or structure and 13 theorems. The definitions and types are `OAI.HigherDimensionalBallPacking.Rigidity.FullLineReady`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.FreeEscapeNeighborhood`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.IsIndexZeroFredholm`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.MarkedEscapeNeighborhood`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst1`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst10`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst11`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst12`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst13`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst14`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst15`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst2`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst3`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst4`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst5`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst6`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst7`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst8`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst9`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst1`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst19`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst2`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst23`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst3`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst7`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst7`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartNbInst1`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartNbInst5`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartNbInst9`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.cmn1`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.fullLineDomain`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.fullLineEquation`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.geometricResidual`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gle1`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gle2`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.globalChart`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.globalCoefficient`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.globalMarkedJet`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.globalNonlinearity`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.globalParameterJet` and 20 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`BallPacking_Campanato_TranslatedSquare`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Campanato/TranslatedSquare.lean), [`BallPacking_Compactness_ResidualCauchy`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Compactness/ResidualCauchy.lean), [`BallPacking_Continuation_CompatibleHomotopy`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Continuation/CompatibleHomotopy.lean), [`BallPacking_Continuation_ParameterizedImplicit`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Continuation/ParameterizedImplicit.lean), [`BallPacking_Energy_CircularEnergy`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Energy/CircularEnergy.lean), [`BallPacking_Fredholm_FrameFredholm`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/FrameFredholm.lean), [`BallPacking_Fredholm_FreeLinearization`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/FreeLinearization.lean), [`BallPacking_Fredholm_PointwiseMarkedCR`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/PointwiseMarkedCR.lean), [`BallPacking_Fredholm_TranslationContinuity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/TranslationContinuity.lean).
--
--   **Imports.** It imports the published bundle `Def_BallPacking`; the bundles `OAIQ240Bp014` and `OAIQ240Bp015` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ240Bp020` and `OAIQ240Bp021`; the statements `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_freeChart_hasFDerivAt_eval`, `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_freeChart_translation_zero_near`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeChart_translation_zero_near_bp240`, `OAI_HigherDimensionalBallPacking_Rigidity_ProperIndexZeroPath_cylinder_supplement`, `OAI.HigherDimensionalBallPacking.Rigidity.ProperIndexZeroPath.cylinder_supplement_bp240`, `OAI_HigherDimensionalBallPacking_Rigidity_ProperIndexZeroPath_endpoint_exists`, `OAI.HigherDimensionalBallPacking.Rigidity.ProperIndexZeroPath.endpoint_exists_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.exact_line_local_energy_of_slope_bp240`, `OAI_HigherDimensionalBallPacking_Rigidity_exact_marked_line_uniform_defect_support`, `OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_line_uniform_defect_support_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.exact_normalized_line_energy_bp240`, `OAI_HigherDimensionalBallPacking_Rigidity_indexZero_finite_stabilizer` and `OAI.HigherDimensionalBallPacking.Rigidity.indexZero_finite_stabilizer_bp240`; the proofs of `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_freeChart_hasFDerivAt_eval`, `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_freeChart_translation_zero_near`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeChart_translation_zero_near_bp240`, `OAI_HigherDimensionalBallPacking_Rigidity_ProperIndexZeroPath_cylinder_supplement`, `OAI.HigherDimensionalBallPacking.Rigidity.ProperIndexZeroPath.cylinder_supplement_bp240`, `OAI_HigherDimensionalBallPacking_Rigidity_ProperIndexZeroPath_endpoint_exists`, `OAI.HigherDimensionalBallPacking.Rigidity.ProperIndexZeroPath.endpoint_exists_bp240`, `OAI_HigherDimensionalBallPacking_Rigidity_equicontinuous_CR_derivative_bound`, `OAI_HigherDimensionalBallPacking_Rigidity_exact_marked_local_jet_cauchy`, `OAI.HigherDimensionalBallPacking.Rigidity.exact_normalized_line_energy_bp240`, `OAI_HigherDimensionalBallPacking_Rigidity_indexZero_finite_stabilizer`, `OAI.HigherDimensionalBallPacking.Rigidity.indexZero_finite_stabilizer_bp240` and `OAI.HigherDimensionalBallPacking.main_theorem`.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp014
import Definitions.Def_OAIQ240Bp015

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_FrameFredholm
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

local instance markedChartInst1_r6d9ad0_1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance markedChartInst2_r6d9ad0_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance markedChartInst3_r6d9ad0_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance markedChartInst4_r6d9ad0_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst6
local instance markedChartInst7_r6d9ad0_1 : NormedAddCommGroup (HMap ℂ (E →L[ℝ] E)) := inferInstance
local instance markedChartInst8_r6d9ad0_1 : NormedSpace ℝ (HMap ℂ (E →L[ℝ] E)) := inferInstance
local instance markedChartInst13_r6d9ad0_1 : NormedAddCommGroup (ℂ →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance markedChartInst14_r6d9ad0_1 : NormedSpace ℝ (ℂ →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
def markedDX (p q : E) (u h : COne ℂ E) : HMap ℂ E :=
  const _ (markedSlope p q u) - constHolderCLM (jetEval 1 h) + jetDirection 1 (u+h)



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_PointwiseMarkedCR
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion

section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable {K : Set ℂ}

variable {n : ℕ}
local instance chartDerInst7 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_FreeLinearization
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
namespace HolderCompletion
variable {n : ℕ}
local instance afInst1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance afInst2 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace
local instance afInst3 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance afInst4_r6d9ad0_1 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
local instance afInst5_r6d9ad0_1 : NormedAddCommGroup (HMap ℂ (Phase n)) := inferInstance
local instance afInst6_r6d9ad0_1 : NormedSpace ℝ (HMap ℂ (Phase n)) := inferInstance
variable {J : Phase n → End n} (hJ : ContDiff ℝ ∞ J) (hc : ∀ x, Compatible (J x)) {B : ℝ}
  (hstd : ∀ x, B < ‖x‖ → J x=standardJ n) (p q : Phase n) (u : COne ℂ (Phase n))
  {K : Set ℂ} (hK : IsCompact K) (he : ∀ z ∉ K, B < ‖markedCurve p q u z‖)
local instance afInst7 : NormedAddCommGroup (freeModel (E := Phase n) K) := inferInstance

local instance afInst8_r6d9ad0_1 : NormedSpace ℝ (freeModel (E := Phase n) K) := inferInstance
local instance afInst9_r6d9ad0_1 : AddCommGroup (freeModel (E := Phase n) K) := (afInst7 (n := n) (K := K)).toAddCommGroup
local instance afInst11_r6d9ad0_1 : NormedAddCommGroup (markedModel (E := Phase n) K) := inferInstance
local instance afInst12_r6d9ad0_1 : NormedSpace ℝ (markedModel (E := Phase n) K) := inferInstance
local instance afInst15_r6d9ad0_1 : NormedAddCommGroup (supportedHolder (E := Phase n) K) := inferInstance
local instance afInst16_r6d9ad0_1 : NormedSpace ℝ (supportedHolder (E := Phase n) K) := inferInstance
include hJ hstd in
theorem actualStructureBound : BoundedCThree J :=
  boundedCThree_of_compactPerturbation hJ (standardJ n) (compactPerturbation_of_outside_constant _ hstd)

variable (b : ContDiffBump (0:ℂ))
local instance afInst19 : NormedAddCommGroup (freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance afInst20_r6d9ad0_1 : NormedSpace ℝ (freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance afInst21_r6d9ad0_1 : AddCommGroup (freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (afInst19 (n := n) b).toAddCommGroup
local instance afInst23 : TopologicalSpace (freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (afInst19 (n := n) b).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

end HolderCompletion

end
section
open scoped Topology BoundedContinuousFunction ContDiff
open Set Function Filter MeasureTheory
namespace HolderCompletion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

local instance testInst1_r6d9ad0_1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance testInst2_r6d9ad0_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
def jetTestCLM (g : PlaneTest) : COne ℂ E →L[ℝ] E :=
  (planeTestCLM g).comp ((valueCLM _).comp (jetValueCLM _))

@[simp] lemma jetTest_value (g : PlaneTest) (u : COne ℂ E) :
    jetTestCLM g u = ∫ z, g.val z • cValue u z := rfl

end HolderCompletion

end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
namespace HolderCompletion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

local instance freeTransInst1_r6d9ad0_1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance freeTransInst2_r6d9ad0_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance freeTransInst3_r6d9ad0_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance freeTransInst4_r6d9ad0_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
def translationVariation (a : E) (u : COne ℂ E) (t : ℂ) : COne ℂ E :=
  constJet (t • a)+jetTranslate t u-u

omit [CompleteSpace E] in
@[simp] lemma translationVariation_value [CompleteSpace E] (a : E) (u : COne ℂ E) (t z : ℂ) :
    cValue (translationVariation a u t) z = t • a+cValue u (z+t)-cValue u z := rfl

omit [CompleteSpace E] in
@[simp] lemma translationVariation_deriv [CompleteSpace E] (a : E) (u : COne ℂ E) (t z : ℂ) :
    cDeriv (translationVariation a u t) z = cDeriv u (z+t)-cDeriv u z := by
  change (0 + cDeriv u (z+t))-cDeriv u z = _
  rw [zero_add]

end HolderCompletion

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_TranslationContinuity
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frozenTargetCoefficient_zero _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

variable (b : ContDiffBump (0:ℂ))

local instance feInst1_r6d9ad0_1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance feInst2_r6d9ad0_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance feInst3_r6d9ad0_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance feInst4_r6d9ad0_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance feInst5_r6d9ad0_1 : NormedAddCommGroup (freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance feInst6_r6d9ad0_1 : NormedSpace ℝ (freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
def FreeEscapeNeighborhood (p a : E) (u : COne ℂ E) (B : ℝ) : Prop :=
  ∀ᶠ v : freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut) in 𝓝 0,
    ∀ z, b.rIn≤‖z‖ → B<‖affineCurve p (complexSlope a) (u+v.val) z‖

end HigherDimensionalBallPacking.Rigidity.HolderCompletion

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
section
variable {n : ℕ}
local instance actFredInst1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance actFredInst2 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace
local instance actFredInst3 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance actFredInst4 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
local instance actFredInst5 : NormedAddCommGroup (HMap ℂ (Phase n)) := inferInstance
local instance actFredInst6 : NormedSpace ℝ (HMap ℂ (Phase n)) := inferInstance
variable {J : Phase n → End n} (hJ : ContDiff ℝ ∞ J) (hc : ∀ x, Compatible (J x)) {B : ℝ}
  (hstd : ∀ x, B < ‖x‖ → J x=standardJ n) (b : ContDiffBump (0:ℂ)) (p q : Phase n)
local instance actFredInst7 : NormedAddCommGroup (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance actFredInst8 : NormedSpace ℝ (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance actFredInst9 : AddCommGroup (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (actFredInst7 (n := n) b).toAddCommGroup
local instance actFredInst10 : Module ℝ (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (actFredInst8 (n := n) b).toModule
local instance actFredInst11 : TopologicalSpace (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) :=
  (actFredInst7 (n := n) b).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
local instance actFredInst12 : NormedAddCommGroup (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance actFredInst13 : NormedSpace ℝ (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance actFredInst14 : AddCommGroup (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (actFredInst12 (n := n) b).toAddCommGroup
local instance actFredInst15 : Module ℝ (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (actFredInst13 (n := n) b).toModule
variable (u : markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut))
  (he : ∀ᶠ h in 𝓝 (0 : markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)),
    ∀ z : ℂ, b.rIn ≤ ‖z‖ → B < ‖markedCurve p q (u.val+h.val) z‖ ∧
      B < ‖truncatedCurve b p q u.val h.val z‖)

def IsIndexZeroFredholm {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (D : X →L[ℝ] Y) : Prop :=
  D.IsFredholm ∧ Module.finrank ℝ D.ker = Module.finrank ℝ (Y ⧸ D.range)

end
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance chartNbInst1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance chartNbInst2_r6d9ad0_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance chartNbInst3_r6d9ad0_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance chartNbInst4_r6d9ad0_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance chartNbInst5 (K : Set ℂ) : NormedAddCommGroup (markedModel (E := E) K) := inferInstance
local instance chartNbInst6_r6d9ad0_1 (K : Set ℂ) : NormedSpace ℝ (markedModel (E := E) K) := inferInstance
local instance chartNbInst7_r6d9ad0_1 (K : Set ℂ) : AddCommGroup (markedModel (E := E) K) := (chartNbInst5 K).toAddCommGroup
local instance chartNbInst9 (K : Set ℂ) : TopologicalSpace (markedModel (E := E) K) :=
  (chartNbInst5 K).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

def MarkedEscapeNeighborhood (b : ContDiffBump (0:ℂ)) (p q : E) (u : COne ℂ E) (B : ℝ) : Prop :=
  ∀ᶠ h in 𝓝 (0 : markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)),
    ∀ z : ℂ, b.rIn ≤ ‖z‖ → B < ‖markedCurve p q (u+h.val) z‖ ∧
      B < ‖truncatedCurve b p q u h.val z‖

end

variable {n : ℕ}

local instance gcInst1_r6d9ad0_1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance gcInst2_r6d9ad0_1 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace
local instance gcInst3_r6d9ad0_1 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance gcInst4_r6d9ad0_1 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
local instance gcInst5_r6d9ad0_1 : NormedAddCommGroup (HMap ℂ (Phase n)) := inferInstance
local instance gcInst6_r6d9ad0_1 : NormedSpace ℝ (HMap ℂ (Phase n)) := inferInstance
local instance gcInst7_r6d9ad0_1 (K : Set ℂ) : NormedAddCommGroup (markedModel (E := Phase n) K) := inferInstance
local instance gcInst8_r6d9ad0_1 (K : Set ℂ) : NormedSpace ℝ (markedModel (E := Phase n) K) := inferInstance
local instance gcInst9_r6d9ad0_1 (K : Set ℂ) : NormedAddCommGroup (supportedHolder (E := Phase n) K) := inferInstance
local instance gcInst10_r6d9ad0_1 (K : Set ℂ) : NormedSpace ℝ (supportedHolder (E := Phase n) K) := inferInstance
def geometricResidual (u : ℂ → Phase n) (z : ℂ) : Phase n :=
  fderiv ℝ u z Complex.I-Complex.I • fderiv ℝ u z 1

lemma geometricResidual_smooth {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (geometricResidual u) := by
  have hd := hu.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hx : ContDiff ℝ ∞ (fun z => fderiv ℝ u z 1) := hd.clm_apply contDiff_const
  have hy : ContDiff ℝ ∞ (fun z => fderiv ℝ u z Complex.I) := hd.clm_apply contDiff_const
  have hI : ContDiff ℝ ∞ (fun _ : ℂ => Complex.I) := contDiff_const
  exact hy.sub (hI.smul hx)

end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Energy_CircularEnergy
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
variable {n : ℕ}

def angularCurveFlux (u : ℂ → Phase n) (z : Plane) : ℝ :=
  planarPullback (realCurve u) (stdOmega n) z (planeRotation z)


end
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
variable {n : ℕ}


def centeredCurve (u : ℂ → Phase n) (c : ℂ) (z : ℂ) : Phase n := u (z+c)



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Campanato_TranslatedSquare
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
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
variable {n : ℕ}


def slopeScale (a : Phase n) : ℝ := (Real.sqrt (stdDot n a a))⁻¹


end
open scoped ContDiff Topology
open Set Function Filter MeasureTheory



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Compactness_ResidualCauchy
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
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

local instance grcInst1_r6d9ad0_1 : NormedAddCommGroup (HMap ℂ (Phase n)) := inferInstance
local instance grcInst2_r6d9ad0_1 : NormedSpace ℝ (HMap ℂ (Phase n)) := inferInstance
def geometricHolder {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u)
    (hc : HasCompactSupport (geometricResidual u)) : HMap ℂ (Phase n) :=
  jetValueCLM _ (ofBoundedCThree (boundedCThree_of_compactSupport (geometricResidual_smooth hu) hc))

@[simp] lemma geometricHolder_value {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u)
    (hc : HasCompactSupport (geometricResidual u)) (z : ℂ) :
    valueCLM _ (geometricHolder hu hc) z=geometricResidual u z := rfl


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
open HolderCompletion



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Continuation_CompatibleHomotopy
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter
section
variable {n : ℕ}
local instance ihInst1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance ihInst2 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace

lemma interpolateJ_standard_initial {t : ℝ} (ht : -1<t ∧ t≤1) : interpolateJ (standardJ n) t=standardJ n := by
  have ha : 0<1+t := by linarith [ht.1]
  have hb : 0≤1-t := by linarith [ht.2]
  obtain ⟨e,he⟩ := cayleyP_invertible (compatible_standardJ n) ha hb
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨x,rfl⟩ := e.surjective v
  change standardJ n (cayleyOperator (standardJ n) (1+t) (1-t) ((e : End n) x)) =
    standardJ n ((e : End n) x)
  rw [he,cayleyOperator_on_denominator ⟨e,he⟩]
  congr 1
  change (1+t) • relativeOperator (standardJ n) x+(1-t) • x =
    (1-t) • relativeOperator (standardJ n) x+(1+t) • x
  simp only [relativeOperator_apply,standardJ_sq,neg_neg]
  module

lemma contDiffAt_interpolateJ_initial {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {J : D → End n} {t : D → ℝ} {x : D}
    (hJs : ContDiffAt ℝ ∞ J x) (hts : ContDiffAt ℝ ∞ t x)
    (hJ : Compatible (J x)) (ht : -1<t x ∧ t x≤1) :
    ContDiffAt ℝ ∞ (fun y => interpolateJ (J y) (t y)) x := by
  have hA : ContDiffAt ℝ ∞ (fun y => relativeOperator (J y)) x :=
    (contDiffAt_const.clm_comp hJs).neg
  have ha : ContDiffAt ℝ ∞ (fun y => 1+t y) x := contDiffAt_const.add hts
  have hb : ContDiffAt ℝ ∞ (fun y => 1-t y) x := contDiffAt_const.sub hts
  have hP : ContDiffAt ℝ ∞ (fun y => cayleyP (J y) (1+t y) (1-t y)) x :=
    (ha.smul hA).add (hb.smul contDiffAt_const)
  have hQ : ContDiffAt ℝ ∞ (fun y => cayleyP (J y) (1-t y) (1+t y)) x :=
    (hb.smul hA).add (ha.smul contDiffAt_const)
  have hQi := cayleyP_invertible hJ (show 0<1+t x by linarith [ht.1]) (show 0≤1-t x by linarith [ht.2])
  have hI : ContDiffAt ℝ ∞ (fun y => (cayleyP (J y) (1-t y) (1+t y)).inverse) x :=
    ContDiffAt.comp x (g := ContinuousLinearMap.inverse)
      (ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse (n := ∞) hQi) hQ
  exact contDiffAt_const.clm_comp (hP.clm_comp hI)

end

variable {n : ℕ}
local instance ghInst1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance ghInst2 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace

def fullCoefficient (J : Phase n → End n) (v : ℝ × Phase n) : End n :=
  fullTimeBump v.1 • (interpolateJ (J v.2) (fullTime v.1)-standardJ n)

variable {J : Phase n → End n} (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x, Compatible (J x))
include hJs hJ in
lemma fullCoefficient_smooth : ContDiff ℝ ∞ (fullCoefficient J) := by
  apply contDiff_iff_contDiffAt.mpr
  intro v
  have ht : -1<fullTime v.1 ∧ fullTime v.1≤1 :=
    ⟨lt_of_lt_of_le (by norm_num) (fullTime_range v.1).1,(fullTime_range v.1).2⟩
  have hh := contDiffAt_interpolateJ_initial (hJs.contDiffAt.comp v contDiffAt_snd)
    (fullTime_smooth.contDiffAt.comp v contDiffAt_fst) (hJ v.2) ht
  exact (fullTimeBump.contDiff.contDiffAt.comp v contDiffAt_fst).smul (hh.sub contDiffAt_const)

lemma fullCoefficient_compact (hJc : HasCompactSupport (fun x => J x-standardJ n)) :
    HasCompactSupport (fullCoefficient J) := by
  apply (fullTimeBump.hasCompactSupport.prod hJc).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ (isClosed_tsupport _ |>.prod (isClosed_tsupport _))
  intro v hv
  constructor
  · by_contra hn
    have hz := image_eq_zero_of_notMem_tsupport hn
    apply hv
    change fullTimeBump v.1 • (interpolateJ (J v.2) (fullTime v.1)-standardJ n)=0
    rw [hz,zero_smul]
  · by_contra hn
    have hz : J v.2=standardJ n := sub_eq_zero.mp
      (image_eq_zero_of_notMem_tsupport (f := fun x => J x-standardJ n) hn)
    apply hv
    change fullTimeBump v.1 • (interpolateJ (J v.2) (fullTime v.1)-standardJ n)=0
    rw [hz,interpolateJ_standard_initial
      ⟨lt_of_lt_of_le (by norm_num) (fullTime_range _).1,(fullTime_range _).2⟩,sub_self,smul_zero]

end HigherDimensionalBallPacking.Rigidity

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance cmn1 : NormedAddCommGroup (COne ℂ E) := inferInstance

local instance cmn2_r6d9ad0_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
def markedBoundedDomain (p q : E) (M δ : ℝ) : Set (COne ℂ E) :=
  {w | ‖w‖<M ∧ δ<‖markedSlope p q w‖}

end HigherDimensionalBallPacking.Rigidity.HolderCompletion

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
section
section RealConstant
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance pcConst1_r6d9ad0_1 : NormedAddCommGroup (COne ℂ F) := inferInstance
local instance pcConst2_r6d9ad0_1 : NormedSpace ℝ (COne ℂ F) := inferInstance
local instance pcConst3_r6d9ad0_1 : NormedAddCommGroup (HMap ℂ F) := inferInstance
local instance pcConst4_r6d9ad0_1 : NormedSpace ℝ (HMap ℂ F) := inferInstance
local instance pcConst5_r6d9ad0_1 : NormedAddCommGroup (HMap ℂ (ℂ →L[ℝ] F)) := inferInstance
local instance pcConst6_r6d9ad0_1 : NormedSpace ℝ (HMap ℂ (ℂ →L[ℝ] F)) := inferInstance
def realConstantJet (v : F) : COne ℂ F :=
  ⟨(const _ v,0),fun z => hasFDerivAt_const v z⟩
@[simp] lemma realConstantJet_value (v : F) (z : ℂ) : cValue (realConstantJet v) z=v := rfl
end RealConstant

end
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance gmc1 : NormedAddCommGroup (COne ℂ E) := inferInstance
variable (b₁ : ContDiffBump (0:ℂ)) (p q : E)

local instance gmc2_r6d9ad0_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance gmc3_r6d9ad0_1 : NormedAddCommGroup (COne ℂ (ℝ × E)) := inferInstance
local instance gmc4_r6d9ad0_1 : NormedSpace ℝ (COne ℂ (ℝ × E)) := inferInstance
local instance gmc5_r6d9ad0_1 : NormedAddCommGroup (HMap ℂ (E →L[ℝ] E)) := inferInstance
local instance gmc6_r6d9ad0_1 : NormedSpace ℝ (HMap ℂ (E →L[ℝ] E)) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmc7
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmc8
def globalMarkedJet (w : COne ℂ E) : COne ℂ E :=
  realConstantJet p+cutoffSlope b₁ (markedSlope p q w)+w

def globalParameterJet (v : ℝ × COne ℂ E) : COne ℂ (ℝ × E) :=
  realConstantJet (v.1,0)+
    mapJetBilinear (D := ℂ) (E := E) (F := ℝ × E)
      (ContinuousLinearMap.inr ℝ ℝ E) (globalMarkedJet b₁ p q v.2)

omit [CompleteSpace E] in
lemma global_zero_derivative_bound [CompleteSpace E] (z : ℂ) :
    ‖fderiv ℝ (fun _ : ℂ => (0 : ℝ × E)) z‖≤0 := by simp

variable {P : ℝ × E → E →L[ℝ] E} (hP : BoundedCThree P)
def globalCoefficient (v : ℝ × COne ℂ E) : HMap ℂ (E →L[ℝ] E) :=
  superpose hP (differentiable_const (0 : ℝ × E)) (le_refl (0:ℝ))
    (global_zero_derivative_bound (E := E)) (globalParameterJet b₁ p q v)

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
variable (b b₁ : ContDiffBump (0:ℂ)) (p q : E)
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmChartInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmChartInst2
local instance gmChartInst3_r6d9ad0_1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance gmChartInst4_r6d9ad0_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance gmChartInst5_r6d9ad0_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance gmChartInst6_r6d9ad0_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance gmChartInst7_r6d9ad0_1 : NormedAddCommGroup (HMap ℂ (E →L[ℝ] E)) := inferInstance
local instance gmChartInst8_r6d9ad0_1 : NormedSpace ℝ (HMap ℂ (E →L[ℝ] E)) := inferInstance
local instance gmChartInst9_r6d9ad0_1 : NormedAddCommGroup (markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance gmChartInst10_r6d9ad0_1 : NormedSpace ℝ (markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance gmChartInst13_r6d9ad0_1 : NormedAddCommGroup (supportedHolder (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance gmChartInst14_r6d9ad0_1 : NormedSpace ℝ (supportedHolder (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance gmChartInst17_r6d9ad0_1 : NormedAddCommGroup (ℝ × markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance gmChartInst18_r6d9ad0_1 : NormedSpace ℝ (ℝ × markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
variable {P : ℝ × E → E →L[ℝ] E} (hP : BoundedCThree P)

def globalNonlinearity (v : ℝ × markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) : HMap ℂ E :=
  bilinCLM (X := ℂ) (α := (1:ℝ)/3) (ContinuousLinearMap.apply (E := E) ℝ E).flip
    (globalCoefficient b₁ p q hP (v.1,v.2.val)) (markedDX p q 0 v.2.val)

def globalChart (v : ℝ × markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) :
    supportedHolder (E := E) (Metric.closedBall (0:ℂ) b.rOut) :=
  (markedCR (E := E) (K := Metric.closedBall (0:ℂ) b.rOut)) v.2-
    supportedSourceCutoff b (globalNonlinearity b b₁ p q hP v)

end
section
variable {n : ℕ}
local instance gle1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance gle2 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace
local instance gle3_r6d9ad0_1 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance gle4_r6d9ad0_1 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
local instance gle5_r6d9ad0_1 : NormedAddCommGroup (HMap ℂ (Phase n)) := inferInstance
local instance gle6_r6d9ad0_1 : NormedSpace ℝ (HMap ℂ (Phase n)) := inferInstance
variable {J : Phase n → End n} (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
  (hJc : HasCompactSupport (fun x => J x-standardJ n))
include hJs hJ hJc in
theorem fullCoefficientBound : BoundedCThree (fullCoefficient J) :=
  boundedCThree_of_compactSupport (fullCoefficient_smooth hJs hJ) (fullCoefficient_compact hJc)
variable (b b₁ : ContDiffBump (0:ℂ)) (p q : Phase n)

local instance gle7_r6d9ad0_1 : NormedAddCommGroup (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance gle8_r6d9ad0_1 : NormedSpace ℝ (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance gle9_r6d9ad0_1 : NormedAddCommGroup (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance gle10_r6d9ad0_1 : NormedSpace ℝ (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
def fullLineEquation := globalChart b b₁ p q (fullCoefficientBound hJs hJ hJc)

end

variable {n : ℕ}
variable (b : ContDiffBump (0:ℂ))

local instance gid1_r6d9ad0_1 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance gid2_r6d9ad0_1 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
local instance gid3_r6d9ad0_1 : NormedAddCommGroup (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance gid4_r6d9ad0_1 : NormedSpace ℝ (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance gid5_r6d9ad0_1 : NormedAddCommGroup (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance gid6_r6d9ad0_1 : NormedSpace ℝ (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
def fullLineDomain (p q : Phase n) (M δ : ℝ) :
    Set (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) :=
  {w | w.val∈markedBoundedDomain p q M δ}

end HigherDimensionalBallPacking.Rigidity.HolderCompletion

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
open HolderCompletion
section

structure ProperIndexZeroPath {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (F : ℝ × X → Y) (U : Set X) : Prop where
  domain_open : IsOpen U
  origin_mem : (0:X)∈U
  smooth : ContDiff ℝ ∞ F
  initial : ∃ L : X ≃L[ℝ] Y,∀ x,F (0,x)=L x
  zeroSet_compact : IsCompact {v : ℝ × X | v.1∈Icc (0:ℝ) 1 ∧ v.2∈U ∧ F v=0}
  fredholm : ∀ t∈Icc (0:ℝ) 1,∀ x∈U,IsIndexZeroFredholm (fderiv ℝ (fun y => F (t,y)) x)

end
section

variable {n : ℕ} {J : Phase n → End n}
local instance lcdFinal1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance lcdFinal2 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace
local instance lcdFinal3 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance lcdFinal4 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
variable (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
  (hJc : HasCompactSupport (fun x => J x-standardJ n)) (p q : Phase n)
def FullLineReady (b b₁ : ContDiffBump (0:ℂ)) (M δ : ℝ) : Prop :=
  ProperIndexZeroPath (fullLineEquation hJs hJ hJc b b₁ p q) (fullLineDomain b p q M δ) ∧
    (∀ w∈fullLineDomain b p q M δ,fullLineEquation hJs hJ hJc b b₁ p q (1,w)=0 →
      AffineLineCurve J p q (markedCurve p q w.val))

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end


