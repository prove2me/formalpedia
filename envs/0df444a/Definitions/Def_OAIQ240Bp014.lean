-- Prove2me | Definitions.Def_OAIQ240Bp014
-- name    : OAIQ240Bp014
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T00:32:07.684946+00:00
-- url     : https://prove2.me/theorems/be38277e-e667-4aeb-9360-8d1fa1a6c02b
-- title:
--   Definitions bundle OAIQ240Bp014 of the split of OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 55 declarations of OpenAI's Lean: 34 definitions and 21 theorems. The definitions and types are `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compLinInst1`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compLinInst2`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compLinInst3`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compLinInst4`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedDStructure`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedDX`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedQ`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveMarkCoefficientHolder`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveZeroOrderHolder`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeFredInst12`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeFredInst14`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeFredInst18`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeFredInst3`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeFredInst4`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeFredInst6`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeFredInst8`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freePrincipal`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeZeroOrder`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frozenCurve`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.geoLinInst4`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ljcInst6`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedDerivEval`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedDerivativeVariation`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedVariation`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ptCRInst10`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ptCRInst11`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ptCRInst3`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ptCRInst4`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ptCRInst7`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ptCRInst8`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ptCRInst9`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.supportedEval`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.truncatedCoefficient`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.truncatedCurve`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`BallPacking_Compactness_FrozenCR`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Compactness/FrozenCR.lean), [`BallPacking_Compactness_JetCauchy`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Compactness/JetCauchy.lean), [`BallPacking_Fredholm_FrameFredholm`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/FrameFredholm.lean), [`BallPacking_Fredholm_PointwiseMarkedCR`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/PointwiseMarkedCR.lean), [`BallPacking_Holder_MarkedFrame`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Holder/MarkedFrame.lean), [`BallPacking_Holder_MarkedJets`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Holder/MarkedJets.lean).
--
--   **Imports.** It imports the published bundle `Def_BallPacking`; the bundles `OAIQ240Bp011` and `OAIQ240Bp012` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ240Bp017`, `OAIQ240Bp018` and `OAIQ240Bp019`; the proof of `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.disk_nonlinear_jet_cauchy_bp240`.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp011
import Definitions.Def_OAIQ240Bp012

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_MarkedJets
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

variable {K : Set ℂ} (hK : IsCompact K)

local instance markedAffineInst1_rcbd1d2_1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance markedAffineInst2_rcbd1d2_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance markedAffineInst3_rcbd1d2_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance markedAffineInst4_rcbd1d2_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance markedAffineInst5_rcbd1d2_1 : NormedAddCommGroup (markedModel (E := E) K) := inferInstance
local instance markedAffineInst6_rcbd1d2_1 : NormedSpace ℝ (markedModel (E := E) K) := inferInstance
local instance markedAffineInst7_rcbd1d2_1 : NormedAddCommGroup (supportedHolder (E := E) K) := inferInstance
local instance markedAffineInst8_rcbd1d2_1 : NormedSpace ℝ (supportedHolder (E := E) K) := inferInstance
omit [CompleteSpace E] in
lemma markedCurve_hasFDerivAt (p q : E) (u : COne ℂ E) (z : ℂ) :
    HasFDerivAt (markedCurve p q u) (complexSlope (markedSlope p q u)+cDeriv u z) z :=
  affineCurve_hasFDerivAt p (complexSlope (markedSlope p q u)) u z

omit [CompleteSpace E] in
lemma markedCurve_fderiv (p q : E) (u : COne ℂ E) (z : ℂ) :
    fderiv ℝ (markedCurve p q u) z = complexSlope (markedSlope p q u)+cDeriv u z :=
  (markedCurve_hasFDerivAt p q u z).fderiv



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_MarkedFrame
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

variable (b : ContDiffBump (0:ℂ))

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineCutInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineCutInst2
local instance affineCutInst3_rcbd1d2_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance affineCutInst4_rcbd1d2_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineCutInst5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineCutInst6
def truncatedCurve (p q : E) (u h : COne ℂ E) (z : ℂ) : E :=
  affineCurve p (complexSlope (markedSlope p q u)) (u+truncateShift b h) z


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Compactness_JetCauchy
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
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ljcInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ljcInst2
local instance ljcInst3_rcbd1d2_1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance ljcInst4_rcbd1d2_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance ljcInst5_rcbd1d2_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance ljcInst6 : NormedSpace ℝ (HMap ℂ E) := inferInstance


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Compactness_FrozenCR
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedStructureJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveMarkCoefficient_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveZeroOrder_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothAlongJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothMarkedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.normalizedPrimitive_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.realCurve_zero _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {n : ℕ}

local instance fcrInst1_rcbd1d2_1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance fcrInst2_rcbd1d2_1 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace
@[simp] lemma frozenTargetCoefficient_zero (J : Phase n → End n) (x : Phase n) :
    frozenTargetCoefficient J x 0=0 := by
  simp only [frozenTargetCoefficient,map_zero,add_zero,sub_self,
    ContinuousLinearMap.comp_zero,ContinuousLinearMap.zero_comp]

def frozenCurve (J : Phase n → End n) (x : Phase n) (u : ℂ → Phase n) (z : ℂ) : Phase n :=
  compatibleFrame (J x) (u z-x)

lemma frozenCurve_smooth {J : Phase n → End n} (x : Phase n) {u : ℂ → Phase n}
    (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (frozenCurve J x u) :=
  (compatibleFrame (J x)).contDiff.comp (hu.sub contDiff_const)

end HigherDimensionalBallPacking.Rigidity.HolderCompletion

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_FrameFredholm
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frozenTargetCoefficient_zero _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.holderTranslate_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetTranslate_deriv _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetTranslate_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.normalizedPrimitive_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.realCurve_zero _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
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
variable {n : ℕ}
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.geoLinInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.geoLinInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.geoLinInst3
local instance geoLinInst4 : NormedSpace ℝ (Phase n →L[ℝ] End n) := ContinuousLinearMap.toNormedSpace

local instance geoLinInst5_rcbd1d2_1 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance geoLinInst6_rcbd1d2_1 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
local instance geoLinInst7_rcbd1d2_1 : NormedAddCommGroup (HMap ℂ (Phase n)) := inferInstance
local instance geoLinInst8_rcbd1d2_1 : NormedSpace ℝ (HMap ℂ (Phase n)) := inferInstance
local instance geoLinInst9_rcbd1d2_1 : NormedAddCommGroup (HMap ℂ (End n)) := inferInstance
local instance geoLinInst10_rcbd1d2_1 : NormedSpace ℝ (HMap ℂ (End n)) := inferInstance
lemma curveZeroOrder_smooth {J : Phase n → End n} (hJ : ContDiff ℝ ∞ J)
    {f : ℂ → Phase n} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (curveZeroOrder J f) := by
  have hDJ := (hJ.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp hf
  have hdF : ContDiff ℝ ∞ (fun z => fderiv ℝ f z 1) :=
    (hf.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const
  let L := (ContinuousLinearMap.flipₗᵢ ℝ (Phase n) (Phase n) (Phase n)).toContinuousLinearEquiv.toContinuousLinearMap
  exact (L.contDiff.comp hDJ).clm_apply hdF

lemma curveMarkCoefficient_smooth {J : Phase n → End n} (hJ : ContDiff ℝ ∞ J)
    {f : ℂ → Phase n} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (curveMarkCoefficient J f) := by
  have hsmul : ContDiff ℝ ∞ (fun z : ℂ => (ContinuousLinearMap.lsmul ℝ ℂ (E := Phase n)) z) :=
    (ContinuousLinearMap.lsmul ℝ ℂ (E := Phase n)).contDiff
  exact ((hJ.comp hf).sub contDiff_const).add ((curveZeroOrder_smooth hJ hf).clm_comp hsmul)

variable {J : Phase n → End n} (hJ : ContDiff ℝ ∞ J) (hc : ∀ x, Compatible (J x))
  {f : ℂ → Phase n} (hf : ContDiff ℝ ∞ f) {B : ℝ}
  (hstd : ∀ x, B < ‖x‖ → J x = standardJ n) {K : Set ℂ} (hK : IsCompact K)
  (hesc : ∀ z ∉ K, B < ‖f z‖)

local instance geoLinInst11_rcbd1d2_1 : NormedAddCommGroup (markedModel (E := Phase n) K) := inferInstance
local instance geoLinInst12_rcbd1d2_1 : NormedSpace ℝ (markedModel (E := Phase n) K) := inferInstance
local instance geoLinInst13_rcbd1d2_1 : NormedAddCommGroup (supportedHolder (E := Phase n) K) := inferInstance
local instance geoLinInst14_rcbd1d2_1 : NormedSpace ℝ (supportedHolder (E := Phase n) K) := inferInstance
include hstd hesc in
lemma curveZeroOrder_zero_outside : ∀ z ∉ K, curveZeroOrder J f z = 0 := by
  intro z hz
  apply ContinuousLinearMap.ext
  intro v
  rw [curveZeroOrder_apply,fderiv_standard_outside hstd (hesc z hz)]
  rfl

include hstd hesc in
lemma curveMarkCoefficient_zero_outside : ∀ z ∉ K, curveMarkCoefficient J f z = 0 := by
  intro z hz
  rw [curveMarkCoefficient,hstd _ (hesc z hz),sub_self,zero_add,
    curveZeroOrder_zero_outside hstd hesc z hz,ContinuousLinearMap.zero_comp]

include hstd hK hesc in
lemma curveZeroOrder_compact : HasCompactSupport (curveZeroOrder J f) := by
  apply HasCompactSupport.of_support_subset_isCompact hK
  intro z hz
  by_contra hzK
  exact hz (curveZeroOrder_zero_outside hstd hesc z hzK)

include hstd hK hesc in
lemma curveMarkCoefficient_compact : HasCompactSupport (curveMarkCoefficient J f) := by
  apply HasCompactSupport.of_support_subset_isCompact hK
  intro z hz
  by_contra hzK
  exact hz (curveMarkCoefficient_zero_outside hstd hesc z hzK)

def curveZeroOrderHolder : HMap ℂ (End n) :=
  jetValueCLM _ (ofBoundedCThree (boundedCThree_of_compactSupport (curveZeroOrder_smooth hJ hf)
    (curveZeroOrder_compact hstd hK hesc)))

def curveMarkCoefficientHolder : HMap ℂ (End n) :=
  jetValueCLM _ (ofBoundedCThree (boundedCThree_of_compactSupport (curveMarkCoefficient_smooth hJ hf)
    (curveMarkCoefficient_compact hstd hK hesc)))

@[simp] lemma curveZeroOrderHolder_value (z : ℂ) :
    valueCLM _ (curveZeroOrderHolder hJ hf hstd hK hesc) z = curveZeroOrder J f z := rfl

@[simp] lemma curveMarkCoefficientHolder_value (z : ℂ) :
    valueCLM _ (curveMarkCoefficientHolder hJ hf hstd hK hesc) z = curveMarkCoefficient J f z := rfl


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

local instance markedChartInst1_rcbd1d2_1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance markedChartInst2_rcbd1d2_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance markedChartInst3_rcbd1d2_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance markedChartInst4_rcbd1d2_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst6
local instance markedChartInst7_rcbd1d2_1 : NormedAddCommGroup (HMap ℂ (E →L[ℝ] E)) := inferInstance
local instance markedChartInst8_rcbd1d2_1 : NormedSpace ℝ (HMap ℂ (E →L[ℝ] E)) := inferInstance
local instance markedChartInst13_rcbd1d2_1 : NormedAddCommGroup (ℂ →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance markedChartInst14_rcbd1d2_1 : NormedSpace ℝ (ℂ →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
variable {P : E → E →L[ℝ] E} (hP : BoundedCThree P) (b : ContDiffBump (0:ℂ))

def truncatedCoefficient (p q : E) (u h : COne ℂ E) : HMap ℂ (E →L[ℝ] E) :=
  structureAlong hP p (complexSlope (markedSlope p q u)) (u+truncateShift b h)

omit [CompleteSpace E] in
@[simp] lemma truncatedCoefficient_value [CompleteSpace E] (p q : E) (u h : COne ℂ E) (z : ℂ) :
    valueCLM _ (truncatedCoefficient hP b p q u h) z = P (truncatedCurve b p q u h z) := rfl



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_PointwiseMarkedCR
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frozenTargetCoefficient_zero _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.holderTranslate_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetTranslate_deriv _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetTranslate_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.normalizedPrimitive_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.realCurve_zero _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
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
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ptCRInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ptCRInst2
local instance ptCRInst3 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance ptCRInst4 : NormedSpace ℝ (COne ℂ E) := inferInstance
variable {K : Set ℂ}
local instance ptCRInst5_rcbd1d2_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance ptCRInst6_rcbd1d2_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance ptCRInst7 : NormedAddCommGroup (markedModel (E := E) K) := inferInstance
local instance ptCRInst8 : NormedSpace ℝ (markedModel (E := E) K) := inferInstance
local instance ptCRInst9 : AddCommGroup (markedModel (E := E) K) := ptCRInst7.toAddCommGroup
local instance ptCRInst10 : Module ℝ (markedModel (E := E) K) := ptCRInst8.toModule
local instance ptCRInst11 : TopologicalSpace (markedModel (E := E) K) :=
  ptCRInst7.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

def markedDerivEval (z v : ℂ) : markedModel (E := E) K →L[ℝ] E :=
  ((BoundedContinuousFunction.evalCLM ℝ z).comp (valueCLM _)).comp
    ((jetDirection v).comp (markedModel (E := E) K).subtypeL)

omit [CompleteSpace E] in
@[simp] lemma markedDerivEval_value [CompleteSpace E] (z v : ℂ) (h : markedModel (E := E) K) :
    markedDerivEval (E := E) (K := K) z v h = cDeriv h.val z v := rfl

def markedVariation (z : ℂ) : markedModel (E := E) K →L[ℝ] E :=
  markedEval z - ((ContinuousLinearMap.lsmul ℝ ℂ (E := E)) z).comp (markedEval 1)

omit [CompleteSpace E] in
@[simp] lemma markedVariation_value [CompleteSpace E] (z : ℂ) (h : markedModel (E := E) K) :
    markedVariation (E := E) (K := K) z h = cValue h.val z - z • cValue h.val 1 := rfl

def markedDerivativeVariation (z v : ℂ) : markedModel (E := E) K →L[ℝ] E :=
  markedDerivEval z v - ((ContinuousLinearMap.lsmul ℝ ℂ (E := E)) v).comp (markedEval 1)

omit [CompleteSpace E] in
@[simp] lemma markedDerivativeVariation_value [CompleteSpace E] (z v : ℂ) (h : markedModel (E := E) K) :
    markedDerivativeVariation (E := E) (K := K) z v h = cDeriv h.val z v - v • cValue h.val 1 := rfl


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {n : ℕ}
local instance compLinInst1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance compLinInst2 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace
local instance compLinInst3 : NormedAddCommGroup (Phase n →L[ℝ] End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance compLinInst4 : NormedSpace ℝ (Phase n →L[ℝ] End n) := ContinuousLinearMap.toNormedSpace

local instance compLinInst5_rcbd1d2_1 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance compLinInst6_rcbd1d2_1 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
local instance compLinInst7_rcbd1d2_1 : NormedAddCommGroup (HMap ℂ (Phase n)) := inferInstance
local instance compLinInst8_rcbd1d2_1 : NormedSpace ℝ (HMap ℂ (Phase n)) := inferInstance
local instance compLinInst9_rcbd1d2_1 : NormedAddCommGroup (HMap ℂ (End n)) := inferInstance
local instance compLinInst10_rcbd1d2_1 : NormedSpace ℝ (HMap ℂ (End n)) := inferInstance
variable {J : Phase n → End n} (hJ : ContDiff ℝ ∞ J) (hc : ∀ x, Compatible (J x)) {B : ℝ}
  (hstd : ∀ x, B < ‖x‖ → J x=standardJ n) (p q : Phase n) (u : COne ℂ (Phase n))

def completedDStructure : HMap ℂ (Phase n →L[ℝ] End n) :=
  affineJetValue (boundedCThree_of_compactSupport (hJ.fderiv_right (by simp))
    (compactSupport_fderiv_of_perturbation (standardJ n)
      (compactPerturbation_of_outside_constant _ hstd))) p (complexSlope (markedSlope p q u)) u

def completedDX : HMap ℂ (Phase n) :=
  const _ (markedSlope p q u)+jetDirection 1 u

@[simp] lemma completedDX_value (z : ℂ) :
    valueCLM _ (completedDX p q u) z = fderiv ℝ (markedCurve p q u) z 1 := by
  rw [markedCurve_fderiv]
  simp only [add_apply,complexSlope_apply,one_smul]
  rfl

def completedQ : HMap ℂ (End n) :=
  bilinCLM (X := ℂ) (α := (1:ℝ)/3)
    (ContinuousLinearMap.flipₗᵢ ℝ (Phase n) (Phase n) (Phase n)).toContinuousLinearEquiv.toContinuousLinearMap
    (completedDStructure hJ hstd p q u) (completedDX p q u)

@[simp] lemma completedQ_value (z : ℂ) (v : Phase n) :
    valueCLM _ (completedQ hJ hstd p q u) z v =
      fderiv ℝ J (markedCurve p q u z) v (fderiv ℝ (markedCurve p q u) z 1) := by
  change fderiv ℝ J (markedCurve p q u z) v (valueCLM _ (completedDX p q u) z) = _
  exact congrArg (fun w : Phase n => fderiv ℝ J (markedCurve p q u z) v w) (completedDX_value p q u z)


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeFredInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeFredInst2
local instance freeFredInst3 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance freeFredInst4 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance freeFredInst5_rcbd1d2_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance freeFredInst6 : NormedSpace ℝ (HMap ℂ E) := inferInstance
variable {K : Set ℂ}
local instance freeFredInst7_rcbd1d2_1 : NormedAddCommGroup (freeModel (E := E) K) := inferInstance
local instance freeFredInst8 : NormedSpace ℝ (freeModel (E := E) K) := inferInstance
local instance freeFredInst9_rcbd1d2_1 : NormedAddCommGroup (markedModel (E := E) K) := inferInstance
local instance freeFredInst10_rcbd1d2_1 : NormedSpace ℝ (markedModel (E := E) K) := inferInstance
local instance freeFredInst11_rcbd1d2_1 : NormedAddCommGroup (supportedHolder (E := E) K) := inferInstance
local instance freeFredInst12 : NormedSpace ℝ (supportedHolder (E := E) K) := inferInstance

local instance freeFredInst14 : Module ℝ (freeModel (E := E) K) := (freeFredInst8 (E := E) (K := K)).toModule
local instance freeFredInst18 : Module ℝ (supportedHolder (E := E) K) := (freeFredInst12 (E := E) (K := K)).toModule

variable (A C : HMap ℂ (E →L[ℝ] E))
  (hA : ∀ z ∉ K, valueCLM _ A z = complexI (E := E))
  (hC : ∀ z ∉ K, valueCLM _ C z = 0)

def freePrincipal : freeModel (E := E) K →L[ℝ] supportedHolder (E := E) K :=
  (markedPrincipal A hA).comp freeNormalize

@[simp] lemma freePrincipal_value (u : freeModel (E := E) K) (z : ℂ) :
    valueCLM _ (freePrincipal A hA u).val z =
      cDeriv u.val z Complex.I-valueCLM _ A z (cDeriv u.val z 1) := by
  change cDeriv (zeroNormalize u.val) z Complex.I-valueCLM _ A z (cDeriv (zeroNormalize u.val) z 1)=_
  rw [zeroNormalize_deriv]

def freeZeroOrder : freeModel (E := E) K →L[ℝ] supportedHolder (E := E) K :=
  ((jetZeroOrder C).comp (freeModel (E := E) K).subtypeL).codRestrict _ (fun u => by
    apply (mem_supportedHolder _ _).mpr
    intro z hz
    change valueCLM _ C z (cValue u.val z)=0
    rw [hC z hz,zero_apply])

omit [CompleteSpace E] in
@[simp] lemma freeZeroOrder_value [CompleteSpace E] (u : freeModel (E := E) K) (z : ℂ) :
    valueCLM _ (freeZeroOrder C hC u).val z = valueCLM _ C z (cValue u.val z) := rfl


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable {K : Set ℂ}

local instance chartDerInst1_rcbd1d2_1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance chartDerInst2_rcbd1d2_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance chartDerInst3_rcbd1d2_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance chartDerInst4_rcbd1d2_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance chartDerInst5_rcbd1d2_1 : NormedAddCommGroup (supportedHolder (E := E) K) := inferInstance
local instance chartDerInst6_rcbd1d2_1 : NormedSpace ℝ (supportedHolder (E := E) K) := inferInstance
def supportedEval (z : ℂ) : supportedHolder (E := E) K →L[ℝ] E :=
  ((BoundedContinuousFunction.evalCLM ℝ z).comp (valueCLM _)).comp
    (supportedHolder (E := E) K).subtypeL

omit [CompleteSpace E] in
@[simp] lemma supportedEval_value [CompleteSpace E] (z : ℂ) (g : supportedHolder (E := E) K) :
    supportedEval (E := E) (K := K) z g = valueCLM _ g.val z := rfl


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end


