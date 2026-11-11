-- Prove2me | Definitions.Def_OAIQ240Bp011
-- name    : OAIQ240Bp011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T00:23:59.859514+00:00
-- url     : https://prove2.me/theorems/7d62420b-2021-4d85-af24-0eebcf135744
-- title:
--   Definitions bundle OAIQ240Bp011 of the split of OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 60 declarations of OpenAI's Lean: 38 definitions and 22 theorems. The definitions and types are `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ccFrameInst1`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ccFrameInst2`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrameJet`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleInverseJet`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedFrameJet`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedInverseJet`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedPrincipal`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedStructureJet`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveMarkCoefficient`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveZeroOrder`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frameCRCoefficient`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frozenTargetCoefficient`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.geoLinInst1`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.geoLinInst2`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.geoLinInst3`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetZeroOrder`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.linCRInst3`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.mFredInst1`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.mFredInst10`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.mFredInst17`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.mFredInst19`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.mFredInst2`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.mFredInst4`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.mFredInst6`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.mFredInst8`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.mFredInst9`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedCurve`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedEval`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedFiniteCorrection`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedPrincipal`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedSlope`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedZeroOrder`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ofBoundedLipschitz`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.principalCR`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothAlongJet`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothMarkedPrincipal`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.supportedFieldAction`, `OAI.HigherDimensionalBallPacking.Rigidity.realCurve`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`BallPacking_Compactness_FrozenCR`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Compactness/FrozenCR.lean), [`BallPacking_Compactness_GradientBounds`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Compactness/GradientBounds.lean), [`BallPacking_Compactness_JetCauchy`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Compactness/JetCauchy.lean), [`BallPacking_Fredholm_CompactFredholmAlternative`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/CompactFredholmAlternative.lean), [`BallPacking_Fredholm_FiniteExtensions`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/FiniteExtensions.lean), [`BallPacking_Fredholm_FrameFredholm`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/FrameFredholm.lean), [`BallPacking_Holder_MarkedJets`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Holder/MarkedJets.lean), [`BallPacking_Rigidity_Correction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Rigidity/Correction.lean), [`BallPacking_Rigidity_CurveArea`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Rigidity/CurveArea.lean).
--
--   **Imports.** It imports the published bundle `Def_BallPacking`; the bundle `OAIQ240Bp008` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ240Bp014` and `OAIQ240Bp015`; the proofs of `OAI.HigherDimensionalBallPacking.Rigidity.compactPerturbation_package_finrank_bp240`, `OAI_HigherDimensionalBallPacking_Rigidity_framed_compact_perturbation_fredholm` and `OAI.HigherDimensionalBallPacking.Rigidity.framed_compact_perturbation_fredholm_bp240`.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp008

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

local instance markedAffineInst1_rb87c41_1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance markedAffineInst2_rb87c41_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance markedAffineInst3_rb87c41_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance markedAffineInst4_rb87c41_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance markedAffineInst5_rb87c41_1 : NormedAddCommGroup (markedModel (E := E) K) := inferInstance
local instance markedAffineInst6_rb87c41_1 : NormedSpace ℝ (markedModel (E := E) K) := inferInstance
local instance markedAffineInst7_rb87c41_1 : NormedAddCommGroup (supportedHolder (E := E) K) := inferInstance
local instance markedAffineInst8_rb87c41_1 : NormedSpace ℝ (supportedHolder (E := E) K) := inferInstance
def markedSlope (p q : E) (u : COne ℂ E) : E := q-p-cValue u 1

def markedCurve (p q : E) (u : COne ℂ E) (z : ℂ) : E :=
  p + z • markedSlope p q u + cValue u z



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Compactness_GradientBounds
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineJetDeriv_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineJetSuperpose_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineJetValue_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compactPerturbationJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeSum_deriv _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeSum_value _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
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
variable {X E F : Type*} [MetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def ofBoundedLipschitz (f : X → E) (hf : Continuous f) (M L : ℝ)
    (hM : 0≤M) (hL : 0≤L) (hb : ∀ x,‖f x‖≤M)
    (hl : ∀ x y,‖f x-f y‖≤L*dist x y) : HMap X E :=
  ofBound f hf M (2*M+L) hb (by positivity) (by
    apply third_interpolation hM hL (by positivity) (show (0:ℝ)<1 by norm_num) hb hl
    · simp only [Real.one_rpow,mul_one] <;> linarith
    · simp only [Real.one_rpow,mul_one] <;> linarith)

@[simp] lemma ofBoundedLipschitz_value (f : X → E) (hf : Continuous f) (M L : ℝ)
    (hM : 0≤M) (hL : 0≤L) (hb : ∀ x,‖f x‖≤M)
    (hl : ∀ x y,‖f x-f y‖≤L*dist x y) (x : X) :
    valueCLM _ (ofBoundedLipschitz f hf M L hM hL hb hl) x=f x := rfl


end
open scoped Topology BoundedContinuousFunction
open Set Filter



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Compactness_JetCauchy
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineJetSuperpose_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compactPerturbationJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeSum_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.normalizedPrimitive_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
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

variable {K : Set ℂ} (hK : IsCompact K) {A : ℂ → End n}
    (hA : ContDiff ℝ ∞ A) (hc : ∀ z, Compatible (A z))
    (hstd : ∀ z ∉ K, A z = standardJ n)

def compatibleFrameJet : COne ℂ (End n) :=
  ofBoundedCThree (boundedCThree_of_compactPerturbation (compatibleFrame_smooth hA) _
    (compatibleFrame_compactPerturbation hK hstd))

def compatibleInverseJet : COne ℂ (End n) :=
  ofBoundedCThree (boundedCThree_of_compactPerturbation (compatibleFrame_inverse_smooth hA hc) _
    (compatibleFrame_inverse_compactPerturbation hK hstd))

@[simp] lemma compatibleFrameJet_value (z : ℂ) :
    cValue (compatibleFrameJet hK hA hstd) z = compatibleFrame (A z) := rfl

@[simp] lemma compatibleInverseJet_value (z : ℂ) :
    cValue (compatibleInverseJet hK hA hc hstd) z = (compatibleFrame (A z)).inverse := rfl



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Compactness_FrozenCR
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
variable {n : ℕ}

local instance fcrInst1_rb87c41_1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance fcrInst2_rb87c41_1 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace
def frozenTargetCoefficient (J : Phase n → End n) (x v : Phase n) : End n :=
  let P := compatibleFrame (J x)
  (P.comp (J (x+P.inverse v)-J x)).comp P.inverse

end HigherDimensionalBallPacking.Rigidity.HolderCompletion

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_FiniteExtensions
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.cutoffCurveJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetDirectional_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ofBoundedLipschitz_value _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
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
namespace HolderCompletion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [completeSpaceE : CompleteSpace E]

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.zeroOrderInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.zeroOrderInst2
local instance zeroOrderInst3_rb87c41_1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance zeroOrderInst4_rb87c41_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance zeroOrderInst5_rb87c41_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance zeroOrderInst6_rb87c41_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
def jetZeroOrder (C : HMap ℂ (E →L[ℝ] E)) : COne ℂ E →L[ℝ] HMap ℂ E :=
  (holderCoefficientAction C).comp (jetValueCLM _)

omit completeSpaceE in
@[simp] lemma jetZeroOrder_value [CompleteSpace E]
    (C : HMap ℂ (E →L[ℝ] E)) (u : COne ℂ E) (z : ℂ) :
    valueCLM _ (jetZeroOrder C u) z = valueCLM _ C z (cValue u z) := rfl

variable {K : Set ℂ}

local instance zeroOrderInst7_rb87c41_1 : NormedAddCommGroup (markedModel (E := E) K) := inferInstance
local instance zeroOrderInst8_rb87c41_1 : NormedSpace ℝ (markedModel (E := E) K) := inferInstance
local instance zeroOrderInst9_rb87c41_1 : NormedAddCommGroup (supportedHolder (E := E) K) := inferInstance
local instance zeroOrderInst10_rb87c41_1 : NormedSpace ℝ (supportedHolder (E := E) K) := inferInstance
def markedZeroOrder (C : HMap ℂ (E →L[ℝ] E))
    (hC : ∀ z ∉ K, valueCLM _ C z = 0) :
    markedModel (E := E) K →L[ℝ] supportedHolder (E := E) K :=
  ((jetZeroOrder C).comp (markedModel K).subtypeL).codRestrict _ (fun u => by
    apply (mem_supportedHolder _ K).mpr
    intro z hz
    change valueCLM _ C z (cValue u.val z) = 0
    rw [hC z hz,zero_apply])

omit completeSpaceE in
@[simp] lemma markedZeroOrder_value [CompleteSpace E] (C : HMap ℂ (E →L[ℝ] E))
    (hC : ∀ z ∉ K, valueCLM _ C z = 0) (u : markedModel (E := E) K) (z : ℂ) :
    valueCLM _ (markedZeroOrder C hC u).val z = valueCLM _ C z (cValue u.val z) := rfl

end HolderCompletion

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_CompactFredholmAlternative
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.normalizedPrimitive_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
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
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.linCRInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.linCRInst2
local instance linCRInst3 : NormedAddCommGroup (COne ℂ E) := inferInstance

local instance linCRInst4_rb87c41_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance linCRInst5_rb87c41_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance linCRInst6_rb87c41_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance linCRInst7_rb87c41_1 : NormedAddCommGroup (HMap ℂ (E →L[ℝ] E)) := inferInstance
local instance linCRInst8_rb87c41_1 : NormedSpace ℝ (HMap ℂ (E →L[ℝ] E)) := inferInstance
local instance linCRInst9_rb87c41_1 : NormedAddCommGroup (COne ℂ (E →L[ℝ] E)) := inferInstance
local instance linCRInst10_rb87c41_1 : NormedSpace ℝ (COne ℂ (E →L[ℝ] E)) := inferInstance
def principalCR (A : HMap ℂ (E →L[ℝ] E)) : COne ℂ E →L[ℝ] HMap ℂ E :=
  jetDirection Complex.I - (holderCoefficientAction A).comp (jetDirection 1)

omit [CompleteSpace E] in
@[simp] lemma principalCR_value [CompleteSpace E]
    (A : HMap ℂ (E →L[ℝ] E)) (u : COne ℂ E) (z : ℂ) :
    valueCLM _ (principalCR A u) z = cDeriv u z Complex.I - valueCLM _ A z (cDeriv u z 1) := rfl

variable {K : Set ℂ}

local instance linCRInst11_rb87c41_1 : NormedAddCommGroup (markedModel (E := E) K) := inferInstance
local instance linCRInst12_rb87c41_1 : NormedSpace ℝ (markedModel (E := E) K) := inferInstance
local instance linCRInst13_rb87c41_1 : NormedAddCommGroup (supportedHolder (E := E) K) := inferInstance
local instance linCRInst14_rb87c41_1 : NormedSpace ℝ (supportedHolder (E := E) K) := inferInstance
def markedPrincipal (A : HMap ℂ (E →L[ℝ] E))
    (hA : ∀ z ∉ K, valueCLM _ A z = complexI) :
    markedModel (E := E) K →L[ℝ] supportedHolder (E := E) K :=
  (principalCR A).restrict (fun u hu => by
    apply (mem_supportedHolder _ K).mpr
    intro z hz
    have huZ := (mem_supportedHolder (standardJetCR u) K).mp hu.2 z hz
    rw [standardJetCR_value] at huZ
    rw [principalCR_value,hA z hz]
    exact huZ)

@[simp] lemma markedPrincipal_value (A : HMap ℂ (E →L[ℝ] E))
    (hA : ∀ z ∉ K, valueCLM _ A z = complexI)
    (u : markedModel (E := E) K) (z : ℂ) :
    valueCLM _ (markedPrincipal A hA u).val z = cDeriv u.val z Complex.I - valueCLM _ A z (cDeriv u.val z 1) := rfl

def frameCRCoefficient (M : COne ℂ (E →L[ℝ] E)) : HMap ℂ (E →L[ℝ] E) :=
  jetDirection Complex.I M -
    mapCLM ((1:ℝ)/3) ((ContinuousLinearMap.compL ℝ E E E) complexI) (jetDirection 1 M)

omit [CompleteSpace E] in
@[simp] lemma frameCRCoefficient_value [CompleteSpace E]
    (M : COne ℂ (E →L[ℝ] E)) (z : ℂ) (v : E) :
    valueCLM _ (frameCRCoefficient M) z v = cDeriv M z Complex.I v - Complex.I • (cDeriv M z 1 v) := rfl

end HigherDimensionalBallPacking.Rigidity.HolderCompletion

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

variable {n : ℕ} {K : Set ℂ} (hK : IsCompact K) {A : ℂ → End n}
    (hA : ContDiff ℝ ∞ A) (hc : ∀ z, Compatible (A z)) (hstd : ∀ z ∉ K, A z = standardJ n)

local instance mFredInst1 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance mFredInst2 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
local instance mFredInst3_rb87c41_1 : NormedAddCommGroup (HMap ℂ (Phase n)) := inferInstance
local instance mFredInst4 : NormedSpace ℝ (HMap ℂ (Phase n)) := inferInstance
local instance mFredInst5_rb87c41_1 : NormedAddCommGroup (markedModel (E := Phase n) K) := inferInstance
local instance mFredInst6 : NormedSpace ℝ (markedModel (E := Phase n) K) := inferInstance
local instance mFredInst7_rb87c41_1 : NormedAddCommGroup (supportedHolder (E := Phase n) K) := inferInstance
local instance mFredInst8 : NormedSpace ℝ (supportedHolder (E := Phase n) K) := inferInstance
local instance mFredInst9 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance mFredInst10 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace
local instance mFredInst11_rb87c41_1 : NormedAddCommGroup (HMap ℂ (End n)) := inferInstance
local instance mFredInst12_rb87c41_1 : NormedSpace ℝ (HMap ℂ (End n)) := inferInstance
local instance mFredInst13_rb87c41_1 : NormedAddCommGroup (COne ℂ (End n)) := inferInstance
local instance mFredInst14_rb87c41_1 : NormedSpace ℝ (COne ℂ (End n)) := inferInstance
local instance mFredInst17 : Module ℝ (markedModel (E := Phase n) K) := (mFredInst6 (n := n) (K := K)).toModule
local instance mFredInst19 : Module ℝ (supportedHolder (E := Phase n) K) := (mFredInst8 (n := n) (K := K)).toModule

include hK hstd in
lemma structureAlong_compactPerturbation : HasCompactSupport (fun z => A z - standardJ n) := by
  apply HasCompactSupport.of_support_subset_isCompact hK
  intro z hz
  by_contra hzK
  apply hz
  change A z-standardJ n=0
  rw [hstd z hzK,sub_self]

def smoothAlongJet : COne ℂ (End n) :=
  ofBoundedCThree (boundedCThree_of_compactPerturbation hA (standardJ n)
    (structureAlong_compactPerturbation hK hstd))

@[simp] lemma smoothAlongJet_value (z : ℂ) : cValue (smoothAlongJet (n := n) hK hA hstd) z = A z := rfl

def smoothMarkedPrincipal : markedModel (E := Phase n) K →L[ℝ] supportedHolder (E := Phase n) K :=
  markedPrincipal (jetValueCLM _ (smoothAlongJet (n := n) hK hA hstd)) (by intro z hz; exact hstd z hz)

@[simp] lemma smoothMarkedPrincipal_value (u : markedModel (E := Phase n) K) (z : ℂ) :
    valueCLM _ (smoothMarkedPrincipal (n := n) hK hA hstd u).val z =
      cDeriv u.val z Complex.I - A z (cDeriv u.val z 1) := rfl

end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_FrameFredholm
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.normalizedPrimitive_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
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
local instance ccFrameInst1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance ccFrameInst2 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace

local instance ccFrameInst3_rb87c41_1 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance ccFrameInst4_rb87c41_1 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
local instance ccFrameInst5_rb87c41_1 : NormedAddCommGroup (HMap ℂ (Phase n)) := inferInstance
local instance ccFrameInst6_rb87c41_1 : NormedSpace ℝ (HMap ℂ (Phase n)) := inferInstance
local instance ccFrameInst7_rb87c41_1 : NormedAddCommGroup (COne ℂ (End n)) := inferInstance
local instance ccFrameInst8_rb87c41_1 : NormedSpace ℝ (COne ℂ (End n)) := inferInstance
local instance ccFrameInst9_rb87c41_1 : NormedAddCommGroup (HMap ℂ (End n)) := inferInstance
local instance ccFrameInst10_rb87c41_1 : NormedSpace ℝ (HMap ℂ (End n)) := inferInstance
variable {J : Phase n → End n} (hJ : ContDiff ℝ ∞ J) (hc : ∀ x, Compatible (J x)) {B : ℝ}
  (hstd : ∀ x, B < ‖x‖ → J x=standardJ n) (p q : Phase n) (u : COne ℂ (Phase n))

def completedStructureJet : COne ℂ (End n) :=
  compactPerturbationJet hJ (standardJ n) (compactPerturbation_of_outside_constant _ hstd)
    p (complexSlope (markedSlope p q u)) u

@[simp] lemma completedStructureJet_value (z : ℂ) :
    cValue (completedStructureJet hJ hstd p q u) z = J (markedCurve p q u z) := rfl

def completedFrameJet : COne ℂ (End n) :=
  compactPerturbationJet (compatibleFrame_smooth hJ) ((2:ℝ) • ContinuousLinearMap.id ℝ (Phase n))
    (compactPerturbation_of_outside_constant _ (fun x hx =>
      (congrArg compatibleFrame (hstd x hx)).trans compatibleFrame_standard))
    p (complexSlope (markedSlope p q u)) u

@[simp] lemma completedFrameJet_value (z : ℂ) :
    cValue (completedFrameJet hJ hstd p q u) z = compatibleFrame (J (markedCurve p q u z)) := rfl

def completedInverseJet : COne ℂ (End n) :=
  compactPerturbationJet (compatibleFrame_inverse_smooth hJ hc) ((1/2:ℝ) • ContinuousLinearMap.id ℝ (Phase n))
    (compactPerturbation_of_outside_constant _ (fun x hx =>
      (congrArg (fun A : End n => (compatibleFrame A).inverse) (hstd x hx)).trans compatibleFrame_inverse_standard))
    p (complexSlope (markedSlope p q u)) u

@[simp] lemma completedInverseJet_value (z : ℂ) :
    cValue (completedInverseJet hJ hc hstd p q u) z = (compatibleFrame (J (markedCurve p q u z))).inverse := rfl

variable {K : Set ℂ} (hK : IsCompact K) (he : ∀ z ∉ K, B < ‖markedCurve p q u z‖)

local instance ccFrameInst11_rb87c41_1 : NormedAddCommGroup (markedModel (E := Phase n) K) := inferInstance
local instance ccFrameInst12_rb87c41_1 : NormedSpace ℝ (markedModel (E := Phase n) K) := inferInstance
local instance ccFrameInst13_rb87c41_1 : NormedAddCommGroup (supportedHolder (E := Phase n) K) := inferInstance
local instance ccFrameInst14_rb87c41_1 : NormedSpace ℝ (supportedHolder (E := Phase n) K) := inferInstance
def completedPrincipal : markedModel (E := Phase n) K →L[ℝ] supportedHolder (E := Phase n) K :=
  markedPrincipal (jetValueCLM _ (completedStructureJet hJ hstd p q u))
    (fun z hz => hstd _ (he z hz))

@[simp] lemma completedPrincipal_value (v : markedModel (E := Phase n) K) (z : ℂ) :
    valueCLM _ (completedPrincipal hJ hstd p q u he v).val z =
      cDeriv v.val z Complex.I-J (markedCurve p q u z) (cDeriv v.val z 1) := rfl


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable {K : Set ℂ}

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markFiniteInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markFiniteInst2
local instance markFiniteInst3_rb87c41_1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance markFiniteInst4_rb87c41_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance markFiniteInst5_rb87c41_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance markFiniteInst6_rb87c41_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance markFiniteInst7_rb87c41_1 : NormedAddCommGroup (markedModel (E := E) K) := inferInstance
local instance markFiniteInst8_rb87c41_1 : NormedSpace ℝ (markedModel (E := E) K) := inferInstance
local instance markFiniteInst9_rb87c41_1 : NormedAddCommGroup (supportedHolder (E := E) K) := inferInstance
local instance markFiniteInst10_rb87c41_1 : NormedSpace ℝ (supportedHolder (E := E) K) := inferInstance
def supportedFieldAction (B : HMap ℂ (E →L[ℝ] E)) (hB : ∀ z ∉ K, valueCLM _ B z = 0) :
    E →L[ℝ] supportedHolder (E := E) K :=
  ((holderCoefficientAction B).comp constHolderCLM).codRestrict _ (fun v => by
    apply (mem_supportedHolder _ K).mpr
    intro z hz
    change valueCLM _ B z v = 0
    rw [hB z hz,zero_apply])

omit [CompleteSpace E] in
@[simp] lemma supportedFieldAction_value [CompleteSpace E] (B : HMap ℂ (E →L[ℝ] E))
    (hB : ∀ z ∉ K, valueCLM _ B z = 0) (v : E) (z : ℂ) :
    valueCLM _ (supportedFieldAction B hB v).val z = valueCLM _ B z v := rfl

def markedEval (z : ℂ) : markedModel (E := E) K →L[ℝ] E :=
  (jetEval z).comp (markedModel (E := E) K).subtypeL

omit [CompleteSpace E] in
@[simp] lemma markedEval_value [CompleteSpace E] (z : ℂ) (u : markedModel (E := E) K) :
    markedEval (E := E) (K := K) z u = cValue u.val z := rfl

def markedFiniteCorrection (B : HMap ℂ (E →L[ℝ] E)) (hB : ∀ z ∉ K, valueCLM _ B z = 0) :
    markedModel (E := E) K →L[ℝ] supportedHolder (E := E) K :=
  (supportedFieldAction B hB).comp (markedEval (E := E) (K := K) 1)

omit [CompleteSpace E] in
@[simp] lemma markedFiniteCorrection_value [CompleteSpace E] (B : HMap ℂ (E →L[ℝ] E))
    (hB : ∀ z ∉ K, valueCLM _ B z = 0) (u : markedModel (E := E) K) (z : ℂ) :
    valueCLM _ (markedFiniteCorrection B hB u).val z = valueCLM _ B z (cValue u.val 1) := rfl


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {n : ℕ}
local instance geoLinInst1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance geoLinInst2 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace
local instance geoLinInst3 : NormedAddCommGroup (Phase n →L[ℝ] End n) := ContinuousLinearMap.toNormedAddCommGroup

local instance geoLinInst4_rb87c41_1 : NormedSpace ℝ (Phase n →L[ℝ] End n) := ContinuousLinearMap.toNormedSpace
local instance geoLinInst5_rb87c41_1 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance geoLinInst6_rb87c41_1 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
local instance geoLinInst7_rb87c41_1 : NormedAddCommGroup (HMap ℂ (Phase n)) := inferInstance
local instance geoLinInst8_rb87c41_1 : NormedSpace ℝ (HMap ℂ (Phase n)) := inferInstance
local instance geoLinInst9_rb87c41_1 : NormedAddCommGroup (HMap ℂ (End n)) := inferInstance
local instance geoLinInst10_rb87c41_1 : NormedSpace ℝ (HMap ℂ (End n)) := inferInstance
lemma fderiv_standard_outside {J : Phase n → End n} {B : ℝ}
    (hstd : ∀ x, B < ‖x‖ → J x = standardJ n) {x : Phase n} (hx : B < ‖x‖) :
    fderiv ℝ J x = 0 := by
  have he : J =ᶠ[𝓝 x] fun _ => standardJ n := by
    filter_upwards [isOpen_lt continuous_const continuous_norm |>.mem_nhds hx] with y hy
    exact hstd y hy
  rw [he.fderiv_eq]
  exact (hasFDerivAt_const (𝕜 := ℝ) (standardJ n) x).fderiv

def curveZeroOrder (J : Phase n → End n) (f : ℂ → Phase n) (z : ℂ) : End n :=
  (fderiv ℝ J (f z)).flip (fderiv ℝ f z 1)

@[simp] lemma curveZeroOrder_apply (J : Phase n → End n) (f : ℂ → Phase n) (z : ℂ) (v : Phase n) :
    curveZeroOrder J f z v = fderiv ℝ J (f z) v (fderiv ℝ f z 1) := rfl

def curveMarkCoefficient (J : Phase n → End n) (f : ℂ → Phase n) (z : ℂ) : End n :=
  J (f z)-standardJ n + (curveZeroOrder J f z).comp ((ContinuousLinearMap.lsmul ℝ ℂ) z)

@[simp] lemma curveMarkCoefficient_apply (J : Phase n → End n) (f : ℂ → Phase n) (z : ℂ) (v : Phase n) :
    curveMarkCoefficient J f z v = J (f z) v - Complex.I • v +
      fderiv ℝ J (f z) (z • v) (fderiv ℝ f z 1) := rfl


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Rigidity_CurveArea
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
open SymplecticBallPacking.Hamiltonian (Plane )

def realCurve {n : ℕ} (u : ℂ → Phase n) : Plane → Phase n :=
  u ∘ Complex.equivRealProdCLM.symm


end

open scoped ContDiff Topology
open Set Function Filter MeasureTheory



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Rigidity_Correction
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrame_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedStructureJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveMarkCoefficient_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveZeroOrder_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothMarkedPrincipal_value _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex _root_.OAI.SymplecticBallPacking.Hamiltonian.coordinateForm_apply
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
open SymplecticBallPacking.Hamiltonian (Plane )

@[simp] theorem realCurve_zero {n : ℕ} (u : ℂ → Phase n) : realCurve u 0 = u 0 := by
  simp [realCurve,Complex.equivRealProdCLM_symm_apply]


end

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end


