-- Prove2me | Definitions.Def_OAIQ240Bp008
-- name    : OAIQ240Bp008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T00:18:23.666115+00:00
-- url     : https://prove2.me/theorems/56d1ec52-e7cf-42d4-afd5-e0045c773ba7
-- title:
--   Definitions bundle OAIQ240Bp008 of the split of OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 37 declarations of OpenAI's Lean: 19 definitions and 18 theorems. The definitions and types are `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineJetDeriv`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineJetSuperpose`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineJetValue`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.bumpHolder`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compactPerturbationJet`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.constHolderCLM`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.cutoffCurveJet`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeConst`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeInst1`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeModel`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeSum`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetDirectional`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.localizedJetValue`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedToFree`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.restrictedValue`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.sourceCutoff`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.supportedSourceCutoff`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.transInst1`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.truncateShift`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`BallPacking_Compactness_AffineCorrectionInfinity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Compactness/AffineCorrectionInfinity.lean), [`BallPacking_Compactness_GradientBounds`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Compactness/GradientBounds.lean), [`BallPacking_Fredholm_FiniteExtensions`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/FiniteExtensions.lean), [`BallPacking_Holder_BanachSpace`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Holder/BanachSpace.lean), [`BallPacking_Holder_MarkedFrame`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Holder/MarkedFrame.lean).
--
--   **Imports.** It imports the bundle `OAIQ240Bp024` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ240Bp011`, `OAIQ240Bp013` and `OAIQ240Bp025`; the statements `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_disk_nonlinear_jet_cauchy` and `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.disk_nonlinear_jet_cauchy_bp240`; the proof of `OAI_HigherDimensionalBallPacking_Rigidity_compactPerturbation_package_finrank`.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ240Bp024

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_BanachSpace
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped BoundedContinuousFunction Topology ContDiff
open Set Filter
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma boundedCThree_of_compactPerturbation {f : E → F} (hf : ContDiff ℝ ∞ f)
    (c : F) (hc : HasCompactSupport (fun x => f x - c)) : BoundedCThree f := by
  have h := (boundedCThree_of_compactSupport (hf.sub contDiff_const) hc).add_const c
  simpa only [sub_add_cancel] using h

end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_MarkedFrame
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
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
local instance affineCutInst3_rbc3ba4_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance affineCutInst4_rbc3ba4_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineCutInst5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineCutInst6
omit [CompleteSpace E] in
@[simp] lemma cutoffSlope_value (a : E) (z : ℂ) :
    cValue (cutoffSlope b a) z = b z • (z • a) := by
  change (b z • z) • a = _
  exact smul_assoc (b z) z a

def truncateShift : COne ℂ E →L[ℝ] COne ℂ E :=
  ContinuousLinearMap.id ℝ _ - (cutoffSlope b).comp (jetEval 1)

omit [CompleteSpace E] in
@[simp] lemma truncateShift_value (h : COne ℂ E) (z : ℂ) :
    cValue (truncateShift b h) z = cValue h z-b z • (z • cValue h 1) := by
  change cValue h z-cValue (cutoffSlope b (cValue h 1)) z = _
  rw [cutoffSlope_value]


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance sourceCutInst1_rbc3ba4_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance sourceCutInst2_rbc3ba4_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
def constHolderCLM : E →L[ℝ] HMap ℂ E :=
  LinearMap.mkContinuous
    { toFun := const _
      map_add' := fun u v => by apply value_ext; intro z; rfl
      map_smul' := fun c v => by apply value_ext; intro z; rfl }
    1 (by intro v; change ‖const _ v‖ ≤ 1*‖v‖; rw [one_mul]; exact const_norm_le v)

@[simp] lemma constHolderCLM_value (v : E) (z : ℂ) : valueCLM _ (constHolderCLM v) z = v := rfl

variable (b : ContDiffBump (0:ℂ))

def bumpHolder : HMap ℂ ℝ :=
  jetValueCLM _ (ofBoundedCThree (boundedCThree_of_compactSupport b.contDiff b.hasCompactSupport))

@[simp] lemma bumpHolder_value (z : ℂ) : valueCLM _ (bumpHolder b) z = b z := rfl

def sourceCutoff : HMap ℂ E →L[ℝ] HMap ℂ E :=
  bilinCLM (X := ℂ) (α := (1:ℝ)/3) (ContinuousLinearMap.lsmul ℝ ℝ (E := E)) (bumpHolder b)

@[simp] lemma sourceCutoff_value (g : HMap ℂ E) (z : ℂ) :
    valueCLM _ (sourceCutoff b g) z = b z • valueCLM _ g z := rfl

local instance sourceCutInst3_rbc3ba4_1 : NormedAddCommGroup (supportedHolder (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance sourceCutInst4_rbc3ba4_1 : NormedSpace ℝ (supportedHolder (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
def supportedSourceCutoff : HMap ℂ E →L[ℝ] supportedHolder (E := E) (Metric.closedBall (0:ℂ) b.rOut) :=
  (sourceCutoff b).codRestrict _ (fun g => by
    apply (mem_supportedHolder _ _).mpr
    intro z hz
    rw [sourceCutoff_value,b.zero_of_le_dist (by
      simp only [Metric.mem_closedBall] at hz
      exact (lt_of_not_ge hz).le),zero_smul])

@[simp] lemma supportedSourceCutoff_value (g : HMap ℂ E) (z : ℂ) :
    valueCLM _ (supportedSourceCutoff b g).val z = b z • valueCLM _ g z := rfl


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {X E : Type*} [MetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
lemma third_interpolation {f : X → E} {M L A s : ℝ}
    (_hM : 0 ≤ M) (hL : 0 ≤ L) (hA : 0 ≤ A) (hs : 0 < s)
    (hb : ∀ x, ‖f x‖ ≤ M) (hl : ∀ x y, ‖f x-f y‖ ≤ L*dist x y)
    (hsmall : L*s^((2:ℝ)/3) ≤ A) (hlarge : 2*M ≤ A*s^((1:ℝ)/3)) :
    ∀ x y, ‖f x-f y‖ ≤ A*dist x y^((1:ℝ)/3) := by
  intro x y
  by_cases hxy : x = y
  · subst y; simp
  have hd : 0 < dist x y := dist_pos.mpr hxy
  by_cases hds : dist x y ≤ s
  · have hp : dist x y = dist x y^((2:ℝ)/3)*dist x y^((1:ℝ)/3) := by
      rw [← Real.rpow_add hd]; norm_num
    calc
      _ ≤ L*dist x y := hl x y
      _ = (L*dist x y^((2:ℝ)/3))*dist x y^((1:ℝ)/3) := (congrArg (fun t : ℝ => L*t) hp).trans (mul_assoc _ _ _).symm
      _ ≤ (L*s^((2:ℝ)/3))*dist x y^((1:ℝ)/3) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hd.le hds (by norm_num)) hL) (by positivity)
      _ ≤ A*dist x y^((1:ℝ)/3) := mul_le_mul_of_nonneg_right hsmall (by positivity)
  · calc
      _ ≤ 2*M := (norm_sub_le _ _).trans (by linarith [hb x,hb y])
      _ ≤ A*s^((1:ℝ)/3) := hlarge
      _ ≤ A*dist x y^((1:ℝ)/3) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hs.le (le_of_not_ge hds) (by norm_num)) hA

local instance holderCompInst1_rbc3ba4_1 : NormedAddCommGroup (HMap X E) := inferInstance
local instance holderCompInst2_rbc3ba4_1 : NormedSpace ℝ (HMap X E) := inferInstance
def restrictedValue (K : Set X) : HMap X E →L[ℝ] (K →ᵇ E) :=
  (BoundedContinuousFunction.compContinuousCLM E ℝ ⟨Subtype.val,continuous_subtype_val⟩).comp (valueCLM _)

@[simp] lemma restrictedValue_apply (K : Set X) (u : HMap X E) (x : K) :
    restrictedValue K u x = valueCLM _ u x.val := rfl

variable (b : ContDiffBump (0:ℂ))

local instance holderLocInst1_rbc3ba4_1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance holderLocInst2_rbc3ba4_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
def localizedJetValue : COne ℂ E →L[ℝ] HMap ℂ E :=
  (sourceCutoff b).comp (jetValueCLM _)

@[simp] lemma localizedJetValue_apply (u : COne ℂ E) (z : ℂ) :
    valueCLM _ (localizedJetValue b u) z = b z • cValue u z := rfl



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Compactness_AffineCorrectionInfinity
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance transInst1 : NormedAddCommGroup (HMap D E) := inferInstance

end HigherDimensionalBallPacking.Rigidity.HolderCompletion

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Compactness_GradientBounds
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
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

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.scsInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.scsInst2
local instance scsInst3_rbc3ba4_1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance scsInst4_rbc3ba4_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance scsInst5_rbc3ba4_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance scsInst6_rbc3ba4_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance scsInst7_rbc3ba4_1 : NormedAddCommGroup (HMap ℂ (E →L[ℝ] E)) := inferInstance
local instance scsInst8_rbc3ba4_1 : NormedSpace ℝ (HMap ℂ (E →L[ℝ] E)) := inferInstance
def jetDirectional (z : ℂ) : COne ℂ E →L[ℝ] HMap ℂ E :=
  (mapCLM _ (ContinuousLinearMap.apply ℝ E z)).comp (jetDerivCLM _)

omit [CompleteSpace E] in
@[simp] lemma jetDirectional_value (z : ℂ) (v : COne ℂ E) (w : ℂ) :
    valueCLM _ (jetDirectional z v) w=cDeriv v w z := rfl


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

variable (b : ContDiffBump (0:ℂ)) {u : ℂ → E} (hu : ContDiff ℝ ∞ u)

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ccInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ccInst2
local instance ccInst3_rbc3ba4_1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance ccInst4_rbc3ba4_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance ccInst5_rbc3ba4_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance ccInst6_rbc3ba4_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance ccInst7_rbc3ba4_1 : NormedAddCommGroup (HMap ℂ (E →L[ℝ] E)) := inferInstance
local instance ccInst8_rbc3ba4_1 : NormedSpace ℝ (HMap ℂ (E →L[ℝ] E)) := inferInstance
def cutoffCurveJet : COne ℂ E :=
  ofBoundedCThree (boundedCThree_of_compactSupport (b.contDiff.smul hu) b.hasCompactSupport.smul_right)

omit [CompleteSpace E] in
@[simp] lemma cutoffCurveJet_value (z : ℂ) : cValue (cutoffCurveJet b hu) z=b z • u z := rfl


end
open scoped Topology BoundedContinuousFunction
open Set Filter



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_FiniteExtensions
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.cutoffCurveJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetDirectional_value _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [completeSpaceE : CompleteSpace E]
local instance freeInst1 : NormedAddCommGroup (COne ℂ E) := inferInstance

local instance freeInst2_rbc3ba4_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance freeInst3_rbc3ba4_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance freeInst4_rbc3ba4_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
def freeModel (K : Set ℂ) : Submodule ℝ (COne ℂ E) :=
  (supportedHolder K).comap standardJetCR.toLinearMap

variable {K : Set ℂ}

local instance freeInst5_rbc3ba4_1 : NormedAddCommGroup (freeModel (E := E) K) := inferInstance
local instance freeInst6_rbc3ba4_1 : NormedSpace ℝ (freeModel (E := E) K) := inferInstance
local instance freeInst7_rbc3ba4_1 : NormedAddCommGroup (markedModel (E := E) K) := inferInstance
local instance freeInst8_rbc3ba4_1 : NormedSpace ℝ (markedModel (E := E) K) := inferInstance
local instance freeInst9_rbc3ba4_1 : NormedAddCommGroup (supportedHolder (E := E) K) := inferInstance
local instance freeInst10_rbc3ba4_1 : NormedSpace ℝ (supportedHolder (E := E) K) := inferInstance
def markedToFree : markedModel (E := E) K →L[ℝ] freeModel (E := E) K :=
  (markedModel (E := E) K).subtypeL.codRestrict _ (fun u => u.property.2)

def freeConst : E →L[ℝ] freeModel (E := E) K :=
  (constJetCLM (E := E)).codRestrict _ (fun c => by
    change standardJetCR (constJet c) ∈ supportedHolder K
    apply (mem_supportedHolder _ _).mpr
    intro z _
    simp only [standardJetCR_value,constJet_deriv,zero_apply,smul_zero,sub_zero])

def freeSum : E × markedModel (E := E) K →L[ℝ] freeModel (E := E) K :=
  (freeConst (E := E) (K := K)).comp (ContinuousLinearMap.fst ℝ E (markedModel (E := E) K)) +
    (markedToFree (E := E) (K := K)).comp (ContinuousLinearMap.snd ℝ E (markedModel (E := E) K))

omit completeSpaceE in
@[simp] lemma freeSum_value [CompleteSpace E] (v : E × markedModel (E := E) K) (z : ℂ) :
    cValue (freeSum (E := E) (K := K) v).val z = v.1+cValue v.2.val z := rfl

omit completeSpaceE in
@[simp] lemma freeSum_deriv [CompleteSpace E] (v : E × markedModel (E := E) K) (z : ℂ) :
    cDeriv (freeSum (E := E) (K := K) v).val z = cDeriv v.2.val z := by
  change (0 : ℂ →L[ℝ] E)+cDeriv v.2.val z = _
  exact zero_add _

end HolderCompletion

end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
namespace HolderCompletion
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetSuperInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetSuperInst2
local instance jetSuperInst3_rbc3ba4_1 : NormedAddCommGroup (ℂ →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance jetSuperInst4_rbc3ba4_1 : NormedSpace ℝ (ℂ →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetSuperInst5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetSuperInst6
local instance jetSuperInst7_rbc3ba4_1 : NormedAddCommGroup (HMap ℂ F) := inferInstance
local instance jetSuperInst8_rbc3ba4_1 : NormedSpace ℝ (HMap ℂ F) := inferInstance
local instance jetSuperInst9_rbc3ba4_1 : NormedAddCommGroup (HMap ℂ (ℂ →L[ℝ] F)) := inferInstance
local instance jetSuperInst10_rbc3ba4_1 : NormedSpace ℝ (HMap ℂ (ℂ →L[ℝ] F)) := inferInstance
variable {P : E → F} (hP : BoundedCThree P) (hDP : BoundedCThree (fderiv ℝ P))
    (p : E) (a : ℂ →L[ℝ] E) (u : COne ℂ E)

def affineJetValue : HMap ℂ F :=
  superpose hP (affine_differentiable p a) (norm_nonneg a) (affine_fderiv_bound p a) u

def affineJetDeriv : HMap ℂ (ℂ →L[ℝ] F) :=
  bilinCLM (X := ℂ) (α := (1:ℝ)/3) (ContinuousLinearMap.compL ℝ ℂ E F)
    (superpose hDP (affine_differentiable p a) (norm_nonneg a) (affine_fderiv_bound p a) u)
    (const _ a+jetDerivCLM _ u)

@[simp] lemma affineJetValue_value (z : ℂ) :
    valueCLM _ (affineJetValue hP p a u) z = P (affineCurve p a u z) := rfl

@[simp] lemma affineJetDeriv_value (z : ℂ) :
    valueCLM _ (affineJetDeriv hDP p a u) z =
      (fderiv ℝ P (affineCurve p a u z)).comp (a+cDeriv u z) := rfl

def affineJetSuperpose : COne ℂ F :=
  ⟨(affineJetValue hP p a u,affineJetDeriv hDP p a u), by
    intro z
    exact ((hP.smooth.differentiable (by simp) (affineCurve p a u z)).hasFDerivAt.comp z
      (affineCurve_hasFDerivAt p a u z))⟩

@[simp] lemma affineJetSuperpose_value (z : ℂ) :
    cValue (affineJetSuperpose hP hDP p a u) z = P (affineCurve p a u z) := rfl

def compactPerturbationJet {P : E → F} (hP : ContDiff ℝ ∞ P) (c : F)
    (hc : HasCompactSupport (fun x => P x-c)) (p : E) (a : ℂ →L[ℝ] E) (u : COne ℂ E) : COne ℂ F :=
  affineJetSuperpose (boundedCThree_of_compactPerturbation hP c hc)
    (boundedCThree_of_compactSupport (hP.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
      (by
        have he : fderiv ℝ (fun x => P x-c) = fderiv ℝ P := funext fun x => fderiv_sub_const c
        rw [←he]
        exact hc.fderiv ℝ)) p a u

@[simp] lemma compactPerturbationJet_value {P : E → F} (hP : ContDiff ℝ ∞ P) (c : F)
    (hc : HasCompactSupport (fun x => P x-c)) (p : E) (a : ℂ →L[ℝ] E) (u : COne ℂ E) (z : ℂ) :
    cValue (compactPerturbationJet hP c hc p a u) z = P (affineCurve p a u z) := rfl

end HolderCompletion

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end


