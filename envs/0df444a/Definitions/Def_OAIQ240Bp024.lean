-- Prove2me | Definitions.Def_OAIQ240Bp024
-- name    : OAIQ240Bp024
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T00:12:28.640255+00:00
-- url     : https://prove2.me/theorems/775abfb2-4a07-4081-ac54-39197a04649e
-- title:
--   Definitions bundle OAIQ240Bp024 of the split of OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 37 declarations of OpenAI's Lean: 22 definitions and 15 theorems. The definitions and types are `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineCurve`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineCutInst1`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineCutInst2`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.cutoffCoordinate`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.cutoffSlope`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.derivativeAssembly`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.holderCoefficientAction`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetDirection`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedCoefficientAction`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedModel`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothSuperInst10`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothSuperInst13`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothSuperInst3`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothSuperInst4`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothSuperInst5`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothSuperInst6`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothSuperInst7`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothSuperInst8`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.standardHolderInverse`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.structureAlong`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.structureAlongDeriv`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.supportedCoefficientAction`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`BallPacking_Holder_MarkedFrame`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Holder/MarkedFrame.lean), [`BallPacking_Holder_MarkedJets`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Holder/MarkedJets.lean).
--
--   **Imports.** It imports the bundle `OAIQ240Bp023` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ240Bp008`.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ240Bp023

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_MarkedJets
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
open Set Filter MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedJetInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedJetInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedJetInst3
local instance markedJetInst4_racb561_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedJetInst5
local instance markedJetInst6_racb561_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedJetInst7
local instance markedJetInst8_racb561_1 : NormedSpace ℝ (HMap ℂ (ℂ →L[ℝ] E)) := inferInstance
omit [CompleteSpace E] in
@[simp] lemma standardJetCR_value (u : COne ℂ E) (z : ℂ) :
    valueCLM _ (standardJetCR u) z = cDeriv u z Complex.I - Complex.I • cDeriv u z 1 := by
  change -(Complex.I • cDeriv u z 1-cDeriv u z Complex.I) = _
  abel

variable {K : Set ℂ} (hK : IsCompact K)

local instance markedJetInst9_racb561_1 : NormedAddCommGroup (supportedHolder (E := E) K) := inferInstance
local instance markedJetInst10_racb561_1 : NormedSpace ℝ (supportedHolder (E := E) K) := inferInstance
def standardHolderInverse : supportedHolder (E := E) K →L[ℝ] COne ℂ E :=
  zeroNormalize.comp ((mapJetBilinear (D := ℂ) (E := E) (F := E) ((ContinuousLinearMap.lsmul ℝ ℂ (E := E)) (Complex.I/2))).comp
    (supportedCauchyCLM hK))

@[simp] lemma standardHolderInverse_value (g : supportedHolder (E := E) K) (z : ℂ) :
    cValue (standardHolderInverse hK g) z =
      (Complex.I/2) • (cauchyTransform (valueCLM _ g.val) z-cauchyTransform (valueCLM _ g.val) 0) := by
  simp only [standardHolderInverse, ContinuousLinearMap.comp_apply,zeroNormalize_value,
    mapJetBilinear_value,ContinuousLinearMap.lsmul_apply,supportedCauchyCLM_value,smul_sub]


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
universe u v
variable {D : Type v} {E F : Type u}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothSuperInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothSuperInst2
local instance smoothSuperInst3 : NormedAddCommGroup (COne D E) := inferInstance
local instance smoothSuperInst4 : NormedSpace ℝ (COne D E) := inferInstance
local instance smoothSuperInst5 : NormedAddCommGroup (HMap D E) := inferInstance
local instance smoothSuperInst6 : NormedSpace ℝ (HMap D E) := inferInstance
local instance smoothSuperInst7 : NormedAddCommGroup (HMap D F) := inferInstance
local instance smoothSuperInst8 : NormedSpace ℝ (HMap D F) := inferInstance
local instance smoothSuperInst9_racb561_1 : NormedAddCommGroup (HMap D (E →L[ℝ] F)) := inferInstance
local instance smoothSuperInst10 : NormedSpace ℝ (HMap D (E →L[ℝ] F)) := inferInstance
local instance smoothSuperInst11_racb561_1 : ContinuousSMul ℝ (COne D E) := IsBoundedSMul.continuousSMul
local instance smoothSuperInst12_racb561_1 : NormedAddCommGroup (COne D E →L[ℝ] HMap D F) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance smoothSuperInst13 : NormedSpace ℝ (COne D E →L[ℝ] HMap D F) :=
  ContinuousLinearMap.toNormedSpace

def derivativeAssembly : HMap D (E →L[ℝ] F) →L[ℝ] (COne D E →L[ℝ] HMap D F) :=
  ((bilinCLM (X := D) (α := (1:ℝ)/3) (ContinuousLinearMap.apply (E := E) ℝ F).flip).precompR
    (COne D E)).flip (jetValueCLM (D := D) (E := E) ((1:ℝ)/3))

@[simp] lemma derivativeAssembly_value (A : HMap D (E →L[ℝ] F)) (u : COne D E) (x : D) :
    valueCLM _ (derivativeAssembly (D := D) (E := E) (F := F) A u) x = valueCLM _ A x (cValue u x) := rfl


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.crSectInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.crSectInst2
local instance crSectInst3_racb561_1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance crSectInst4_racb561_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance crSectInst5_racb561_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance crSectInst6_racb561_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance crSectInst7_racb561_1 : NormedAddCommGroup (HMap ℂ (E →L[ℝ] E)) := inferInstance
local instance crSectInst8_racb561_1 : NormedSpace ℝ (HMap ℂ (E →L[ℝ] E)) := inferInstance
def jetDirection (v : ℂ) : COne ℂ E →L[ℝ] HMap ℂ E :=
  (mapCLM _ (ContinuousLinearMap.apply ℝ E v)).comp (jetDerivCLM _)

@[simp] lemma jetDirection_value (v : ℂ) (u : COne ℂ E) (z : ℂ) :
    valueCLM _ (jetDirection v u) z = cDeriv u z v := rfl

def affineCurve (p : E) (a : ℂ →L[ℝ] E) (u : COne ℂ E) (z : ℂ) : E :=
  affine p a z + cValue u z

lemma affineCurve_hasFDerivAt (p : E) (a : ℂ →L[ℝ] E) (u : COne ℂ E) (z : ℂ) :
    HasFDerivAt (affineCurve p a u) (a+cDeriv u z) z :=
  (affine_hasFDerivAt p a z).add (c_hasFDerivAt u z)

variable {J : E → E →L[ℝ] E} (hJ : BoundedCThree J)

def structureAlong (p : E) (a : ℂ →L[ℝ] E) (u : COne ℂ E) : HMap ℂ (E →L[ℝ] E) :=
  superpose hJ (affine_differentiable p a) (norm_nonneg a) (affine_fderiv_bound p a) u

@[simp] lemma structureAlong_value (p : E) (a : ℂ →L[ℝ] E) (u : COne ℂ E) (z : ℂ) :
    valueCLM _ (structureAlong hJ p a u) z = J (affineCurve p a u z) := rfl

def structureAlongDeriv (p : E) (a : ℂ →L[ℝ] E) (u : COne ℂ E) :
    COne ℂ E →L[ℝ] HMap ℂ (E →L[ℝ] E) :=
  superposeDeriv hJ (affine_differentiable p a) (norm_nonneg a) (affine_fderiv_bound p a) u

@[simp] lemma structureAlongDeriv_value (p : E) (a : ℂ →L[ℝ] E)
    (u h : COne ℂ E) (z : ℂ) :
    valueCLM _ (structureAlongDeriv hJ p a u h) z =
      fderiv ℝ J (affineCurve p a u z) (cValue h z) := rfl


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

local instance markedAffineInst1_racb561_1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance markedAffineInst2_racb561_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance markedAffineInst3_racb561_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance markedAffineInst4_racb561_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
def markedModel (K : Set ℂ) : Submodule ℝ (COne ℂ E) :=
  (jetEval (E := E) 0).ker ⊓ (supportedHolder K).comap standardJetCR.toLinearMap

variable {K : Set ℂ} (hK : IsCompact K)

omit [CompleteSpace E] in
@[simp] lemma complexSlope_apply (a : E) (z : ℂ) : complexSlope a z = z • a := rfl



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

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedFrameInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedFrameInst2
local instance markedFrameInst3_racb561_1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance markedFrameInst4_racb561_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance markedFrameInst5_racb561_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance markedFrameInst6_racb561_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
omit [CompleteSpace E] in
lemma coefficientDeriv_zero_outside {K : Set ℂ} (hK : IsClosed K)
    (M : COne ℂ (E →L[ℝ] E)) (c : ℝ)
    (hM : ∀ z ∉ K, cValue M z = c • ContinuousLinearMap.id ℝ E)
    {z : ℂ} (hz : z ∉ K) : cDeriv M z = 0 := by
  have he : (cValue M : ℂ → E →L[ℝ] E) =ᶠ[𝓝 z] fun _ => c • ContinuousLinearMap.id ℝ E := by
    filter_upwards [hK.isOpen_compl.mem_nhds hz] with w hw
    exact hM w hw
  rw [← c_fderiv,he.fderiv_eq]
  exact (hasFDerivAt_const (𝕜 := ℝ) (c • ContinuousLinearMap.id ℝ E) z).fderiv

omit [CompleteSpace E] in
lemma coefficientAction_mem_marked {K : Set ℂ} (hK : IsClosed K)
    (M : COne ℂ (E →L[ℝ] E)) (c : ℝ)
    (hM : ∀ z ∉ K, cValue M z = c • ContinuousLinearMap.id ℝ E)
    {u : COne ℂ E} (hu : u ∈ markedModel K) : coefficientAction M u ∈ markedModel K := by
  refine ⟨?_,?_⟩
  · change cValue M 0 (cValue u 0) = 0
    have hu0 : cValue u 0 = 0 := hu.1
    rw [hu0,map_zero]
  · change standardJetCR (coefficientAction M u) ∈ supportedHolder K
    apply (mem_supportedHolder _ K).mpr
    intro z hz
    have hzD := coefficientDeriv_zero_outside hK M c hM hz
    have hzC := hM z hz
    have huZ := (mem_supportedHolder (standardJetCR u) K).mp hu.2 z hz
    rw [standardJetCR_value] at huZ
    rw [standardJetCR_value,coefficientAction_deriv]
    simp only [add_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply,hzD,zero_apply,add_zero,hzC,
      smul_apply,ContinuousLinearMap.id_apply]
    rw [smul_comm Complex.I c,←smul_sub]
    exact (congrArg (fun v : E => c • v) huZ).trans (smul_zero c)

variable {K : Set ℂ}

local instance markedFrameInst7_racb561_1 : NormedAddCommGroup (markedModel (E := E) K) := inferInstance
local instance markedFrameInst8_racb561_1 : NormedSpace ℝ (markedModel (E := E) K) := inferInstance
local instance markedFrameInst9_racb561_1 : NormedAddCommGroup (supportedHolder (E := E) K) := inferInstance
local instance markedFrameInst10_racb561_1 : NormedSpace ℝ (supportedHolder (E := E) K) := inferInstance
def markedCoefficientAction (hK : IsClosed K) (M : COne ℂ (E →L[ℝ] E)) (c : ℝ)
    (hM : ∀ z ∉ K, cValue M z = c • ContinuousLinearMap.id ℝ E) :
    markedModel (E := E) K →L[ℝ] markedModel (E := E) K :=
  (coefficientAction M).restrict (fun _u hu => coefficientAction_mem_marked hK M c hM hu)

omit [CompleteSpace E] in
@[simp] lemma markedCoefficientAction_value (hK : IsClosed K) (M : COne ℂ (E →L[ℝ] E)) (c : ℝ)
    (hM : ∀ z ∉ K, cValue M z = c • ContinuousLinearMap.id ℝ E)
    (u : markedModel (E := E) K) (z : ℂ) :
    cValue (markedCoefficientAction hK M c hM u).val z = cValue M z (cValue u.val z) := rfl

def holderCoefficientAction (M : HMap ℂ (E →L[ℝ] E)) : HMap ℂ E →L[ℝ] HMap ℂ E :=
  bilinCLM (X := ℂ) (α := (1:ℝ)/3) (ContinuousLinearMap.apply (E := E) ℝ E).flip M

omit [CompleteSpace E] in
@[simp] lemma holderCoefficientAction_value (M : HMap ℂ (E →L[ℝ] E)) (g : HMap ℂ E) (z : ℂ) :
    valueCLM _ (holderCoefficientAction M g) z = valueCLM _ M z (valueCLM _ g z) := rfl

def supportedCoefficientAction (M : HMap ℂ (E →L[ℝ] E)) :
    supportedHolder (E := E) K →L[ℝ] supportedHolder (E := E) K :=
  (holderCoefficientAction M).restrict (fun g hg => by
    apply (mem_supportedHolder _ K).mpr
    intro z hz
    rw [holderCoefficientAction_value,(mem_supportedHolder g K).mp hg z hz,map_zero])

omit [CompleteSpace E] in
@[simp] lemma supportedCoefficientAction_value (M : HMap ℂ (E →L[ℝ] E))
    (g : supportedHolder (E := E) K) (z : ℂ) :
    valueCLM _ (supportedCoefficientAction M g).val z = valueCLM _ M z (valueCLM _ g.val z) := rfl


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance affineCutInst1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance affineCutInst2 : NormedSpace ℝ (COne ℂ E) := inferInstance

omit [CompleteSpace E] in
@[simp] lemma complexSlopeCLM_apply (a : E) : complexSlopeCLM a = complexSlope a := rfl

variable (b : ContDiffBump (0:ℂ))

local instance affineCutInst3_racb561_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance affineCutInst4_racb561_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
def cutoffCoordinate : COne ℂ ℂ :=
  ofBoundedCThree (boundedCThree_of_compactSupport (cutoffCoordinate_smooth b) (cutoffCoordinate_compact b))

@[simp] lemma cutoffCoordinate_value (z : ℂ) : cValue (cutoffCoordinate b) z = b z • z := rfl

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineCutInst5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineCutInst6
def cutoffSlope : E →L[ℝ] COne ℂ E :=
  ((mapJetBilinear (D := ℂ) (E := ℂ) (F := E)).flip (cutoffCoordinate b)).comp complexSlopeCLM


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end


