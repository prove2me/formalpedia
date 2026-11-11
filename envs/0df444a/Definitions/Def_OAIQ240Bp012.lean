-- Prove2me | Definitions.Def_OAIQ240Bp012
-- name    : OAIQ240Bp012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T00:28:17.833369+00:00
-- url     : https://prove2.me/theorems/12a73c20-9fd9-4fd1-a8e2-b81d903a44ca
-- title:
--   Definitions bundle OAIQ240Bp012 of the split of OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 41 declarations of OpenAI's Lean: 21 definitions and 20 theorems. The definitions and types are `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedCREquiv`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedCoefficientEquiv`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedInverse`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.scsInst3`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.scsInst4`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.scsInst5`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.scsInst6`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.scsInst7`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.scsInst8`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothSuperInst12`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothSuperInst9`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.supportedCoefficientEquiv`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.transInst3`, `OAI.HigherDimensionalBallPacking.Rigidity.parametricInfiniteSolution`, `OAI.HigherDimensionalBallPacking.Rigidity.parametricSolution`, `OAI.HigherDimensionalBallPacking.Rigidity.planarPullback`, `OAI.PackingSufficiencySupport.CubicModel.BaseCurve`, `OAI.PackingSufficiencySupport.CubicModel.projection`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusChart`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.realInfinityChart`, `OAI.SymplecticBallPacking.Hamiltonian.angularOneForm`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `BallPacking_Cauchy_GreenFormula`, `BallPacking_Compactness_AffineCorrectionInfinity`, `BallPacking_Compactness_GradientBounds`, `BallPacking_Fredholm_NonlinearReduction`, `BallPacking_Fredholm_SurjectiveParametricReduction`, `BallPacking_Holder_MarkedFrame`, `BallPacking_Holder_MarkedJets`, `BallPacking_Moduli_SmoothZeroCharts`, `BallPacking_Rigidity_CurveArea`, `BallPacking_Rigidity_RadialForm`, `BallPacking_Surfaces_QuadricAnnulusDomain`, `BallPacking_Surfaces_QuadricCurveManifold`, `BallPacking_Surfaces_QuadricInfinityDiffeomorph`.
--
--   **Imports.** It imports the bundle `OAIQ240Bp025` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ240Bp014`, `OAIQ240Bp015` and `OAIQ240Bp016`; the proof of `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_disk_nonlinear_jet_cauchy`.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ240Bp025

section
-- module Solutions.OAIQ240_BP.BallPacking_Rigidity_RadialForm
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SymplecticBallPacking.Hamiltonian
open scoped ContDiff Topology
open Set Function Filter MeasureTheory

@[simp] theorem radiusSq_polar (R t : ℝ) : radiusSq (polarCoord.symm (R,t)) = R^2 := by
  simp only [radiusSq,polarCoord_symm_apply]
  linear_combination R^2 * Real.cos_sq_add_sin_sq t

def angularOneForm (z : Plane) : Plane →L[ℝ] ℝ := (radiusSq z)⁻¹ • planarArea z

end SymplecticBallPacking.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Cauchy_GreenFormula
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
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

lemma globalCauchyDerivative_curl {g : ℂ → E} (hgC : Continuous g) (hi : Integrable g)
    {H : ℝ} (hH : 0 ≤ H) (hg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) (x : ℂ) :
    curlJet (globalCauchyDerivative g x) = (2*Complex.I) • g x := by
  rw [globalCauchyDerivative,curlJet_smul,map_add,
    cutoffCauchyDerivative_curl schauderBump hgC hH hg x,tailCauchyDerivative_curl hgC hi x]
  simp_rw [smul_sub]
  rw [integral_sub (bumpCurlKernel_smul_integrable schauderBump hgC x)
      ((bumpCurlKernel_integrable schauderBump).smul_const (g x)),integral_smul_const,
    bumpCurlKernel_integral]
  have he : (∫ w : ℂ, bumpCurlKernel schauderBump w • g (x-w)) -
      (-(2*Real.pi*Complex.I)) • g x + -(∫ w : ℂ, bumpCurlKernel schauderBump w • g (x-w)) =
      (2*Real.pi*Complex.I) • g x := by rw [neg_smul]; abel
  rw [he,smul_smul]
  congr 1
  field_simp [Real.pi_ne_zero]

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_MarkedJets
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineJetDeriv_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineJetSuperpose_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineJetValue_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.bumpHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compactPerturbationJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.constHolderCLM_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.cutoffSlope_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeSum_deriv _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeSum_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.holderCoefficientAction_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.holderTranslate_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetDirectional_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetTranslate_deriv _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetTranslate_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.localizedJetValue_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedCoefficientAction_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.restrictedValue_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.sourceCutoff_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.supportedCoefficientAction_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.supportedSourceCutoff_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.truncateShift_value _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
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
local instance markedJetInst4_reea5de_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedJetInst5
local instance markedJetInst6_reea5de_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedJetInst7
local instance markedJetInst8_reea5de_1 : NormedSpace ℝ (HMap ℂ (ℂ →L[ℝ] E)) := inferInstance
omit [CompleteSpace E] in
lemma standardJetCR_injective_zeroMarked {u v : COne ℂ E}
    (hu : cValue u 0 = 0) (hv : cValue v 0 = 0)
    (he : standardJetCR u = standardJetCR v) : u = v := by
  have hd : Differentiable ℂ (cValue (u-v)) := by
    intro z
    apply complex_differentiable_of_curl_zero (c_differentiable (u-v) z)
    rw [c_fderiv]
    have h := congrArg (fun h : HMap ℂ E => valueCLM _ h z)
      (show standardJetCR (u-v) = 0 by rw [map_sub,he,sub_self])
    change -curlJet (cDeriv (u-v) z) = 0 at h
    exact neg_eq_zero.mp h
  apply cValue_ext
  intro z
  have h := hd.apply_eq_apply_of_bounded (cValue (u-v)).isBounded_range z 0
  change cValue u z-cValue v z = cValue u 0-cValue v 0 at h
  rw [hu,hv,sub_self] at h
  exact sub_eq_zero.mp h

variable {K : Set ℂ} (hK : IsCompact K)

local instance markedJetInst9_reea5de_1 : NormedAddCommGroup (supportedHolder (E := E) K) := inferInstance
local instance markedJetInst10_reea5de_1 : NormedSpace ℝ (supportedHolder (E := E) K) := inferInstance
lemma standardHolderInverse_zero (g : supportedHolder (E := E) K) :
    cValue (standardHolderInverse hK g) 0 = 0 := by rw [standardHolderInverse_value,sub_self,smul_zero]

lemma standardHolderInverse_residual (g : supportedHolder (E := E) K) :
    standardJetCR (standardHolderInverse hK g) = g.val := by
  rw [standardHolderInverse,ContinuousLinearMap.comp_apply,standardJetCR_zeroNormalize]
  apply value_ext
  intro z
  change -curlJet (((ContinuousLinearMap.lsmul ℝ ℂ (E := E)) (Complex.I/2)).comp
    (globalCauchyDerivative (valueCLM _ g.val) z)) = valueCLM _ g.val z
  have he : ((ContinuousLinearMap.lsmul ℝ ℂ (E := E)) (Complex.I/2)).comp
      (globalCauchyDerivative (valueCLM _ g.val) z) =
      (Complex.I/2) • globalCauchyDerivative (valueCLM _ g.val) z := rfl
  rw [he,curlJet_smul,globalCauchyDerivative_curl (valueCLM _ g.val).continuous
    (supportedHolder_integrable hK g) (norm_nonneg g.val)
    (by simpa only [dist_eq_norm] using norm_sub_value_le g.val),smul_smul]
  norm_num [Complex.I_mul_I,← mul_assoc]


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
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothSuperInst3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothSuperInst4
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothSuperInst5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothSuperInst6
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothSuperInst7
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothSuperInst8
local instance smoothSuperInst9 : NormedAddCommGroup (HMap D (E →L[ℝ] F)) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothSuperInst10
local instance smoothSuperInst11_reea5de_1 : ContinuousSMul ℝ (COne D E) := IsBoundedSMul.continuousSMul
local instance smoothSuperInst12 : NormedAddCommGroup (COne D E →L[ℝ] HMap D F) :=
  ContinuousLinearMap.toNormedAddCommGroup


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

variable {K : Set ℂ} (hK : IsCompact K)

local instance markedAffineInst1_reea5de_1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance markedAffineInst2_reea5de_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance markedAffineInst3_reea5de_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance markedAffineInst4_reea5de_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance markedAffineInst5_reea5de_1 : NormedAddCommGroup (markedModel (E := E) K) := inferInstance
local instance markedAffineInst6_reea5de_1 : NormedSpace ℝ (markedModel (E := E) K) := inferInstance
local instance markedAffineInst7_reea5de_1 : NormedAddCommGroup (supportedHolder (E := E) K) := inferInstance
local instance markedAffineInst8_reea5de_1 : NormedSpace ℝ (supportedHolder (E := E) K) := inferInstance
def markedInverse : supportedHolder (E := E) K →L[ℝ] markedModel (E := E) K :=
  (standardHolderInverse hK).codRestrict (markedModel K) (fun g => by
    apply (mem_markedModel K _).mpr
    refine ⟨standardHolderInverse_zero hK g, ?_⟩
    rw [standardHolderInverse_residual]; exact g.property)

def markedCREquiv : markedModel (E := E) K ≃L[ℝ] supportedHolder (E := E) K :=
  ContinuousLinearEquiv.equivOfInverse (markedCR (E := E) (K := K)) (markedInverse (E := E) hK)
    (by
      intro u
      apply Subtype.ext
      exact standardJetCR_injective_zeroMarked
        (standardHolderInverse_zero hK (markedCR (E := E) (K := K) u)) u.property.1
        (standardHolderInverse_residual hK (markedCR (E := E) (K := K) u)))
    (by
      intro g
      apply Subtype.ext
      exact standardHolderInverse_residual hK g)



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

variable {K : Set ℂ}

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedFrameInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedFrameInst2
local instance markedFrameInst3_reea5de_1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance markedFrameInst4_reea5de_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance markedFrameInst5_reea5de_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance markedFrameInst6_reea5de_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance markedFrameInst7_reea5de_1 : NormedAddCommGroup (markedModel (E := E) K) := inferInstance
local instance markedFrameInst8_reea5de_1 : NormedSpace ℝ (markedModel (E := E) K) := inferInstance
local instance markedFrameInst9_reea5de_1 : NormedAddCommGroup (supportedHolder (E := E) K) := inferInstance
local instance markedFrameInst10_reea5de_1 : NormedSpace ℝ (supportedHolder (E := E) K) := inferInstance
def markedCoefficientEquiv (hK : IsClosed K) (M N : COne ℂ (E →L[ℝ] E)) (c d : ℝ)
    (hM : ∀ z ∉ K, cValue M z = c • ContinuousLinearMap.id ℝ E)
    (hN : ∀ z ∉ K, cValue N z = d • ContinuousLinearMap.id ℝ E)
    (hNM : ∀ z v, cValue N z (cValue M z v) = v)
    (hMN : ∀ z v, cValue M z (cValue N z v) = v) :
    markedModel (E := E) K ≃L[ℝ] markedModel (E := E) K :=
  ContinuousLinearEquiv.equivOfInverse (markedCoefficientAction hK M c hM)
    (markedCoefficientAction hK N d hN)
    (by
      intro u; apply Subtype.ext; apply cValue_ext; intro z
      simpa only [markedCoefficientAction_value] using hNM z (cValue u.val z))
    (by
      intro u; apply Subtype.ext; apply cValue_ext; intro z
      simpa only [markedCoefficientAction_value] using hMN z (cValue u.val z))

def supportedCoefficientEquiv (M N : HMap ℂ (E →L[ℝ] E))
    (hNM : ∀ z v, valueCLM _ N z (valueCLM _ M z v) = v)
    (hMN : ∀ z v, valueCLM _ M z (valueCLM _ N z v) = v) :
    supportedHolder (E := E) K ≃L[ℝ] supportedHolder (E := E) K :=
  ContinuousLinearEquiv.equivOfInverse (supportedCoefficientAction M) (supportedCoefficientAction N)
    (by intro g; apply Subtype.ext; apply value_ext; intro z; exact hNM z _)
    (by intro g; apply Subtype.ext; apply value_ext; intro z; exact hMN z _)


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
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)

def planarPullback {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Plane → E) (α : E → E →L[ℝ] ℝ) (z : Plane) : Plane →L[ℝ] ℝ :=
  (α (v z)).comp (fderiv ℝ v z)


end

open scoped ContDiff Topology
open Set Function Filter MeasureTheory



end HigherDimensionalBallPacking.Rigidity
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
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.transInst1
local instance transInst2_reea5de_1 : NormedSpace ℝ (HMap D E) := inferInstance
local instance transInst3 : NormedAddCommGroup (COne D E) := inferInstance

end HigherDimensionalBallPacking.Rigidity.HolderCompletion

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Compactness_GradientBounds
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
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.scsInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.scsInst2
local instance scsInst3 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance scsInst4 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance scsInst5 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance scsInst6 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance scsInst7 : NormedAddCommGroup (HMap ℂ (E →L[ℝ] E)) := inferInstance
local instance scsInst8 : NormedSpace ℝ (HMap ℂ (E →L[ℝ] E)) := inferInstance


end
open scoped Topology BoundedContinuousFunction
open Set Filter



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_NonlinearReduction
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.OAI.ContinuousLinearMap.FredholmPackage

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter
open HolderCompletion
section
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

variable {D : X →L[ℝ] Y} (pkg : D.FredholmPackage)

variable {F : ℝ × X → Y} (hF : ContDiff ℝ ∞ F) {t : ℝ} {x : X}
  (hD : HasFDerivAt (fun y => F (t,y)) D x)

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.pfrK
local instance pfrC_reea5de_1 : FiniteDimensional ℝ pkg.decCodom.X₀ := pkg.decCodom.finite_X₀
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.pfrX
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.pfrY
def parametricInfiniteSolution : ℝ × pkg.decDom.X₀ → pkg.decDom.X₁ :=
  (parametricEssential_smooth pkg hF).contDiffAt.implicitFunction (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    (parametricEssential_invertible pkg hF hD)

def parametricSolution (v : ℝ × pkg.decDom.X₀) : X :=
  (domCoords pkg).symm (parametricInfiniteSolution pkg hF hD v,v.2)

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_SurjectiveParametricReduction
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.OAI.ContinuousLinearMap.FredholmPackage

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {D : X →L[ℝ] Y} (pkg : D.FredholmPackage)

variable {F : ℝ × X → Y} (hF : ContDiff ℝ ∞ F) {t : ℝ} {x : X}
  (hD : HasFDerivAt (fun y => F (t,y)) D x)

lemma parametricSolution_kernel_coordinate (v : ℝ × pkg.decDom.X₀) :
    ((domCoords pkg) (parametricSolution pkg hF hD v)).2=v.2 := by
  exact congrArg Prod.snd ((domCoords pkg).apply_symm_apply _)


end
open scoped Topology
open Set Function Filter



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moduli_SmoothZeroCharts
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.OAI.ContinuousLinearMap.FredholmPackage

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : ℝ × X → Y}

variable [CompleteSpace X] [CompleteSpace Y]
variable {D : X →L[ℝ] Y} (pkg : D.FredholmPackage)
variable (hF : ContDiff ℝ ∞ F) {t : ℝ} {x : X}
    (hD : HasFDerivAt (fun y => F (t,y)) D x)

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.szcK
local instance szcC_reea5de_1 : FiniteDimensional ℝ pkg.decCodom.X₀ := pkg.decCodom.finite_X₀
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.szcX
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.szcY
lemma parametricSolution_smooth_neighborhood :
    ∃ S : Set (ℝ × pkg.decDom.X₀),IsOpen S ∧ (t,((domCoords pkg) x).2)∈S ∧
      ContDiffOn ℝ ∞ (parametricSolution pkg hF hD) S := by
  obtain ⟨S,hSo,hSt,hSs⟩ := implicitFunction_smooth_neighborhood (parametricEssential_smooth pkg hF)
    (parametricEssential_invertible pkg hF hD)
  refine ⟨S,hSo,hSt,?_⟩
  exact (domCoords pkg).symm.contDiff.comp_contDiffOn (hSs.prodMk contDiffOn_snd)


end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Surfaces_QuadricCurveManifold
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Manifold
open Filter
section
variable {m : ℕ} (a : Fin m → ℂ) [ha : Fact (Injective a)] [ha0 : Fact (∀ j,a j≠0)]

theorem mem_normalChartAt (x : locus a) : (x : Affine m)∈(normalChartAt a x).ambient.source :=
  (exists_normalChart_at ha.out ha0.out x).choose_spec

end

end PackingSufficiencySupport.DiagonalQuadrics

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Surfaces_QuadricAnnulusDomain
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Topology
open Set Function Filter
open scoped Manifold
open Manifold
variable (m : ℕ)

theorem plus_coordinate {x : Affine (m+2)} (hx : x∈locus (parameters m)) :
    plus (annulusCoordinate m x)=x.2 0 := by
  rw [plus,inverse_coordinate m hx,annulusCoordinate_apply]
  ring

theorem minus_coordinate {x : Affine (m+2)} (hx : x∈locus (parameters m)) :
    minus (annulusCoordinate m x)=x.2 1 := by
  rw [minus,inverse_coordinate m hx,annulusCoordinate_apply]
  ring

theorem baseSquare_coordinate {x : Affine (m+2)} (hx : x∈locus (parameters m)) :
    baseSquare (annulusCoordinate m x)=x.1^2 := by
  have h0 := mem_locus.mp hx 0
  rw [baseSquare,plus_coordinate m hx]
  simp only [parameters_zero] at h0
  linear_combination h0

theorem annulusPoint_positive {s : ℂ} (hs : s∈annulusDomain m) :
    0<(annulusPoint m s).1.re ∧
    ∀ j : Fin (m+2),1<j.val → 0<((annulusPoint m s).2 j).im := by
  refine ⟨sqrt_re_pos hs.2.1,?_⟩
  intro j hj
  have hj0 : j≠0 := by intro h; subst j; simp at hj
  have hj1 : j≠1 := by intro h; subst j; simp at hj
  simpa only [annulusPoint,ite_eq_right hj0,ite_eq_right hj1,Complex.mul_im,
    Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_add] using sqrt_re_pos (hs.2.2 j hj)

theorem annulusPoint_coordinate {x : Surface m} (hx : x∈annulusBranch m) :
    annulusPoint m (annulusCoordinate m x.val)=x.val := by
  apply Prod.ext
  · change Complex.sqrt (baseSquare (annulusCoordinate m x.val))=x.val.1
    rw [baseSquare_coordinate m x.property]
    exact sqrt_of_sq_pos hx.2.1
  · funext j
    by_cases hj0 : j=0
    · subst j
      exact (annulusPoint_zero m _).trans (plus_coordinate m x.property)
    by_cases hj1 : j=1
    · subst j
      exact (annulusPoint_one m _).trans (minus_coordinate m x.property)
    · have hj : 1<j.val := by
        have h0 : j.val≠0 := fun h => hj0 (Fin.ext h)
        have h1 : j.val≠1 := fun h => hj1 (Fin.ext (by simpa using h))
        omega
      have hp : 0<(-Complex.I*x.val.2 j).re := by
        simpa only [Complex.mul_re,Complex.neg_re,Complex.neg_im,Complex.I_re,
          Complex.I_im,neg_zero,zero_mul,neg_mul,one_mul,zero_sub,neg_neg] using hx.2.2 j hj
      have he : parameters m j-baseSquare (annulusCoordinate m x.val)=(-Complex.I*x.val.2 j)^2 := by
        rw [baseSquare_coordinate m x.property,mul_pow,neg_pow,Complex.I_sq]
        have hjx := mem_locus.mp x.property j
        linear_combination hjx
      simp only [annulusPoint,ite_eq_right hj0,ite_eq_right hj1,he,sqrt_of_sq_pos hp]
      rw [← mul_assoc]
      simp

def annulusChart : OpenPartialHomeomorph (Surface m) ℂ where
  toFun x := annulusCoordinate m x.val
  invFun := annulusInverse m
  source := annulusBranch m
  target := annulusDomain m
  map_source' _ hx := hx.1
  map_target' s hs := by
    refine ⟨?_,?_⟩
    · rw [annulusInverse_val m hs.1,annulusCoordinate_point]
      exact hs
    · rw [annulusInverse_val m hs.1]
      exact annulusPoint_positive m hs
  left_inv' x hx := by
    apply Subtype.ext
    rw [annulusInverse_val m hx.1.1]
    exact annulusPoint_coordinate m hx
  right_inv' s hs := by
    rw [annulusInverse_val m hs.1,annulusCoordinate_point]
  open_source := annulusBranch_isOpen m
  open_target := annulusDomain_isOpen m
  continuousOn_toFun := ((annulusCoordinate m).continuous.comp continuous_subtype_val).continuousOn
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    apply continuous_induced_rng.mpr
    have hc : ContinuousOn (annulusPoint m) (annulusDomain m) :=
      fun s hs => (annulusPoint_contDiffAt m hs).continuousAt.continuousWithinAt
    rw [continuousOn_iff_continuous_domRestrict] at hc
    exact hc.congr fun s => (annulusInverse_val m s.property.1).symm

@[simp] theorem annulusChart_apply (x : Surface m) : annulusChart m x=annulusCoordinate m x.val := rfl
@[simp] theorem annulusChart_source : (annulusChart m).source=annulusBranch m := rfl
@[simp] theorem annulusChart_target : (annulusChart m).target=annulusDomain m := rfl

end PackingSufficiencySupport.DiagonalQuadrics.Explicit

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology
open Set Function Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit

abbrev BaseCurve := Surface 0

 def projection (z : Affine 2) : PlaneBase := (z.2 0-z.1,z.2 1-z.1)

end PackingSufficiencySupport.CubicModel
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Surfaces_QuadricInfinityDiffeomorph
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusCoordinate_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusCoordinate_point _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusInverse_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold
open Hamiltonian
open scoped BigOperators
section
variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]
  (ε : Fin m → Bool)

def realInfinityChart : OpenPartialHomeomorph RealModel (locus a) :=
  Complex.equivRealProdCLM.symm.toHomeomorph.toOpenPartialHomeomorph.trans (infinityChart a ε).symm

omit [Fact (Injective a)] [Fact (∀ j,a j≠0)] in
@[simp] theorem realInfinityChart_source :
    (realInfinityChart a ε).source=Complex.equivRealProdCLM.symm ⁻¹' infinityDomain a := by
  simp [realInfinityChart]

omit [Fact (Injective a)] [Fact (∀ j,a j≠0)] in
@[simp] theorem realInfinityChart_target : (realInfinityChart a ε).target=infinityBranch a ε := by
  simp [realInfinityChart]

omit [Fact (Injective a)] [Fact (∀ j,a j≠0)] in
@[simp] theorem realInfinityChart_apply (x : RealModel) :
    realInfinityChart a ε x=infinityInverse a ε (Complex.equivRealProdCLM.symm x) := rfl

omit [Fact (Injective a)] [Fact (∀ j,a j≠0)] in
@[simp] theorem realInfinityChart_symm_apply (x : locus a) :
    (realInfinityChart a ε).symm x=Complex.equivRealProdCLM x.val.1⁻¹ := rfl

end

end PackingSufficiencySupport.DiagonalQuadrics

end

end OAI
end


