-- Prove2me | Definitions.Def_OAIQ240Bp023
-- name    : OAIQ240Bp023
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:55:49.842333+00:00
-- url     : https://prove2.me/theorems/d059d730-e830-4152-b794-fb19c630781f
-- title:
--   Definitions bundle OAIQ240Bp023 of the split of OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 41 declarations of OpenAI's Lean: 13 definitions and 28 theorems. The definitions and types are `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.constJet`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.constJetCLM`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetEval`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedJetInst3`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedJetInst5`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedJetInst7`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.schauderConstant`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.standardJetCR`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.supportedCauchy`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.supportedCauchyCLM`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.zeroNormalize`, `OAI.SymplecticBallPacking.Hamiltonian.coordinateForm`, `OAI.SymplecticBallPacking.Hamiltonian.planarDot`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`BallPacking_Cauchy_GreenFormula`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Cauchy/GreenFormula.lean), [`BallPacking_Holder_HolderTaylor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Holder/HolderTaylor.lean), [`BallPacking_Holder_MarkedJets`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Holder/MarkedJets.lean), [`BallPacking_Rigidity_RadialForm`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Rigidity/RadialForm.lean).
--
--   **Imports.** It imports the bundles `OAIQ240Bp005` and `OAIQ240Bp006` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ240Bp024`; the statement `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_regularityTranslation_smooth`; the proofs of `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_completed_markedCurve_contDiff`, `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_fullLineEquation_contDiff` and `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_regularityTranslation_smooth`.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ240Bp005
import Definitions.Def_OAIQ240Bp006

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_HolderTaylor
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped Topology
open Set Filter
open scoped ContDiff
open MeasureTheory
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

lemma cutoffCauchy_fderiv_bound (b : ContDiffBump (0:ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : ℂ → E, Continuous g → ∀ H : ℝ, 0 ≤ H →
      (∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) → ∀ x : ℂ,
      ‖cutoffCauchyDerivative b g x‖ ≤ C*H := by
  obtain ⟨C,hC,hCb⟩ := cutoff_smoothCauchyKernel_bound b
  let L : ℝ := (C+3)*(∫ w : ℂ, cauchySchauderWeight b.rOut w)
  have hw0 (w : ℂ) : 0 ≤ cauchySchauderWeight b.rOut w := by
    apply indicator_nonneg _ w
    intro z _
    exact add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (norm_nonneg _) _)
  have hL : 0 ≤ L := mul_nonneg (by linarith) (integral_nonneg hw0)
  refine ⟨L,hL,?_⟩
  intro g hgC H hH hg x
  apply le_of_tendsto (cutoff_smoothCauchyKernel_derivative_tendsto b hgC hH hg x).norm
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have he := compact_kernel_convolution_derivative_bound
    (K := fun w => b w • smoothCauchyKernel δ w)
    (b.contDiff.smul (smoothCauchyKernel_smooth hδ))
    (b.hasCompactSupport.smul_right (f' := smoothCauchyKernel δ)) hgC
    ((cauchySchauderWeight_integrable b.rOut).const_mul ((C+3)*H))
    (cutoff_smoothCauchyKernel_schauder_bound b hC hCb hH hg hδ) x
  apply he.trans_eq
  rw [integral_const_mul]
  dsimp only [L]
  ring

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma tailCauchy_hasFDerivAt {g : ℂ → E} (hg : Continuous g) (hi : Integrable g) (x : ℂ) :
    HasFDerivAt (tailCauchyTransform g) (tailCauchyDerivative g x) x := by
  obtain ⟨A,B,hA,hB,hjet,hL⟩ := tailCauchyKernel_bounds
  have hc : Continuous (tailCauchyKernel 0) := tailCauchyKernel_contDiff_one.continuous
  have hm (z : ℂ) : Continuous (fun w => tailCauchyKernel 0 (z-w) • g w) :=
    (hc.comp (continuous_const.sub continuous_id)).smul hg
  have ht (z : ℂ) : Integrable (fun w => tailCauchyKernel 0 (z-w) • g w) :=
    hi.norm.mono' (hm z).aestronglyMeasurable (Eventually.of_forall fun w => by
      rw [norm_smul]; exact (mul_le_mul_of_nonneg_right (hjet _).1 (norm_nonneg _)).trans_eq (one_mul _))
  have he : tailCauchyTransform g = fun z => ∫ w : ℂ, tailCauchyKernel 0 (z-w) • g w :=
    funext (tailCauchyTransform_eq g)
  rw [he]
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := univ) (bound := fun w => A*‖g w‖)
    (F' := tailIntegralJet g) (univ_mem) (Eventually.of_forall fun z => (hm z).aestronglyMeasurable)
    (ht x) (tailIntegralJet_continuous hg x).aestronglyMeasurable
  · exact Eventually.of_forall fun w z _ => tailIntegralJet_bound hA (fun z => (hjet z).2) g z w
  · exact hi.norm.const_mul A
  · apply Eventually.of_forall
    intro w z _
    have hd := (tailCauchyKernel_hasFDerivAt (z-w)).comp z ((hasFDerivAt_id z).sub_const w)
    have hh := ((ContinuousLinearMap.lsmul ℝ ℂ).flip (g w)).hasFDerivAt.comp z hd
    simpa only [ContinuousLinearMap.comp_id, Function.comp_def, id_eq,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply, tailIntegralJet] using hh

omit [CompleteSpace E] in
lemma tailCauchy_value_bound {g : ℂ → E} (hi : Integrable g) (x : ℂ) :
    ‖tailCauchyTransform g x‖ ≤ ∫ w : ℂ, ‖g w‖ := by
  rw [tailCauchyTransform_eq]
  obtain ⟨A,B,hA,hB,hjet,hL⟩ := tailCauchyKernel_bounds
  apply norm_integral_le_of_norm_le hi.norm
  exact Eventually.of_forall fun w => by
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_right (hjet _).1 (norm_nonneg _)).trans_eq (one_mul _)

omit [CompleteSpace E] in
lemma tailCauchy_derivative_bounds :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ g : ℂ → E, Continuous g → Integrable g →
      (∀ x, ‖tailCauchyDerivative g x‖ ≤ A*(∫ w : ℂ, ‖g w‖)) ∧
      (∀ x y, ‖tailCauchyDerivative g x-tailCauchyDerivative g y‖ ≤
        (B*(∫ w : ℂ, ‖g w‖))*‖x-y‖) := by
  obtain ⟨A,B,hA,hB,hjet,hL⟩ := tailCauchyKernel_bounds
  refine ⟨A,B,hA,hB,?_⟩
  intro g hg hi
  have hj (x : ℂ) : Integrable (tailIntegralJet g x) :=
    (hi.norm.const_mul A).mono' (tailIntegralJet_continuous hg x).aestronglyMeasurable
      (Eventually.of_forall (tailIntegralJet_bound hA (fun z => (hjet z).2) g x))
  constructor
  · intro x
    exact (norm_integral_le_of_norm_le (hi.norm.const_mul A)
      (Eventually.of_forall (tailIntegralJet_bound hA (fun z => (hjet z).2) g x))).trans_eq
      (integral_const_mul A _)
  · intro x y
    rw [tailCauchyDerivative, tailCauchyDerivative, ← integral_sub (hj x) (hj y)]
    calc
      _ ≤ ∫ w : ℂ, (B*‖x-y‖)*‖g w‖ := by
        apply norm_integral_le_of_norm_le (hi.norm.const_mul (B*‖x-y‖))
        apply Eventually.of_forall
        intro w
        apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
        intro v
        change ‖tailCauchyJet 0 (x-w) v • g w-tailCauchyJet 0 (y-w) v • g w‖ ≤ _
        rw [← sub_smul, ← sub_apply, norm_smul]
        calc
          _ ≤ (‖tailCauchyJet 0 (x-w)-tailCauchyJet 0 (y-w)‖*‖v‖)*‖g w‖ :=
            mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
          _ ≤ ((B*‖x-y‖)*‖v‖)*‖g w‖ := by
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            simpa only [sub_sub_sub_cancel_right] using hL (x-w) (y-w)
          _ = _ := by ring
      _ = _ := by rw [integral_const_mul]; ring

lemma cauchyTransform_holder_hasFDerivAt {g : ℂ → E} (hgC : Continuous g) (hi : Integrable g)
    {H : ℝ} (hH : 0 ≤ H) (hg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) (x : ℂ) :
    HasFDerivAt (cauchyTransform g) (globalCauchyDerivative g x) x := by
  unfold cauchyTransform
  rw [cauchy_kernel_convolution_split hgC hi]
  exact ((cutoffCauchy_hasFDerivAt schauderBump hgC hH hg x).add
    (tailCauchy_hasFDerivAt hgC hi x)).const_smul _

lemma cauchyTransform_schauder_bounds :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : ℂ → E, Continuous g → Integrable g →
      ∀ M H : ℝ, 0 ≤ M → 0 ≤ H → (∀ x, ‖g x‖ ≤ M) →
        (∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) →
      (∀ x, ‖cauchyTransform g x‖ ≤ C*(M+H+∫ w : ℂ, ‖g w‖)) ∧
      (∀ x, ‖globalCauchyDerivative g x‖ ≤ C*(M+H+∫ w : ℂ, ‖g w‖)) ∧
      (∀ x y, ‖globalCauchyDerivative g x-globalCauchyDerivative g y‖ ≤
        C*(M+H+∫ w : ℂ, ‖g w‖)*‖x-y‖^((1:ℝ)/3)) := by
  obtain ⟨D,hD,hDb⟩ := cutoffCauchy_fderiv_bound (E := E) schauderBump
  obtain ⟨F,hF,hFb⟩ := cutoffCauchyDerivative_holder (E := E) schauderBump
  obtain ⟨A,B,hA,hB,hTb⟩ := tailCauchy_derivative_bounds (E := E)
  let K : ℝ := ∫ w : ℂ, ‖schauderBump w • w⁻¹‖
  have hK : 0 ≤ K := integral_nonneg (fun _ => norm_nonneg _)
  let c : ℝ := ‖(Real.pi : ℂ)⁻¹‖
  have hc : 0 ≤ c := norm_nonneg _
  refine ⟨c*(K+D+F+2*A+B+1),by positivity,?_⟩
  intro g hgC hi M H hM hH hb hh
  let I : ℝ := ∫ w : ℂ, ‖g w‖
  have hI : 0 ≤ I := integral_nonneg (fun _ => norm_nonneg _)
  have htotal : 0 ≤ M+H+I := by positivity
  have hMI : M ≤ M+H+I := by linarith
  have hHI : H ≤ M+H+I := by linarith
  have hII : I ≤ M+H+I := by linarith
  have hDb' (x : ℂ) : ‖cutoffCauchyDerivative schauderBump g x‖ ≤ D*H := hDb g hgC H hH hh x
  have hTb' := hTb g hgC hi
  have hTh : ∀ x y, ‖tailCauchyDerivative g x-tailCauchyDerivative g y‖ ≤
      ((2*A+B)*I)*‖x-y‖^((1:ℝ)/3) := by
    have he := thirdHolderOn_of_bounded_lipschitz (s := (univ : Set ℂ))
      (mul_nonneg hA hI) (mul_nonneg hB hI) (fun x _ => hTb'.1 x)
      (fun x _ y _ => hTb'.2 x y)
    intro x y
    convert! he x (mem_univ x) y (mem_univ y) using 1; ring
  refine ⟨?_,?_,?_⟩
  · intro x
    change ‖(Real.pi : ℂ)⁻¹ •
      (convolution (fun w : ℂ => w⁻¹) g (ContinuousLinearMap.lsmul ℝ ℂ) volume x : E)‖ ≤ _
    rw [norm_smul, cauchy_kernel_convolution_split hgC hi]
    apply (mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans
      (add_le_add (cutoffCauchy_value_bound schauderBump hb x) (tailCauchy_value_bound hi x))) hc).trans
    dsimp only [K, c, I] at *
    nlinarith [mul_le_mul_of_nonneg_left hMI hK, mul_le_mul_of_nonneg_left hII (by norm_num : (0:ℝ) ≤ 1),
      mul_nonneg (add_nonneg (add_nonneg hD hF) (add_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hA) hB)) htotal]
  · intro x
    rw [globalCauchyDerivative, norm_smul]
    apply (mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add (hDb' x) (hTb'.1 x))) hc).trans
    have hL1 := mul_le_mul_of_nonneg_left hHI hD
    have hL2 := mul_le_mul_of_nonneg_left hII hA
    have hRest := mul_nonneg (show 0 ≤ K+F+A+B+1 by positivity) htotal
    dsimp only [c, I] at *
    nlinarith
  · intro x y
    have hr : 0 ≤ ‖x-y‖^((1:ℝ)/3) := Real.rpow_nonneg (norm_nonneg _) _
    simp only [globalCauchyDerivative, ← smul_sub, norm_smul]
    have he : cutoffCauchyDerivative schauderBump g x+tailCauchyDerivative g x -
        (cutoffCauchyDerivative schauderBump g y+tailCauchyDerivative g y) =
        (cutoffCauchyDerivative schauderBump g x-cutoffCauchyDerivative schauderBump g y)+
        (tailCauchyDerivative g x-tailCauchyDerivative g y) := by abel
    rw [he]
    apply (mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans
      (add_le_add (hFb g hgC H hH hh x y) (hTh x y))) hc).trans
    have hL1 := mul_le_mul_of_nonneg_left hHI hF
    have hL2 := mul_le_mul_of_nonneg_left hII (show 0 ≤ 2*A+B by positivity)
    have hRest := mul_nonneg (show 0 ≤ K+D+1 by positivity) htotal
    have he' : F*H+(2*A+B)*I ≤ (K+D+F+2*A+B+1)*(M+H+I) := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right he' hr) hc
    dsimp only [c, I] at *
    nlinarith

end HigherDimensionalBallPacking.Rigidity

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable {K : Set ℂ} (hK : IsCompact K)
include hK

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedAddCommGroupSubtypeAmbientComplexMemSubmoduleRealHMap
local instance instNormedSpaceRealSubtypeAmbientComplexMemSubmoduleHMap_r07fc69_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedAddCommGroupSubtypeAmbientComplexMemSubmoduleRealHMapSupportedHolder
local instance instNormedSpaceRealSubtypeAmbientComplexMemSubmoduleHMapSupportedHolder_r07fc69_1 : NormedSpace ℝ (supportedHolder (E := E) K) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedAddCommGroupSubtypeJetAmbientComplexHDivRealOfNatMemSubmoduleCOne
local instance instNormedSpaceRealSubtypeJetAmbientComplexHDivOfNatMemSubmoduleCOne_r07fc69_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
lemma supported_cauchy_bounds : ∃ C : ℝ, 0 ≤ C ∧
    ∀ g : supportedHolder (E := E) K,
    (∀ x, ‖cauchyTransform (valueCLM _ g.val) x‖ ≤ C*‖g‖) ∧
    (∀ x, ‖globalCauchyDerivative (valueCLM _ g.val) x‖ ≤ C*‖g‖) ∧
    (∀ x y, ‖globalCauchyDerivative (valueCLM _ g.val) x -
      globalCauchyDerivative (valueCLM _ g.val) y‖ ≤ C*‖g‖*‖x-y‖^((1:ℝ)/3)) := by
  obtain ⟨C,hC,hb⟩ := cauchyTransform_schauder_bounds (E := E)
  refine ⟨C*(2+volume.real K),by positivity,?_⟩
  intro g
  have hg := hb (valueCLM _ g.val) (valueCLM _ g.val).continuous
    (supportedHolder_integrable hK g) ‖g‖ ‖g‖ (norm_nonneg g) (norm_nonneg g)
    (norm_value_le g.val) (by intro x y; change ‖valueCLM _ g.val x-valueCLM _ g.val y‖ ≤ ‖g.val‖*‖x-y‖^((1:ℝ)/3); simpa only [dist_eq_norm] using norm_sub_value_le g.val x y)
  have he : C*(‖g‖+‖g‖+∫ x : ℂ, ‖valueCLM _ g.val x‖) ≤ (C*(2+volume.real K))*‖g‖ := by
    have hh := mul_le_mul_of_nonneg_left (supportedHolder_integral_norm_le hK g) hC
    nlinarith
  exact ⟨fun x => (hg.1 x).trans he,fun x => (hg.2.1 x).trans he,
    fun x y => (hg.2.2 x y).trans (mul_le_mul_of_nonneg_right he (Real.rpow_nonneg (norm_nonneg _) _))⟩

def schauderConstant : ℝ := (supported_cauchy_bounds (E := E) hK).choose
lemma schauderConstant_nonneg : 0 ≤ schauderConstant (E := E) hK :=
  (supported_cauchy_bounds (E := E) hK).choose_spec.1
lemma schauderConstant_spec (g : supportedHolder (E := E) K) :
    (∀ x, ‖cauchyTransform (valueCLM _ g.val) x‖ ≤ schauderConstant (E := E) hK*‖g‖) ∧
    (∀ x, ‖globalCauchyDerivative (valueCLM _ g.val) x‖ ≤ schauderConstant (E := E) hK*‖g‖) ∧
    (∀ x y, ‖globalCauchyDerivative (valueCLM _ g.val) x-globalCauchyDerivative (valueCLM _ g.val) y‖ ≤
      schauderConstant (E := E) hK*‖g‖*‖x-y‖^((1:ℝ)/3)) :=
  (supported_cauchy_bounds (E := E) hK).choose_spec.2 g

def supportedCauchy (g : supportedHolder (E := E) K) : COne ℂ E := by
  let f := cauchyTransform (valueCLM _ g.val)
  let A := globalCauchyDerivative (valueCLM _ g.val)
  let B := schauderConstant (E := E) hK * ‖g‖
  have hB : 0 ≤ B := mul_nonneg (schauderConstant_nonneg hK) (norm_nonneg g)
  have hd : ∀ x, HasFDerivAt f (A x) x :=
    cauchyTransform_holder_hasFDerivAt (valueCLM _ g.val).continuous
      (supportedHolder_integrable hK g) (norm_nonneg g.val)
      (by simpa only [dist_eq_norm] using norm_sub_value_le g.val)
  have hb := schauderConstant_spec hK g
  exact ⟨(ofBoundedDeriv f (fun x => (hd x).differentiableAt) B B hB hB hb.1
      (fun x => by rw [(hd x).fderiv]; exact hb.2.1 x),
    ofBound A (holder_continuous (by norm_num : (0:ℝ)<(1:ℝ)/3) hb.2.2)
      B B hb.2.1 hB (by simpa only [dist_eq_norm] using hb.2.2)),hd⟩

@[simp] lemma supportedCauchy_value (g : supportedHolder (E := E) K) (x : ℂ) :
    cValue (supportedCauchy hK g) x = cauchyTransform (valueCLM _ g.val) x := rfl
@[simp] lemma supportedCauchy_deriv (g : supportedHolder (E := E) K) (x : ℂ) :
    cDeriv (supportedCauchy hK g) x = globalCauchyDerivative (valueCLM _ g.val) x := rfl

lemma supportedCauchy_norm_le (g : supportedHolder (E := E) K) :
    ‖supportedCauchy hK g‖ ≤ (3*schauderConstant (E := E) hK)*‖g‖ := by
  let B := schauderConstant (E := E) hK * ‖g‖
  have hB : 0 ≤ B := mul_nonneg (schauderConstant_nonneg hK) (norm_nonneg g)
  have hd := cauchyTransform_holder_hasFDerivAt (valueCLM _ g.val).continuous
    (supportedHolder_integrable hK g) (norm_nonneg g.val)
    (by simpa only [dist_eq_norm] using norm_sub_value_le g.val)
  have hb := schauderConstant_spec hK g
  change max _ _ ≤ _
  apply max_le
  · apply (ofBoundedDeriv_norm_le _ (fun x => (hd x).differentiableAt) B B hB hB hb.1
      (fun x => by rw [(hd x).fderiv]; exact hb.2.1 x)).trans
    dsimp only [B] <;> linarith
  · apply (ofBound_norm_le _ _ B B hB hb.2.1 hB
      (by simpa only [dist_eq_norm] using hb.2.2)).trans
    rw [max_self]
    dsimp only [B] at * <;> nlinarith

omit [CompleteSpace E] in
lemma supported_cauchy_integrable (g : supportedHolder (E := E) K) (x : ℂ) :
    Integrable (fun w : ℂ => w⁻¹ • valueCLM _ g.val (x-w)) :=
  (supportedHolder_hasCompactSupport hK g).convolutionExists_right
    (ContinuousLinearMap.lsmul ℝ ℂ) locallyIntegrable_complex_inv
    (valueCLM _ g.val).continuous x

lemma supportedCauchy_add (g h : supportedHolder (E := E) K) :
    supportedCauchy hK (g+h) = supportedCauchy hK g + supportedCauchy hK h := by
  apply cValue_ext
  intro x
  simp only [supportedCauchy_value, cValue_add, cauchyTransform_apply]
  change (Real.pi : ℂ)⁻¹ • (∫ w : ℂ, w⁻¹ •
    (valueCLM _ g.val (x-w)+valueCLM _ h.val (x-w))) = _
  simp_rw [smul_add]
  rw [integral_add (supported_cauchy_integrable hK g x) (supported_cauchy_integrable hK h x),smul_add]

lemma supportedCauchy_smul (c : ℝ) (g : supportedHolder (E := E) K) :
    supportedCauchy hK (c • g) = c • supportedCauchy hK g := by
  apply cValue_ext
  intro x
  simp only [supportedCauchy_value, cValue_smul, cauchyTransform_apply]
  change (Real.pi : ℂ)⁻¹ • (∫ w : ℂ, w⁻¹ • (c • valueCLM _ g.val (x-w))) = _
  simp_rw [smul_comm (M := ℂ) (N := ℝ)]
  rw [integral_smul]
  exact smul_comm _ _ _

def supportedCauchyCLM : supportedHolder (E := E) K →L[ℝ] COne ℂ E :=
  LinearMap.mkContinuous
    { toFun := supportedCauchy hK
      map_add' := supportedCauchy_add hK
      map_smul' := supportedCauchy_smul hK }
    (3*schauderConstant hK) (supportedCauchy_norm_le hK)

@[simp] lemma supportedCauchyCLM_value (g : supportedHolder (E := E) K) (x : ℂ) :
    cValue (supportedCauchyCLM hK g) x = cauchyTransform (valueCLM _ g.val) x := rfl

end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Rigidity_RadialForm
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SymplecticBallPacking.Hamiltonian
open scoped ContDiff Topology
open Set Function Filter MeasureTheory

@[simp] theorem radiusSq_nonneg (p : Plane) : 0 ≤ radiusSq p :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

@[fun_prop] theorem radiusSq_smooth : ContDiff ℝ ∞ radiusSq := by unfold radiusSq; fun_prop

def planarDot : Plane →L[ℝ] Plane →L[ℝ] ℝ :=
  (ContinuousLinearMap.mul ℝ ℝ).bilinearComp (ContinuousLinearMap.fst ℝ ℝ ℝ)
    (ContinuousLinearMap.fst ℝ ℝ ℝ) +
  (ContinuousLinearMap.mul ℝ ℝ).bilinearComp (ContinuousLinearMap.snd ℝ ℝ ℝ)
    (ContinuousLinearMap.snd ℝ ℝ ℝ)

@[simp] theorem planarDot_apply (z v : Plane) : planarDot z v=z.1*v.1+z.2*v.2 := rfl

end SymplecticBallPacking.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Cauchy_GreenFormula
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SymplecticBallPacking.Hamiltonian
open scoped ContDiff Topology
open Set Function Filter MeasureTheory

@[fun_prop] theorem polar_smooth : ContDiff ℝ ∞ (polarCoord.symm : Plane → Plane) := by
  change ContDiff ℝ ∞ (fun p : Plane => (p.1*Real.cos p.2,p.1*Real.sin p.2))
  fun_prop

def coordinateForm (U V : Plane → ℝ) (p : Plane) : Plane →L[ℝ] ℝ :=
  U p • ContinuousLinearMap.fst ℝ ℝ ℝ + V p • ContinuousLinearMap.snd ℝ ℝ ℝ

@[simp] theorem coordinateForm_apply (U V : Plane → ℝ) (p v : Plane) :
    coordinateForm U V p v = U p*v.1+V p*v.2 := rfl

end SymplecticBallPacking.Hamiltonian

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
@[simp] lemma curlJet_apply (A : ℂ →L[ℝ] E) :
    curlJet A = Complex.I • A 1 - A Complex.I := rfl

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

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
local instance markedJetInst3 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance markedJetInst4_r07fc69_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance markedJetInst5 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance markedJetInst6_r07fc69_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance markedJetInst7 : NormedAddCommGroup (HMap ℂ (ℂ →L[ℝ] E)) := inferInstance

local instance markedJetInst8_r07fc69_1 : NormedSpace ℝ (HMap ℂ (ℂ →L[ℝ] E)) := inferInstance
def constJet (v : E) : COne ℂ E :=
  ⟨(const _ v,0),fun z => hasFDerivAt_const v z⟩

omit [CompleteSpace E] in
@[simp] lemma constJet_value (v : E) (z : ℂ) : cValue (constJet v) z = v := rfl
omit [CompleteSpace E] in
@[simp] lemma constJet_deriv (v : E) (z : ℂ) : cDeriv (constJet v) z = 0 := rfl

omit [CompleteSpace E] in
lemma constJet_norm_le (v : E) : ‖constJet v‖ ≤ ‖v‖ := by
  change max ‖const _ v‖ ‖(0 : HMap ℂ (ℂ →L[ℝ] E))‖ ≤ _
  rw [norm_zero]
  exact max_le (const_norm_le v) (norm_nonneg v)

def constJetCLM : E →L[ℝ] COne ℂ E :=
  LinearMap.mkContinuous
    { toFun := constJet
      map_add' := fun u v => by apply cValue_ext; intro z; rfl
      map_smul' := fun c v => by apply cValue_ext; intro z; rfl }
    1 (by intro v; change ‖constJet v‖ ≤ 1*‖v‖; rw [one_mul]; exact constJet_norm_le v)

def jetEval (z : ℂ) : COne ℂ E →L[ℝ] E :=
  (BoundedContinuousFunction.evalCLM ℝ z).comp ((valueCLM _).comp (jetValueCLM _))

omit [CompleteSpace E] in
@[simp] lemma jetEval_apply (z : ℂ) (u : COne ℂ E) : jetEval z u = cValue u z := rfl

def zeroNormalize : COne ℂ E →L[ℝ] COne ℂ E :=
  ContinuousLinearMap.id ℝ _ - constJetCLM.comp (jetEval 0)

omit [CompleteSpace E] in
@[simp] lemma zeroNormalize_value (u : COne ℂ E) (z : ℂ) :
    cValue (zeroNormalize u) z = cValue u z-cValue u 0 := rfl
omit [CompleteSpace E] in
@[simp] lemma zeroNormalize_deriv (u : COne ℂ E) (z : ℂ) :
    cDeriv (zeroNormalize u) z = cDeriv u z := by
  change cDeriv u z - 0 = _
  exact sub_zero _

def standardJetCR : COne ℂ E →L[ℝ] HMap ℂ E :=
  let L : HMap ℂ (ℂ →L[ℝ] E) →L[ℝ] HMap ℂ E := mapCLM _ (curlJet (E := E));
  -(L.comp (jetDerivCLM (D := ℂ) (E := E) ((1:ℝ)/3)))


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end


