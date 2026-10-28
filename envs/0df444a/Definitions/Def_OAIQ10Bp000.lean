-- Prove2me | Definitions.Def_OAIQ10Bp000
-- name    : OAIQ10Bp000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T16:20:55.196485+00:00
-- url     : https://prove2.me/theorems/1ae9c845-3036-4ce6-8cdd-27843558ea73
-- title:
--   Definitions bundle OAIQ10Bp000 of the split of OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.packing_necessity`, carved from OpenAI's openai/math development (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 331 declarations of OpenAI's Lean: 95 definitions, 6 instances and 230 theorems. The definitions and types are `OAI.HigherDimensionalBallPacking.Rigidity.C1HolderAmbient`, `OAI.HigherDimensionalBallPacking.Rigidity.C1HolderSpace`, `OAI.HigherDimensionalBallPacking.Rigidity.CompactHolderSpace`, `OAI.HigherDimensionalBallPacking.Rigidity.Compatible`, `OAI.HigherDimensionalBallPacking.Rigidity.End`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderSpace`, `OAI.HigherDimensionalBallPacking.Rigidity.OffDiagonal`, `OAI.HigherDimensionalBallPacking.Rigidity.UnitTime`, `OAI.HigherDimensionalBallPacking.Rigidity.annularCauchyKernel`, `OAI.HigherDimensionalBallPacking.Rigidity.baseSegment`, `OAI.HigherDimensionalBallPacking.Rigidity.c1HolderDeriv`, `OAI.HigherDimensionalBallPacking.Rigidity.c1HolderEval`, `OAI.HigherDimensionalBallPacking.Rigidity.c1HolderGraph`, `OAI.HigherDimensionalBallPacking.Rigidity.c1HolderMk`, `OAI.HigherDimensionalBallPacking.Rigidity.c1HolderValue`, `OAI.HigherDimensionalBallPacking.Rigidity.c1LowerOrderCLM`, `OAI.HigherDimensionalBallPacking.Rigidity.cauchyCurl`, `OAI.HigherDimensionalBallPacking.Rigidity.cauchyInnerBump`, `OAI.HigherDimensionalBallPacking.Rigidity.cauchyPuncture`, `OAI.HigherDimensionalBallPacking.Rigidity.cauchyTransform`, `OAI.HigherDimensionalBallPacking.Rigidity.cayleyP`, `OAI.HigherDimensionalBallPacking.Rigidity.compactCRInverse`, `OAI.HigherDimensionalBallPacking.Rigidity.compactCRInverseValue`, `OAI.HigherDimensionalBallPacking.Rigidity.compactCoefficient`, `OAI.HigherDimensionalBallPacking.Rigidity.compactHolderCauchy`, `OAI.HigherDimensionalBallPacking.Rigidity.compactHolderCauchyCLM`, `OAI.HigherDimensionalBallPacking.Rigidity.compactHolderCauchyLM`, `OAI.HigherDimensionalBallPacking.Rigidity.compactHolderMap`, `OAI.HigherDimensionalBallPacking.Rigidity.compactHolderSubmodule`, `OAI.HigherDimensionalBallPacking.Rigidity.compactHolderValue`, `OAI.HigherDimensionalBallPacking.Rigidity.compactSmoothHolder`, `OAI.HigherDimensionalBallPacking.Rigidity.complexCauchyCurl`, `OAI.HigherDimensionalBallPacking.Rigidity.conjugateJ`, `OAI.HigherDimensionalBallPacking.Rigidity.cutoffCauchyKernel`, `OAI.HigherDimensionalBallPacking.Rigidity.decayRatio`, `OAI.HigherDimensionalBallPacking.Rigidity.differencePull`, `OAI.HigherDimensionalBallPacking.Rigidity.dyadicKernelDerivative`, `OAI.HigherDimensionalBallPacking.Rigidity.dyadicKernelPotential`, `OAI.HigherDimensionalBallPacking.Rigidity.holderApply`, `OAI.HigherDimensionalBallPacking.Rigidity.holderBaseDifference` and 55 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry/BallPacking, in whole or in part: `BallPacking_Cauchy_GreenFormula`, `BallPacking_Holder_NonlinearCR`, `BallPacking_Holder_SchauderSplit`, `BallPacking_Necessity_CauchyDuality`, `BallPacking_Necessity_FrameFredholm`, `BallPacking_Necessity_HolderCalculus`, `BallPacking_Necessity_HolderCompactness`, `BallPacking_Necessity_HolderCompletion`, `BallPacking_Necessity_KernelMoments`, `BallPacking_Necessity_MarkedInverse`, `BallPacking_Necessity_NonlinearCR`, `BallPacking_Necessity_SquareBounds`, `BallPacking_Rigidity_Adapted`, `BallPacking_Rigidity_CompatibleStructures`, `BallPacking_Rigidity_RadialForm`.
--
--   **Imports.** It imports the published bundle `Def_BallPackingNecessity`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ10Bp002`, `OAIQ10Bp003` and `OAIQ10Bp008`; the statements `OAI_HigherDimensionalBallPacking_Rigidity_actual_affine_line_exists`, `OAI.HigherDimensionalBallPacking.Rigidity.c1_decaying_CR_zero`, `OAI.HigherDimensionalBallPacking.Rigidity.compatible_frozen_solution`, `OAI.HigherDimensionalBallPacking.Rigidity.framed_density_equation` and `OAI.HigherDimensionalBallPacking.Rigidity.framed_frozen_solution`.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/BallPacking at commit adc7f12

import Mathlib
import Definitions.Def_BallPackingNecessity

section
-- module Solutions.OAIQ10_BP.BallPacking_Holder_NonlinearCR
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Filter MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

 theorem compact_kernel_derivative_integral_zero {K : ℂ → ℂ}
    (hK : ContDiff ℝ ∞ K) (hc : HasCompactSupport K) (v : ℂ) :
    (∫ w : ℂ, fderiv ℝ K w v)=0 := by
  have hi : Integrable (fun w => fderiv ℝ K w v) :=
    (((hK.fderiv_right (m := ∞) (by simp)).continuous).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) v)
  have hi0 : Integrable (fun w : ℂ => K w) := hK.continuous.integrable_of_hasCompactSupport hc
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := K) (g := fun _ : ℂ => (1:ℂ)) (v := v) (μ := volume)
    (by simpa only [mul_one] using hi) (by simp) (by simpa only [mul_one] using hi0)
    (fun w _ => hK.differentiable (by simp) w) (fun _ _ => differentiableAt_const _)
  have he : (fun x : ℂ => K x*fderiv ℝ (fun _ : ℂ => (1:ℂ)) x v)=0 := by
    funext x
    simp only [fderiv_const_apply,zero_apply,mul_zero,Pi.zero_apply]
  rw [he] at h
  change (∫ x : ℂ, (0:ℂ)) = -(∫ x : ℂ, fderiv ℝ K x v * 1) at h
  simpa only [integral_zero,mul_one,zero_eq_neg] using h

omit [CompleteSpace E] in
 theorem compact_kernel_convolution_fderiv {K : ℂ → ℂ}
    (hK : ContDiff ℝ ∞ K) (hc : HasCompactSupport K) {g : ℂ → E}
    (hg : Continuous g) (x v : ℂ) :
    fderiv ℝ (convolution K g (ContinuousLinearMap.lsmul ℝ ℂ) volume) x v =
      ∫ w : ℂ, fderiv ℝ K w v • g (x-w) := by
  have hd := hc.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℂ)
    (hK.of_le (by simp)) (hg.locallyIntegrable (μ := volume)) x
  rw [hd.fderiv,convolution]
  have hi : Integrable (fun w : ℂ =>
      ((ContinuousLinearMap.lsmul ℝ ℂ).precompL ℂ) (fderiv ℝ K w) (g (x-w))) :=
    (hc.fderiv ℝ).convolutionExists_left _
      (hK.continuous_fderiv (by simp)) (hg.locallyIntegrable (μ := volume)) x
  rw [ContinuousLinearMap.integral_apply hi]
  rfl

 theorem compact_kernel_convolution_cancel {K : ℂ → ℂ}
    (hK : ContDiff ℝ ∞ K) (hc : HasCompactSupport K) {g : ℂ → E}
    (hg : Continuous g) (x v : ℂ) :
    fderiv ℝ (convolution K g (ContinuousLinearMap.lsmul ℝ ℂ) volume) x v =
      ∫ w : ℂ, fderiv ℝ K w v • (g (x-w)-g x) := by
  rw [compact_kernel_convolution_fderiv hK hc hg]
  have hi : Integrable (fun w : ℂ => fderiv ℝ K w v • g (x-w)) :=
    ((((hK.fderiv_right (m := ∞) (by simp)).continuous.clm_apply continuous_const).smul
      (hg.comp (continuous_const.sub continuous_id)))).integrable_of_hasCompactSupport
        ((hc.fderiv_apply (𝕜 := ℝ) v).smul_right)
  have hi0 : Integrable (fun w : ℂ => fderiv ℝ K w v) :=
    (((hK.fderiv_right (m := ∞) (by simp)).continuous).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) v)
  simp_rw [smul_sub]
  rw [integral_sub hi (hi0.smul_const _),integral_smul_const,
    compact_kernel_derivative_integral_zero hK hc,zero_smul,sub_zero]

 theorem compact_kernel_convolution_derivative_bound {K : ℂ → ℂ}
    (hK : ContDiff ℝ ∞ K) (hc : HasCompactSupport K) {g : ℂ → E}
    (hg : Continuous g) {W : ℂ → ℝ} (hW : Integrable W)
    (hb : ∀ x w v, ‖fderiv ℝ K w v‖*‖g (x-w)-g x‖ ≤ W w*‖v‖) (x : ℂ) :
    ‖fderiv ℝ (convolution K g (ContinuousLinearMap.lsmul ℝ ℂ) volume) x‖ ≤
      ∫ w : ℂ, W w := by
  have hW0 : 0≤ ∫ w : ℂ, W w := by
    apply integral_nonneg
    intro w
    change (0:ℝ) ≤ W w
    have h := hb 0 w 1
    simpa only [norm_one,mul_one] using (mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans h
  apply ContinuousLinearMap.opNorm_le_bound _ hW0
  intro v
  rw [compact_kernel_convolution_cancel hK hc hg]
  calc
    _ ≤ ∫ w : ℂ, W w*‖v‖ := norm_integral_le_of_norm_le (hW.mul_const _)
      (Eventually.of_forall fun w => by rw [norm_smul]; exact hb x w v)
    _ = _ := integral_mul_const _ _


end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Holder_SchauderSplit
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

 theorem locallyIntegrable_complex_inv : LocallyIntegrable (fun z : ℂ => z⁻¹) := by
  apply locallyIntegrable_of_norm_le_rpow (C := 1) (α := 1) (by simp) (by norm_num)
  · exact ae_of_all _ fun z => by simp only [norm_inv,Real.rpow_neg_one,one_mul,le_refl]
  · exact measurable_inv.aestronglyMeasurable

 variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

 def cauchyTransform (h : ℂ → E) : ℂ → E :=
  (Real.pi : ℂ)⁻¹ • convolution (fun z : ℂ => z⁻¹) h (ContinuousLinearMap.lsmul ℝ ℂ) volume

 theorem cauchyTransform_apply (h : ℂ → E) (z : ℂ) :
    cauchyTransform h z = (Real.pi : ℂ)⁻¹ • ∫ w : ℂ, w⁻¹ • h (z-w) := rfl

 theorem cauchyTransform_hasFDerivAt {h : ℂ → E} (hc : HasCompactSupport h)
    (hs : ContDiff ℝ ∞ h) (z : ℂ) :
    HasFDerivAt (cauchyTransform h)
      ((Real.pi : ℂ)⁻¹ • convolution (fun w : ℂ => w⁻¹) (fderiv ℝ h)
        ((ContinuousLinearMap.lsmul ℝ ℂ).precompR ℂ) volume z) z := by
  exact (hc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℂ)
    locallyIntegrable_complex_inv (hs.of_le (by simp)) z).const_smul _


end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Rigidity_CompatibleStructures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HigherDimensionalBallPacking
open scoped ContDiff

noncomputable section
open scoped Topology
open Set Function Filter

namespace Rigidity

abbrev End (n : ℕ) := Phase n →L[ℝ] Phase n

def standardJ (n : ℕ) : End n :=
  (ContinuousLinearMap.lsmul ℝ ℂ) Complex.I

@[simp] theorem standardJ_apply (n : ℕ) (v : Phase n) (i : Fin n) :
    standardJ n v i = Complex.I * v i := rfl

@[simp] theorem standardJ_sq (n : ℕ) (v : Phase n) :
    standardJ n (standardJ n v) = -v := by
  funext i
  simp only [standardJ_apply, ← mul_assoc, Complex.I_mul_I, neg_one_mul, Pi.neg_apply]

@[simp] theorem standardForm_J_J {n : ℕ} (v w : Phase n) :
    standardForm (standardJ n v) (standardJ n w) = standardForm v w := by
  unfold standardForm
  apply Finset.sum_congr rfl
  intro i _
  simp [standardJ_apply, Complex.mul_re, Complex.mul_im]
  ring

@[simp] theorem standardForm_J_self {n : ℕ} (v : Phase n) :
    standardForm v (standardJ n v) = ∑ i, Complex.normSq (v i) := by
  unfold standardForm
  apply Finset.sum_congr rfl
  intro i _
  simp [standardJ_apply, Complex.mul_re, Complex.mul_im, Complex.normSq_apply]

def Compatible {n : ℕ} (J : End n) : Prop :=
  (∀ v, J (J v) = -v) ∧
  (∀ v w, standardForm (J v) (J w) = standardForm v w) ∧
  (∀ v, v ≠ 0 → 0 < standardForm v (J v))

def conjugateJ {n : ℕ} (e : Phase n ≃L[ℝ] Phase n) : End n :=
  e.toContinuousLinearMap.comp ((standardJ n).comp e.symm.toContinuousLinearMap)

@[simp] theorem conjugateJ_apply {n : ℕ} (e : Phase n ≃L[ℝ] Phase n) (v : Phase n) :
    conjugateJ e v = e (standardJ n (e.symm v)) := rfl

end Rigidity
end
end HigherDimensionalBallPacking

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
namespace HigherDimensionalBallPacking.Rigidity

def stdDot (n : ℕ) : Phase n →L[ℝ] Phase n →L[ℝ] ℝ :=
  ∑ i, ((ContinuousLinearMap.mul ℝ ℝ).bilinearComp
    (Complex.reCLM.comp (ContinuousLinearMap.proj i))
    (Complex.reCLM.comp (ContinuousLinearMap.proj i)) +
    (ContinuousLinearMap.mul ℝ ℝ).bilinearComp
    (Complex.imCLM.comp (ContinuousLinearMap.proj i))
    (Complex.imCLM.comp (ContinuousLinearMap.proj i)))

@[simp] theorem stdDot_apply {n : ℕ} (v w : Phase n) :
    stdDot n v w = ∑ i, ((v i).re * (w i).re + (v i).im * (w i).im) := by
  simp [stdDot]

@[simp] theorem standardForm_J_right {n : ℕ} (v w : Phase n) :
    standardForm v (standardJ n w) = stdDot n v w := by
  simp [standardForm, stdDot_apply, standardJ_apply, Complex.mul_re, Complex.mul_im]

@[simp] theorem standardForm_neg_right {n : ℕ} (v w : Phase n) :
    standardForm v (-w) = -standardForm v w := by
  unfold standardForm
  rw [←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.neg_apply, Complex.neg_re, Complex.neg_im]
  ring

def relativeOperator {n : ℕ} (J : End n) : End n := -(standardJ n).comp J

@[simp] theorem relativeOperator_apply {n : ℕ} (J : End n) (v : Phase n) :
    relativeOperator J v = -standardJ n (J v) := rfl

@[simp] theorem standardJ_relativeOperator {n : ℕ} (J : End n) (v : Phase n) :
    standardJ n (relativeOperator J v) = J v := by simp

@[simp] theorem relativeOperator_J_relativeOperator {n : ℕ} {J : End n}
    (hJ : Compatible J) (v : Phase n) :
    relativeOperator J (standardJ n (relativeOperator J v)) = standardJ n v := by
  rw [standardJ_relativeOperator, relativeOperator_apply, hJ.1]
  simp

@[simp] theorem stdDot_relativeOperator {n : ℕ} (J : End n) (v w : Phase n) :
    stdDot n v (relativeOperator J w) = standardForm v (J w) := by
  rw [←standardForm_J_right, standardJ_relativeOperator]

def cayleyP {n : ℕ} (J : End n) (a b : ℝ) : End n :=
  a • relativeOperator J + b • ContinuousLinearMap.id ℝ (Phase n)

@[simp] theorem cayleyP_apply {n : ℕ} (J : End n) (a b : ℝ) (v : Phase n) :
    cayleyP J a b v = a • relativeOperator J v + b • v := rfl

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Rigidity_Adapted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology Manifold
open Set Function Filter


@[fun_prop]
theorem continuous_capacity (n : ℕ) : Continuous (capacity : Phase n → ℝ) := by
  unfold capacity
  fun_prop


end

open scoped ContDiff Topology
open Set Function Filter MeasureTheory



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Rigidity_RadialForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter MeasureTheory

@[simp] theorem stdDot_J_right {n : ℕ} (v w : Phase n) :
    stdDot n v (standardJ n w) = -standardForm v w := by
  rw [←standardForm_J_right,standardJ_sq,standardForm_neg_right]

@[simp] theorem capacity_eq_stdDot {n : ℕ} (x : Phase n) :
    capacity x = Real.pi * stdDot n x x := by
  rw [←standardForm_J_right,standardForm_J_self]
  rfl

end HigherDimensionalBallPacking.Rigidity

namespace SymplecticBallPacking.Hamiltonian
open scoped ContDiff Topology
open Set Function Filter MeasureTheory

abbrev Plane := ℝ × ℝ

def planarArea : Plane →L[ℝ] Plane →L[ℝ] ℝ :=
  (ContinuousLinearMap.mul ℝ ℝ).bilinearComp (ContinuousLinearMap.fst ℝ ℝ ℝ)
    (ContinuousLinearMap.snd ℝ ℝ ℝ) -
  (ContinuousLinearMap.mul ℝ ℝ).bilinearComp (ContinuousLinearMap.snd ℝ ℝ ℝ)
    (ContinuousLinearMap.fst ℝ ℝ ℝ)

@[simp] theorem planarArea_apply (v w : Plane) : planarArea v w = v.1*w.2-v.2*w.1 := rfl
def planarCurl (alpha : Plane → Plane →L[ℝ] ℝ) (p : Plane) : ℝ :=
  fderiv ℝ alpha p (1,0) (0,1) - fderiv ℝ alpha p (0,1) (1,0)
def radiusSq (p : Plane) : ℝ := p.1^2+p.2^2
@[simp] theorem radiusSq_nonneg (p : Plane) : 0 ≤ radiusSq p :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

@[fun_prop] theorem radiusSq_smooth : ContDiff ℝ ∞ radiusSq := by unfold radiusSq; fun_prop

 theorem HasCompactSupport.left_slice {F : Type*} [Zero F] {f : ℝ × ℝ → F}
    (hf : HasCompactSupport f) (y : ℝ) : HasCompactSupport (fun x => f (x,y)) := by
  apply HasCompactSupport.intro (hf.image continuous_fst)
  intro x hx
  by_contra hn
  exact hx ⟨(x,y),subset_tsupport f hn,rfl⟩

 theorem HasCompactSupport.right_slice {F : Type*} [Zero F] {f : ℝ × ℝ → F}
    (hf : HasCompactSupport f) (x : ℝ) : HasCompactSupport (fun y => f (x,y)) := by
  apply HasCompactSupport.intro (hf.image continuous_snd)
  intro y hy
  by_contra hn
  exact hy ⟨(x,y),subset_tsupport f hn,rfl⟩

 theorem integral_compact_partial_fst {f : ℝ × ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    (∫ z, fderiv ℝ f z (1,0))=0 := by
  have hd : ContDiff ℝ ∞ (fun z => fderiv ℝ f z (1,0)) :=
    (hf.fderiv_right (by simp)).clm_apply contDiff_const
  have hdc := hc.fderiv_apply (𝕜 := ℝ) (1,0)
  rw [Measure.volume_eq_prod ℝ ℝ,integral_prod_symm _
    (hd.continuous.integrable_of_hasCompactSupport hdc)]
  have he (y : ℝ) : (∫ x, fderiv ℝ f (x,y) (1,0))=0 := by
    apply integral_eq_zero_of_hasDerivAt_of_integrable
      (f := fun x => f (x,y))
    · intro x
      exact ((hf.differentiable (by simp) (x,y)).hasFDerivAt).comp_hasDerivAt x
        ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))
    · exact (hd.continuous.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
        (HasCompactSupport.left_slice hdc y)
    · exact (hf.continuous.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
        (HasCompactSupport.left_slice hc y)
  simp_rw [he]
  exact integral_zero _ _

 theorem integral_compact_partial_snd {f : ℝ × ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    (∫ z, fderiv ℝ f z (0,1))=0 := by
  have hd : ContDiff ℝ ∞ (fun z => fderiv ℝ f z (0,1)) :=
    (hf.fderiv_right (by simp)).clm_apply contDiff_const
  have hdc := hc.fderiv_apply (𝕜 := ℝ) (0,1)
  rw [Measure.volume_eq_prod ℝ ℝ,integral_prod _
    (hd.continuous.integrable_of_hasCompactSupport hdc)]
  have he (x : ℝ) : (∫ y, fderiv ℝ f (x,y) (0,1))=0 := by
    apply integral_eq_zero_of_hasDerivAt_of_integrable
      (f := fun y => f (x,y))
    · intro y
      exact ((hf.differentiable (by simp) (x,y)).hasFDerivAt).comp_hasDerivAt y
        ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))
    · exact (hd.continuous.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
        (HasCompactSupport.right_slice hdc x)
    · exact (hf.continuous.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
        (HasCompactSupport.right_slice hc x)
  simp_rw [he]
  exact integral_zero _ _

 theorem compact_planar_stokes {α : (ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] ℝ}
    (hα : ContDiff ℝ ∞ α) (hc : HasCompactSupport α) :
    (∫ z, fderiv ℝ α z (1,0) (0,1) - fderiv ℝ α z (0,1) (1,0))=0 := by
  have h1 : ContDiff ℝ ∞ (fun z => α z (0,1)) := hα.clm_apply contDiff_const
  have h2 : ContDiff ℝ ∞ (fun z => α z (1,0)) := hα.clm_apply contDiff_const
  have hc1 : HasCompactSupport (fun z => α z (0,1)) := hc.comp_left (g := fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (0,1)) rfl
  have hc2 : HasCompactSupport (fun z => α z (1,0)) := hc.comp_left (g := fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (1,0)) rfl
  have he1 (z v : ℝ × ℝ) : fderiv ℝ (fun z => α z (0,1)) z v=fderiv ℝ α z v (0,1) := by
    rw [fderiv_clm_apply (hα.differentiable (by simp) z) (differentiableAt_const _)]
    simp only [add_apply,ContinuousLinearMap.comp_apply,fderiv_const_apply,
      zero_apply,map_zero,zero_add,ContinuousLinearMap.flip_apply]
  have he2 (z v : ℝ × ℝ) : fderiv ℝ (fun z => α z (1,0)) z v=fderiv ℝ α z v (1,0) := by
    rw [fderiv_clm_apply (hα.differentiable (by simp) z) (differentiableAt_const _)]
    simp only [add_apply,ContinuousLinearMap.comp_apply,fderiv_const_apply,
      zero_apply,map_zero,zero_add,ContinuousLinearMap.flip_apply]
  have hd1 : ContDiff ℝ ∞ (fun z => fderiv ℝ (fun z => α z (0,1)) z (1,0)) :=
    (h1.fderiv_right (by simp)).clm_apply contDiff_const
  have hd2 : ContDiff ℝ ∞ (fun z => fderiv ℝ (fun z => α z (1,0)) z (0,1)) :=
    (h2.fderiv_right (by simp)).clm_apply contDiff_const
  simp_rw [← he1,← he2]
  rw [integral_sub
    (hd1.continuous.integrable_of_hasCompactSupport
      (hc1.fderiv_apply (𝕜 := ℝ) (1,0)))
    (hd2.continuous.integrable_of_hasCompactSupport
      (hc2.fderiv_apply (𝕜 := ℝ) (0,1))),
    integral_compact_partial_fst h1 hc1,integral_compact_partial_snd h2 hc2,sub_self]

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
-- module Solutions.OAIQ10_BP.BallPacking_Cauchy_GreenFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SymplecticBallPacking.Hamiltonian
open scoped ContDiff Topology
open Set Function Filter MeasureTheory

theorem plane_deriv_first {F : Plane → ℝ} (hF : Differentiable ℝ F) (p : Plane) :
    deriv (fun x => F (x,p.2)) p.1 = fderiv ℝ F p (1,0) := by
  exact ((hF p).hasFDerivAt.comp_hasDerivAt p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))).deriv

theorem plane_deriv_second {F : Plane → ℝ} (hF : Differentiable ℝ F) (p : Plane) :
    deriv (fun t => F (p.1,t)) p.2 = fderiv ℝ F p (0,1) := by
  exact ((hF p).hasFDerivAt.comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))).deriv

def pullbackForm (phi : Plane → Plane) (alpha : Plane → Plane →L[ℝ] ℝ)
    (p : Plane) : Plane →L[ℝ] ℝ := (alpha (phi p)).comp (fderiv ℝ phi p)

theorem bilinear_skew_plane (B : Plane →L[ℝ] Plane →L[ℝ] ℝ) (u v : Plane) :
    B u v - B v u = (B (1,0) (0,1)-B (0,1) (1,0))*planarArea u v := by
  have hu : u = u.1 • ((1:ℝ),(0:ℝ)) + u.2 • ((0:ℝ),(1:ℝ)) := by ext <;> simp
  have hv : v = v.1 • ((1:ℝ),(0:ℝ)) + v.2 • ((0:ℝ),(1:ℝ)) := by ext <;> simp
  conv_lhs => rw [hu,hv]
  simp only [map_add,map_smul,add_apply,smul_apply,
    smul_eq_mul,planarArea_apply]
  ring

theorem pullbackForm_smooth {phi : Plane → Plane} (hp : ContDiff ℝ ∞ phi)
    {alpha : Plane → Plane →L[ℝ] ℝ} (ha : ContDiff ℝ ∞ alpha) :
    ContDiff ℝ ∞ (pullbackForm phi alpha) :=
  (ha.comp hp).clm_comp (hp.fderiv_right (by simp))

theorem pullbackForm_curl {phi : Plane → Plane} (hp : ContDiff ℝ ∞ phi)
    {alpha : Plane → Plane →L[ℝ] ℝ} (ha : ContDiff ℝ ∞ alpha) (p : Plane) :
    planarCurl (pullbackForm phi alpha) p = planarCurl alpha (phi p) *
      planarArea (fderiv ℝ phi p (1,0)) (fderiv ℝ phi p (0,1)) := by
  have hd := (((ha.differentiable (by simp)) (phi p)).hasFDerivAt.comp p
    (((hp.differentiable (by simp)) p).hasFDerivAt)).clm_comp
      (((hp.fderiv_right (by simp : (∞ : ℕ∞ω)+1 ≤ ∞)).differentiable (by simp) p).hasFDerivAt)
  have hs := (hp.contDiffAt (x := p)).isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  dsimp only [Function.comp_def] at hd
  unfold planarCurl pullbackForm
  rw [hd.fderiv]
  simp only [add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply,ContinuousLinearMap.flip_apply]
  rw [hs.eq (1,0) (0,1)]
  have hb := bilinear_skew_plane (fderiv ℝ alpha (phi p))
    (fderiv ℝ phi p (1,0)) (fderiv ℝ phi p (0,1))
  linear_combination hb

theorem integral_curl_rectangle {alpha : Plane → Plane →L[ℝ] ℝ}
    (ha : ContDiff ℝ ∞ alpha) (a b : Plane) (hab : a ≤ b) :
    (∫ p in Icc a b, planarCurl alpha p) =
      ((∫ t in a.2..b.2, alpha (b.1,t) (0,1)) - ∫ t in a.2..b.2, alpha (a.1,t) (0,1)) -
      ((∫ r in a.1..b.1, alpha (r,b.2) (1,0)) - ∫ r in a.1..b.1, alpha (r,a.2) (1,0)) := by
  let F : Plane → ℝ := fun p => alpha p (0,1)
  let G : Plane → ℝ := fun p => -alpha p (1,0)
  have hF : ContDiff ℝ ∞ F := ha.clm_apply contDiff_const
  have hG : ContDiff ℝ ∞ G := (ha.clm_apply contDiff_const).neg
  have hFd (p : Plane) : fderiv ℝ F p =
      (ContinuousLinearMap.apply ℝ ℝ (0,1)).comp (fderiv ℝ alpha p) :=
    ((ContinuousLinearMap.apply ℝ ℝ (0,1) : (Plane →L[ℝ] ℝ) →L[ℝ] ℝ).hasFDerivAt.comp p
      ((ha.differentiable (by simp)) p).hasFDerivAt).fderiv
  have hGd (p : Plane) : fderiv ℝ G p =
      -((ContinuousLinearMap.apply ℝ ℝ (1,0)).comp (fderiv ℝ alpha p)) :=
    (((ContinuousLinearMap.apply ℝ ℝ (1,0) : (Plane →L[ℝ] ℝ) →L[ℝ] ℝ).hasFDerivAt.comp p
      ((ha.differentiable (by simp)) p).hasFDerivAt).neg).fderiv
  have he (p : Plane) : fderiv ℝ F p (1,0)+fderiv ℝ G p (0,1) = planarCurl alpha p := by
    rw [hFd,hGd]
    rfl
  have hi : IntegrableOn (fun p => fderiv ℝ F p (1,0)+fderiv ℝ G p (0,1)) (Icc a b) :=
    (((hF.continuous_fderiv (by simp)).clm_apply continuous_const).add
      ((hG.continuous_fderiv (by simp)).clm_apply continuous_const)).continuousOn.integrableOn_compact isCompact_Icc
  have hg := integral_divergence_prod_Icc_of_hasFDerivAt_of_le F G
    (fderiv ℝ F) (fderiv ℝ G) a b hab hF.continuous.continuousOn hG.continuous.continuousOn
    (fun p _ => ((hF.differentiable (by simp)) p).hasFDerivAt)
    (fun p _ => ((hG.differentiable (by simp)) p).hasFDerivAt) hi
  simp_rw [he] at hg
  simp only [F,G,intervalIntegral.integral_neg] at hg
  linear_combination hg

@[fun_prop] theorem polar_smooth : ContDiff ℝ ∞ (polarCoord.symm : Plane → Plane) := by
  change ContDiff ℝ ∞ (fun p : Plane => (p.1*Real.cos p.2,p.1*Real.sin p.2))
  fun_prop

theorem polar_deriv_first (p : Plane) :
    fderiv ℝ polarCoord.symm p (1,0) = (Real.cos p.2,Real.sin p.2) := by
  rw [(hasFDerivAt_polarCoord_symm p).fderiv]
  simp [fderivPolarCoordSymm,Matrix.toLin_finTwoProd_toContinuousLinearMap]

theorem polar_deriv_second (p : Plane) :
    fderiv ℝ polarCoord.symm p (0,1) = (-p.1*Real.sin p.2,p.1*Real.cos p.2) := by
  rw [(hasFDerivAt_polarCoord_symm p).fderiv]
  simp [fderivPolarCoordSymm,Matrix.toLin_finTwoProd_toContinuousLinearMap]

theorem polar_area (p : Plane) :
    planarArea (fderiv ℝ polarCoord.symm p (1,0)) (fderiv ℝ polarCoord.symm p (0,1)) = p.1 := by
  rw [polar_deriv_first,polar_deriv_second,planarArea_apply]
  have ht := Real.cos_sq_add_sin_sq p.2
  dsimp
  linear_combination p.1 * ht

theorem integral_curl_polar_rectangle {alpha : Plane → Plane →L[ℝ] ℝ}
    (ha : ContDiff ℝ ∞ alpha) {R : ℝ} (hR : 0 ≤ R) :
    (∫ p in Icc ((0:ℝ),-Real.pi) (R,Real.pi), p.1*planarCurl alpha (polarCoord.symm p)) =
      ∫ t in -Real.pi..Real.pi,
        alpha (polarCoord.symm (R,t)) (-R*Real.sin t,R*Real.cos t) := by
  let eta := pullbackForm polarCoord.symm alpha
  have he (p : Plane) : planarCurl eta p = p.1*planarCurl alpha (polarCoord.symm p) := by
    rw [pullbackForm_curl polar_smooth ha,polar_area,mul_comm]
  have h := integral_curl_rectangle (pullbackForm_smooth polar_smooth ha)
    ((0:ℝ),-Real.pi) (R,Real.pi) ⟨hR,by linarith [Real.pi_pos]⟩
  change (∫ p in Icc ((0:ℝ),-Real.pi) (R,Real.pi), planarCurl eta p) = _ at h
  simp_rw [he] at h
  have hside (r : ℝ) : eta (r,Real.pi) (1,0) = eta (r,-Real.pi) (1,0) := by
    simp [eta,pullbackForm,polar_deriv_first,polarCoord_symm_apply]
  have hin (t : ℝ) : eta (0,t) (0,1) = 0 := by
    simp [eta,pullbackForm,polar_deriv_second,Prod.mk_zero_zero]
  have hout (t : ℝ) : eta (R,t) (0,1) =
      alpha (polarCoord.symm (R,t)) (-R*Real.sin t,R*Real.cos t) := by
    simp [eta,pullbackForm,polar_deriv_second]
  change _ = ((∫ t in -Real.pi..Real.pi, eta (R,t) (0,1)) -
    ∫ t in -Real.pi..Real.pi, eta (0,t) (0,1)) -
    ((∫ r in (0:ℝ)..R, eta (r,Real.pi) (1,0)) - ∫ r in (0:ℝ)..R, eta (r,-Real.pi) (1,0)) at h
  simp_rw [hside,hin,hout] at h
  simpa using h

def roundDisk (R : ℝ) : Set Plane := {p | p.1^2+p.2^2 < R^2}

theorem polar_mem_roundDisk {R : ℝ} (hR : 0 < R) {p : Plane} (hp : 0 < p.1) :
    polarCoord.symm p ∈ roundDisk R ↔ p.1 < R := by
  have hn : (polarCoord.symm p).1^2+(polarCoord.symm p).2^2 = p.1^2 := by
    simp only [polarCoord_symm_apply]
    linear_combination p.1^2 * Real.cos_sq_add_sin_sq p.2
  change (polarCoord.symm p).1^2+(polarCoord.symm p).2^2 < R^2 ↔ _
  rw [hn]
  constructor <;> intro h <;> nlinarith

theorem integral_roundDisk_polar (f : Plane → ℝ) {R : ℝ} (hR : 0 < R) :
    (∫ p in roundDisk R, f p) =
      ∫ p in Icc ((0:ℝ),-Real.pi) (R,Real.pi), p.1*f (polarCoord.symm p) := by
  have hm : MeasurableSet (roundDisk R) :=
    (isOpen_lt ((continuous_fst.pow 2).add (continuous_snd.pow 2)) continuous_const).measurableSet
  let S : Set Plane := {p | p.1 < R}
  have hS : MeasurableSet S := (isOpen_lt continuous_fst continuous_const).measurableSet
  have he (p : Plane) (hp : p ∈ polarCoord.target) :
      p.1 * (roundDisk R).indicator f (polarCoord.symm p) =
        S.indicator (fun p => p.1*f (polarCoord.symm p)) p := by
    have hi := polar_mem_roundDisk hR hp.1
    by_cases ht : p.1 < R
    · simp only [indicator_of_mem (hi.mpr ht),indicator_of_mem (show p ∈ S from ht)]
    · simp only [indicator_of_notMem (mt hi.mp ht),indicator_of_notMem (show p ∉ S from ht),mul_zero]
  have hinter : polarCoord.target ∩ S = Ioo (0:ℝ) R ×ˢ Ioo (-Real.pi) Real.pi := by
    ext p
    simp only [polarCoord_target,mem_inter_iff,mem_prod,mem_Ioi,mem_Ioo,S,mem_ofPred_eq]
    tauto
  calc
    (∫ p in roundDisk R, f p) = ∫ p in polarCoord.target,
        p.1 * (roundDisk R).indicator f (polarCoord.symm p) := by
      rw [← integral_indicator hm]
      exact (integral_comp_polarCoord_symm ((roundDisk R).indicator f)).symm
    _ = ∫ p in polarCoord.target, S.indicator (fun p => p.1*f (polarCoord.symm p)) p :=
      setIntegral_congr_fun polarCoord.open_target.measurableSet he
    _ = ∫ p in Ioo (0:ℝ) R ×ˢ Ioo (-Real.pi) Real.pi, p.1*f (polarCoord.symm p) := by
      rw [setIntegral_indicator hS,hinter]
    _ = ∫ p in Icc ((0:ℝ),-Real.pi) (R,Real.pi), p.1*f (polarCoord.symm p) := by
      apply setIntegral_congr_set
      rw [Icc_prod_eq]
      exact MeasureTheory.Measure.set_prod_ae_eq MeasureTheory.Ioo_ae_eq_Icc MeasureTheory.Ioo_ae_eq_Icc

theorem integral_curl_roundDisk {alpha : Plane → Plane →L[ℝ] ℝ}
    (ha : ContDiff ℝ ∞ alpha) {R : ℝ} (hR : 0 < R) :
    (∫ p in roundDisk R, planarCurl alpha p) =
      ∫ t in -Real.pi..Real.pi,
        alpha (polarCoord.symm (R,t)) (-R*Real.sin t,R*Real.cos t) := by
  rw [integral_roundDisk_polar _ hR]
  exact integral_curl_polar_rectangle ha hR.le

def coordinateForm (U V : Plane → ℝ) (p : Plane) : Plane →L[ℝ] ℝ :=
  U p • ContinuousLinearMap.fst ℝ ℝ ℝ + V p • ContinuousLinearMap.snd ℝ ℝ ℝ

@[simp] theorem coordinateForm_apply (U V : Plane → ℝ) (p v : Plane) :
    coordinateForm U V p v = U p*v.1+V p*v.2 := rfl

theorem coordinateForm_smooth {U V : Plane → ℝ} (hU : ContDiff ℝ ∞ U)
    (hV : ContDiff ℝ ∞ V) : ContDiff ℝ ∞ (coordinateForm U V) :=
  (hU.smul contDiff_const).add (hV.smul contDiff_const)

theorem coordinateForm_compact {U V : Plane → ℝ} (hU : HasCompactSupport U)
    (hV : HasCompactSupport V) : HasCompactSupport (coordinateForm U V) := by
  apply HasCompactSupport.intro (hU.union hV)
  intro p hp
  have hu : U p = 0 := image_eq_zero_of_notMem_tsupport (fun h => hp (Or.inl h))
  have hv : V p = 0 := image_eq_zero_of_notMem_tsupport (fun h => hp (Or.inr h))
  simp only [coordinateForm,hu,hv,zero_smul,zero_add]

theorem form_eval_fderiv {alpha : Plane → Plane →L[ℝ] ℝ} (ha : ContDiff ℝ ∞ alpha)
    (p v w : Plane) : fderiv ℝ (fun q => alpha q w) p v = fderiv ℝ alpha p v w := by
  have he := ((ContinuousLinearMap.apply ℝ ℝ w : (Plane →L[ℝ] ℝ) →L[ℝ] ℝ).hasFDerivAt.comp p
    ((ha.differentiable (by simp)) p).hasFDerivAt).fderiv
  exact congrArg (fun D : Plane →L[ℝ] ℝ => D v) he

theorem coordinateForm_curl {U V : Plane → ℝ} (hU : ContDiff ℝ ∞ U)
    (hV : ContDiff ℝ ∞ V) (p : Plane) :
    planarCurl (coordinateForm U V) p =
      deriv (fun x => V (x,p.2)) p.1 - deriv (fun y => U (p.1,y)) p.2 := by
  rw [plane_deriv_first (hV.differentiable (by simp)),
    plane_deriv_second (hU.differentiable (by simp))]
  unfold planarCurl
  rw [← form_eval_fderiv (coordinateForm_smooth hU hV),
    ← form_eval_fderiv (coordinateForm_smooth hU hV)]
  simp only [coordinateForm_apply,mul_zero,mul_one,zero_add,add_zero]

end SymplecticBallPacking.Hamiltonian

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian

 theorem polar_complex_eq_circleMap (R t : ℝ) :
    Complex.equivRealProdCLM.symm (polarCoord.symm (R,t)) = circleMap 0 R t := by
  apply Complex.ext <;> simp [Complex.equivRealProdCLM_symm_apply,polarCoord_symm_apply,
    circleMap_zero_re,circleMap_zero_im,Complex.cos_ofReal_re,Complex.sin_ofReal_re]

 theorem angular_complex_eq_circleMap (R t : ℝ) :
    Complex.equivRealProdCLM.symm (-R*Real.sin t,R*Real.cos t) =
      Complex.I*circleMap 0 R t := by
  apply Complex.ext <;> simp [Complex.equivRealProdCLM_symm_apply,
    circleMap_zero_re,circleMap_zero_im,Complex.cos_ofReal_re,Complex.sin_ofReal_re]

 theorem roundDisk_measurable (R : ℝ) : MeasurableSet (roundDisk R) :=
  (isOpen_lt ((continuous_fst.pow 2).add (continuous_snd.pow 2)) continuous_const).measurableSet

 def cauchyCurl (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  Complex.I * fderiv ℝ f z 1 - fderiv ℝ f z Complex.I

 theorem cauchyCurl_smooth {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (cauchyCurl f) :=
  (contDiff_const.mul ((hf.fderiv_right (by simp)).clm_apply contDiff_const)).sub
    ((hf.fderiv_right (by simp)).clm_apply contDiff_const)

 theorem cauchyCurl_compact {f : ℂ → ℂ} (hf : HasCompactSupport f) :
    HasCompactSupport (cauchyCurl f) :=
  ((hf.fderiv_apply (𝕜 := ℝ) 1).comp_left (g := fun z : ℂ => Complex.I*z) (by simp)).sub
    (hf.fderiv_apply (𝕜 := ℝ) Complex.I)

 def projectedCauchyForm (L : ℂ →L[ℝ] ℝ) (f : ℂ → ℂ) : Plane → Plane →L[ℝ] ℝ :=
  coordinateForm (fun p => L (f (Complex.equivRealProdCLM.symm p)))
    (fun p => L (Complex.I*f (Complex.equivRealProdCLM.symm p)))

 theorem projectedCauchyForm_smooth (L : ℂ →L[ℝ] ℝ) {f : ℂ → ℂ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (projectedCauchyForm L f) := by
  exact coordinateForm_smooth
    (L.contDiff.comp (hf.comp Complex.equivRealProdCLM.symm.contDiff))
    (L.contDiff.comp (contDiff_const.mul (hf.comp Complex.equivRealProdCLM.symm.contDiff)))

 theorem projectedCauchyForm_compact (L : ℂ →L[ℝ] ℝ) {f : ℂ → ℂ}
    (hf : HasCompactSupport f) : HasCompactSupport (projectedCauchyForm L f) := by
  have hc := hf.comp_homeomorph Complex.equivRealProdCLM.symm.toHomeomorph
  exact coordinateForm_compact (hc.comp_left L.map_zero)
    (hc.comp_left (g := fun z : ℂ => L (Complex.I*z)) (by simp))

 theorem projectedCauchyForm_apply (L : ℂ →L[ℝ] ℝ) (f : ℂ → ℂ) (p v : Plane) :
    projectedCauchyForm L f p v =
      L (f (Complex.equivRealProdCLM.symm p)*Complex.equivRealProdCLM.symm v) := by
  have h (z : ℂ) : z*Complex.equivRealProdCLM.symm v =
      v.1 • z + v.2 • (Complex.I*z) := by
    apply Complex.ext <;> simp [Complex.equivRealProdCLM_symm_apply] <;> ring
  rw [h,map_add,map_smul,map_smul]
  simp only [projectedCauchyForm,coordinateForm_apply,smul_eq_mul]
  ring

 theorem projectedCauchyForm_curl (L : ℂ →L[ℝ] ℝ) {f : ℂ → ℂ}
    (hf : ContDiff ℝ ∞ f) (p : Plane) :
    planarCurl (projectedCauchyForm L f) p =
      L (cauchyCurl f (Complex.equivRealProdCLM.symm p)) := by
  have hb := (hf.differentiable (by simp) (Complex.equivRealProdCLM.symm p)).hasFDerivAt.comp
    p Complex.equivRealProdCLM.symm.hasFDerivAt
  have hu := L.hasFDerivAt.comp p hb
  have hv := L.hasFDerivAt.comp p (hb.const_mul Complex.I)
  have hU : ContDiff ℝ ∞ (fun p => L (f (Complex.equivRealProdCLM.symm p))) :=
    L.contDiff.comp (hf.comp Complex.equivRealProdCLM.symm.contDiff)
  have hV : ContDiff ℝ ∞ (fun p => L (Complex.I*f (Complex.equivRealProdCLM.symm p))) :=
    L.contDiff.comp (contDiff_const.mul (hf.comp Complex.equivRealProdCLM.symm.contDiff))
  rw [projectedCauchyForm,coordinateForm_curl hU hV,
    plane_deriv_first (hV.differentiable (by simp)),
    plane_deriv_second (hU.differentiable (by simp))]
  simp only [Function.comp_def] at hu hv
  rw [hu.fderiv,hv.fderiv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    smul_apply,smul_eq_mul,Complex.equivRealProdCLM_symm_apply,
    Complex.ofReal_one,Complex.ofReal_zero,zero_mul,one_mul,zero_add,add_zero]
  exact (map_sub L _ _).symm

 theorem complex_compact_stokes {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) :
    (∫ p : Plane, cauchyCurl f (Complex.equivRealProdCLM.symm p)) = 0 := by
  have hi : Integrable (fun p : Plane => cauchyCurl f (Complex.equivRealProdCLM.symm p)) :=
    ((cauchyCurl_smooth hf).continuous.comp Complex.equivRealProdCLM.symm.continuous).integrable_of_hasCompactSupport
        ((cauchyCurl_compact hc).comp_homeomorph Complex.equivRealProdCLM.symm.toHomeomorph)
  have hh (L : ℂ →L[ℝ] ℝ) : L (∫ p : Plane,
      cauchyCurl f (Complex.equivRealProdCLM.symm p))=0 := by
    rw [←L.integral_comp_comm hi]
    simp_rw [←projectedCauchyForm_curl L hf]
    exact compact_planar_stokes (projectedCauchyForm_smooth L hf)
      (projectedCauchyForm_compact L hc)
  exact Complex.ext (hh Complex.reCLM) (hh Complex.imCLM)

 theorem complex_disk_stokes {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) {R : ℝ} (hR : 0<R) :
    (∫ p in roundDisk R, cauchyCurl f (Complex.equivRealProdCLM.symm p)) =
      ∫ t in -Real.pi..Real.pi, f (circleMap 0 R t)*(Complex.I*circleMap 0 R t) := by
  have hi : Integrable (fun p : Plane => cauchyCurl f (Complex.equivRealProdCLM.symm p)) :=
    ((cauchyCurl_smooth hf).continuous.comp Complex.equivRealProdCLM.symm.continuous).integrable_of_hasCompactSupport
        ((cauchyCurl_compact hc).comp_homeomorph Complex.equivRealProdCLM.symm.toHomeomorph)
  have hb : IntervalIntegrable (fun t => f (circleMap 0 R t)*(Complex.I*circleMap 0 R t))
      volume (-Real.pi) Real.pi :=
    ((hf.continuous.comp (continuous_circleMap 0 R)).mul
      (continuous_const.mul (continuous_circleMap 0 R))).intervalIntegrable _ _
  have hh (L : ℂ →L[ℝ] ℝ) :
      L (∫ p in roundDisk R, cauchyCurl f (Complex.equivRealProdCLM.symm p)) =
      L (∫ t in -Real.pi..Real.pi, f (circleMap 0 R t)*(Complex.I*circleMap 0 R t)) := by
    rw [←L.integral_comp_comm hi.integrableOn,←L.intervalIntegral_comp_comm hb]
    simp_rw [←projectedCauchyForm_curl L hf]
    rw [integral_curl_roundDisk (projectedCauchyForm_smooth L hf) hR]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [projectedCauchyForm_apply,polar_complex_eq_circleMap,angular_complex_eq_circleMap]
  exact Complex.ext (hh Complex.reCLM) (hh Complex.imCLM)

 def cauchyInnerBump (R : ℝ) (hR : 0<R) : ContDiffBump (0:ℂ) where
  rIn := R/4
  rOut := R/2
  rIn_pos := by linarith
  rIn_lt_rOut := by linarith

 def cauchyPuncture (b : ContDiffBump (0:ℂ)) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1-b z) • (f z/z)

 theorem cauchyPuncture_compact (b : ContDiffBump (0:ℂ)) {f : ℂ → ℂ}
    (hc : HasCompactSupport f) : HasCompactSupport (cauchyPuncture b f) := by
  apply HasCompactSupport.intro hc
  intro z hz
  simp only [cauchyPuncture,image_eq_zero_of_notMem_tsupport hz,zero_div,smul_zero]

 theorem cauchyPuncture_smooth (b : ContDiffBump (0:ℂ)) {f : ℂ → ℂ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (cauchyPuncture b f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z=0
  · subst z
    apply (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq
    filter_upwards [b.eventuallyEq_one] with z hz
    simp only [cauchyPuncture,hz,Pi.one_apply,sub_self,zero_smul]
  · apply (contDiffAt_const.sub b.contDiff.contDiffAt).smul
    simpa only [div_eq_mul_inv] using hf.contDiffAt.mul (contDiffAt_inv (𝕜 := ℝ) hz)

 theorem cauchyPuncture_eventuallyEq (b : ContDiffBump (0:ℂ)) (f : ℂ → ℂ)
    {z : ℂ} (hz : b.rOut<‖z‖) :
    cauchyPuncture b f =ᶠ[𝓝 z] (fun w => f w/w) := by
  have hh : ∀ᶠ w in 𝓝 z, b.rOut<‖w‖ :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds hz
  filter_upwards [hh] with w hw
  have hb : b w=0 := b.zero_of_le_dist (by simpa only [dist_zero_right] using hw.le)
  simp only [cauchyPuncture,hb,sub_zero,one_smul]

 theorem cauchyCurl_div {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hz : z≠0) : cauchyCurl (fun w => f w/w) z = cauchyCurl f z/z := by
  have hd := hf.hasFDerivAt.mul ((hasDerivAt_inv hz).hasFDerivAt.restrictScalars ℝ)
  have he : (fun w => f w/w) = (fun w => f w*w⁻¹) := by
    funext w
    exact div_eq_mul_inv _ _
  change HasFDerivAt (fun w => f w*w⁻¹) _ z at hd
  rw [he,cauchyCurl,hd.fderiv]
  change Complex.I * (f z * (1 * (-(z^2)⁻¹)) + z⁻¹ * fderiv ℝ f z 1) -
    (f z * (Complex.I * (-(z^2)⁻¹)) + z⁻¹ * fderiv ℝ f z Complex.I) =
      (Complex.I * fderiv ℝ f z 1 - fderiv ℝ f z Complex.I) / z
  rw [div_eq_mul_inv]
  ring

 theorem cauchyPuncture_curl (b : ContDiffBump (0:ℂ)) {f : ℂ → ℂ}
    (hf : ContDiff ℝ ∞ f) {z : ℂ} (hz : b.rOut<‖z‖) :
    cauchyCurl (cauchyPuncture b f) z = cauchyCurl f z/z := by
  have he := (cauchyPuncture_eventuallyEq b f hz).fderiv_eq (𝕜 := ℝ)
  unfold cauchyCurl
  rw [he]
  exact cauchyCurl_div (hf.differentiable (by simp) z)
    (fun h => by simp only [h,norm_zero,not_lt_of_ge b.rOut_pos.le] at hz)

 theorem complexCartesian_norm_sq (p : Plane) :
    ‖Complex.equivRealProdCLM.symm p‖^2 = p.1^2+p.2^2 := by
  rw [Complex.sq_norm]
  simp [Complex.normSq_apply,Complex.equivRealProdCLM_symm_apply,pow_two]

 theorem complexCartesian_norm_ge_of_notMem {R : ℝ} (hR : 0<R) {p : Plane}
    (hp : p ∉ roundDisk R) : R≤‖Complex.equivRealProdCLM.symm p‖ := by
  have hn := norm_nonneg (Complex.equivRealProdCLM.symm p)
  have he := complexCartesian_norm_sq p
  change ¬p.1^2+p.2^2<R^2 at hp
  push Not at hp
  nlinarith

 theorem cauchy_exterior_integral {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) {R : ℝ} (hR : 0<R) :
    (∫ p in (roundDisk R)ᶜ,
      cauchyCurl f (Complex.equivRealProdCLM.symm p)/Complex.equivRealProdCLM.symm p) =
      -(Complex.I * ∫ t in -Real.pi..Real.pi, f (circleMap 0 R t)) := by
  let b := cauchyInnerBump R hR
  let g := cauchyPuncture b f
  have hg : ContDiff ℝ ∞ g := cauchyPuncture_smooth b hf
  have hgc : HasCompactSupport g := cauchyPuncture_compact b hc
  have hi : Integrable (fun p : Plane => cauchyCurl g (Complex.equivRealProdCLM.symm p)) :=
    ((cauchyCurl_smooth hg).continuous.comp Complex.equivRealProdCLM.symm.continuous).integrable_of_hasCompactSupport
        ((cauchyCurl_compact hgc).comp_homeomorph Complex.equivRealProdCLM.symm.toHomeomorph)
  have hs := integral_add_compl (roundDisk_measurable R) hi
  rw [complex_compact_stokes hg hgc,complex_disk_stokes hg hgc hR] at hs
  have he : (∫ p in (roundDisk R)ᶜ, cauchyCurl g (Complex.equivRealProdCLM.symm p)) =
      ∫ p in (roundDisk R)ᶜ,
        cauchyCurl f (Complex.equivRealProdCLM.symm p)/Complex.equivRealProdCLM.symm p := by
    apply setIntegral_congr_fun (roundDisk_measurable R).compl
    intro p hp
    apply cauchyPuncture_curl b hf
    have hh := complexCartesian_norm_ge_of_notMem hR hp
    change R/2 < _
    linarith
  have hb : (∫ t in -Real.pi..Real.pi, g (circleMap 0 R t)*(Complex.I*circleMap 0 R t)) =
      Complex.I * ∫ t in -Real.pi..Real.pi, f (circleMap 0 R t) := by
    rw [←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    have hn : b.rOut<‖circleMap 0 R t‖ := by
      rw [norm_circleMap_zero,abs_of_pos hR]
      change R/2<R
      linarith
    rw [show g (circleMap 0 R t)=f (circleMap 0 R t)/circleMap 0 R t from
      (cauchyPuncture_eventuallyEq b f hn).eq_of_nhds]
    field_simp [circleMap_ne_center hR.ne' (θ := t)]
  rw [he,hb] at hs
  exact eq_neg_of_add_eq_zero_right hs

 theorem cauchyCurl_div_integrable {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) : Integrable (fun z => cauchyCurl f z/z) := by
  simpa only [smul_eq_mul,div_eq_mul_inv,mul_comm] using
    locallyIntegrable_complex_inv.integrable_smul_right_of_hasCompactSupport
      (cauchyCurl_smooth hf).continuous (cauchyCurl_compact hc)

 theorem shrinking_exterior_aecover :
    AECover (volume : Measure Plane) (𝓝[>] (0:ℝ)) (fun R => (roundDisk R)ᶜ) := by
  refine ⟨?_,fun R => (roundDisk_measurable R).compl⟩
  filter_upwards [volume.ae_ne (0:Plane)] with p hp
  have hpos : 0<p.1^2+p.2^2 := by
    by_contra! hh
    have hx : p.1=0 := by nlinarith [sq_nonneg p.1,sq_nonneg p.2]
    have hy : p.2=0 := by nlinarith [sq_nonneg p.1,sq_nonneg p.2]
    exact hp (Prod.ext hx hy)
  have hsq : ContinuousAt (fun R : ℝ => R^2) 0 := by fun_prop
  have ht : Tendsto (fun R : ℝ => R^2) (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) := by
    simpa only [zero_pow (by decide : (2:ℕ)≠0)] using
      hsq.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
  filter_upwards [ht.eventually (Iio_mem_nhds hpos)] with R hR
  change ¬p.1^2+p.2^2<R^2
  exact not_lt_of_ge (le_of_lt hR)

 theorem circle_mean_integral_limit {f : ℂ → ℂ} (hf : Continuous f) :
    Tendsto (fun R : ℝ => ∫ t in -Real.pi..Real.pi, f (circleMap 0 R t))
      (𝓝 (0:ℝ)) (𝓝 ((2*Real.pi : ℝ) • f 0)) := by
  have hh : Continuous (fun p : ℝ×ℝ => f (circleMap 0 p.1 p.2)) := by
    apply hf.comp
    unfold circleMap
    fun_prop
  have hi := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) (f := fun R t : ℝ => f (circleMap 0 R t)) hh (-Real.pi) Real.pi
  convert (hi.continuousAt (x := (0:ℝ))).tendsto using 1
  all_goals try with_reducible_and_instances rfl
  simp only [circleMap,Complex.ofReal_zero,zero_mul,zero_add,intervalIntegral.integral_const]
  congr 1
  congr 1
  ring

 theorem cauchy_green_fundamental {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) :
    (∫ z : ℂ, cauchyCurl f z/z) = -(2*Real.pi*Complex.I)*f 0 := by
  have hp := Complex.volume_preserving_equiv_real_prod.symm
  have hi : Integrable (fun p : Plane =>
      cauchyCurl f (Complex.equivRealProdCLM.symm p)/Complex.equivRealProdCLM.symm p) :=
    hp.integrable_comp_of_integrable (cauchyCurl_div_integrable hf hc)
  have hl := ((circle_mean_integral_limit hf.continuous).const_mul Complex.I).neg
  have hl' : Tendsto (fun R : ℝ => ∫ p in (roundDisk R)ᶜ,
      cauchyCurl f (Complex.equivRealProdCLM.symm p)/Complex.equivRealProdCLM.symm p)
      (𝓝[>] (0:ℝ)) (𝓝 (-(2*Real.pi*Complex.I)*f 0)) := by
    have hh := hl.mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
    have heval : -(Complex.I * ((2*Real.pi:ℝ) • f 0)) =
        -(2*Real.pi*Complex.I)*f 0 := by
      rw [Complex.real_smul]
      push_cast
      ring
    rw [heval] at hh
    apply hh.congr'
    have hR : ∀ᶠ R in 𝓝[>] (0:ℝ), 0<R := self_mem_nhdsWithin
    filter_upwards [hR] with R hR
    exact (cauchy_exterior_integral hf hc hR).symm
  have he := shrinking_exterior_aecover.integral_eq_of_tendsto _ hi hl'
  rw [← hp.integral_comp' (fun z : ℂ => cauchyCurl f z/z)]
  exact he

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_KernelMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open Set Filter Function
open Set Filter MeasureTheory

open scoped ContDiff Topology
open Set Filter MeasureTheory
namespace HigherDimensionalBallPacking.Rigidity
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

 
def kernelMomentOne (K : ℂ → ℂ) : ℝ :=
  ∫ w : ℂ, ‖fderiv ℝ K w‖ * ‖w‖^((1:ℝ)/3)
def kernelMomentTwo (K : ℂ → ℂ) : ℝ :=
  ∫ w : ℂ, ‖fderiv ℝ (fderiv ℝ K) w‖ * ‖w‖^((1:ℝ)/3)

lemma weightedKernel_integrable {F : Type*} [NormedAddCommGroup F]
    {f : ℂ → F} (hf : Continuous f) (hc : HasCompactSupport f) :
    Integrable (fun w : ℂ => ‖f w‖*‖w‖^((1:ℝ)/3)) := by
  exact (hf.norm.mul (continuous_norm.rpow_const (fun _ => Or.inr (by norm_num)))).integrable_of_hasCompactSupport
    (hc.norm.mul_right)

lemma kernelMomentOne_nonneg (K : ℂ → ℂ) : 0 ≤ kernelMomentOne K :=
  integral_nonneg (fun _ => by positivity)
lemma kernelMomentTwo_nonneg (K : ℂ → ℂ) : 0 ≤ kernelMomentTwo K :=
  integral_nonneg (fun _ => by positivity)

lemma compactKernel_schauder_first {K : ℂ → ℂ}
    (hK : ContDiff ℝ ∞ K) (hc : HasCompactSupport K) {g : ℂ → E}
    (hg : Continuous g) {H : ℝ} (_hH : 0 ≤ H)
    (hHg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) (x : ℂ) :
    ‖fderiv ℝ (convolution K g (ContinuousLinearMap.lsmul ℝ ℂ) volume) x‖ ≤
      H*kernelMomentOne K := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ K) := hK.fderiv_right (by simp)
  have hb : ∀ x w v : ℂ,
      ‖fderiv ℝ K w v‖*‖g (x-w)-g x‖ ≤ (H*(‖fderiv ℝ K w‖*‖w‖^((1:ℝ)/3)))*‖v‖ := by
    intro x w v
    have hh : ‖g (x-w)-g x‖ ≤ H*‖w‖^((1:ℝ)/3) := by
      simpa only [sub_sub_cancel_left,norm_neg] using hHg (x-w) x
    calc
      _ ≤ (‖fderiv ℝ K w‖*‖v‖)*(H*‖w‖^((1:ℝ)/3)) :=
        mul_le_mul (ContinuousLinearMap.le_opNorm _ _) hh (norm_nonneg _) (by positivity)
      _ = _ := by ring
  apply (compact_kernel_convolution_derivative_bound hK hc hg
    ((weightedKernel_integrable hd.continuous (hc.fderiv ℝ)).const_mul H) hb x).trans_eq
  rw [integral_const_mul]
  rfl

omit [CompleteSpace E] in
lemma compactKernel_directional_eq {K : ℂ → ℂ}
    (hK : ContDiff ℝ ∞ K) (hc : HasCompactSupport K) {g : ℂ → E}
    (hg : Continuous g) (x v : ℂ) :
    fderiv ℝ (convolution K g (ContinuousLinearMap.lsmul ℝ ℂ) volume) x v =
      convolution (fun w => fderiv ℝ K w v) g (ContinuousLinearMap.lsmul ℝ ℂ) volume x :=
  compact_kernel_convolution_fderiv hK hc hg x v

lemma kernelMomentOne_directional_le {K : ℂ → ℂ}
    (hK : ContDiff ℝ ∞ K) (hc : HasCompactSupport K) (v : ℂ) :
    kernelMomentOne (fun w => fderiv ℝ K w v) ≤ kernelMomentTwo K*‖v‖ := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ K) := hK.fderiv_right (by simp)
  have hd₂ : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ K)) := hd.fderiv_right (by simp)
  have hLv : ContDiff ℝ ∞ (fun w => fderiv ℝ K w v) := hd.clm_apply contDiff_const
  have hcv := hc.fderiv_apply (𝕜 := ℝ) v
  have hb (w : ℂ) : ‖fderiv ℝ (fun z => fderiv ℝ K z v) w‖ ≤
      ‖fderiv ℝ (fderiv ℝ K) w‖*‖v‖ := by
    rw [((hd.differentiable (by simp) w).hasFDerivAt.clm_apply (hasFDerivAt_const v w)).fderiv]
    simp only [ContinuousLinearMap.comp_zero,zero_add]
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro y
    change ‖fderiv ℝ (fderiv ℝ K) w y v‖ ≤ _
    calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ K) w y‖*‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖fderiv ℝ (fderiv ℝ K) w‖*‖y‖)*‖v‖ :=
        mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ = _ := by ring

  calc
    _ ≤ ∫ w : ℂ, (‖fderiv ℝ (fderiv ℝ K) w‖*‖w‖^((1:ℝ)/3))*‖v‖ := by
      apply integral_mono
        (weightedKernel_integrable (hLv.fderiv_right (m := ∞) (by simp)).continuous (hcv.fderiv ℝ))
        ((weightedKernel_integrable hd₂.continuous ((hc.fderiv ℝ).fderiv ℝ)).mul_const _)
      intro w
      exact (mul_le_mul_of_nonneg_right (hb w) (Real.rpow_nonneg (norm_nonneg _) _)).trans_eq (by ring)
    _ = _ := integral_mul_const _ _

lemma compactKernel_schauder_second {K : ℂ → ℂ}
    (hK : ContDiff ℝ ∞ K) (hc : HasCompactSupport K) {g : ℂ → E}
    (hg : Continuous g) {H : ℝ} (hH : 0 ≤ H)
    (hHg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) (x y : ℂ) :
    ‖fderiv ℝ (convolution K g (ContinuousLinearMap.lsmul ℝ ℂ) volume) x -
      fderiv ℝ (convolution K g (ContinuousLinearMap.lsmul ℝ ℂ) volume) y‖ ≤
      H*kernelMomentTwo K*‖x-y‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity [kernelMomentTwo_nonneg K])
  intro v
  simp only [sub_apply]
  rw [compactKernel_directional_eq hK hc hg,compactKernel_directional_eq hK hc hg]
  let Kv : ℂ → ℂ := fun w => fderiv ℝ K w v
  have hKv : ContDiff ℝ ∞ Kv := (hK.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hcKv : HasCompactSupport Kv := hc.fderiv_apply (𝕜 := ℝ) v
  have hbound (z : ℂ) : ‖fderiv ℝ (convolution Kv g (ContinuousLinearMap.lsmul ℝ ℂ) volume) z‖ ≤
      H*kernelMomentTwo K*‖v‖ := by
    exact (compactKernel_schauder_first hKv hcKv hg hH hHg z).trans
      ((mul_le_mul_of_nonneg_left (kernelMomentOne_directional_le hK hc v) hH).trans_eq (by ring))
  have hi := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
    (s := (univ : Set ℂ)) (fun z _ =>
      (hcKv.hasFDerivAt_convolution_left _ (hKv.of_le (by simp)) hg.locallyIntegrable z).differentiableAt)
    (fun z _ => hbound z) convex_univ (mem_univ y) (mem_univ x)
  exact hi.trans_eq (by ring)

end

open scoped ContDiff Topology
open Set Filter MeasureTheory
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

 

def scaledKernelPotential (K : ℂ → ℂ) (ε : ℝ) (g : ℂ → E) (x : ℂ) : E :=
  ε • convolution K (fun z => g (ε • z)) (ContinuousLinearMap.lsmul ℝ ℂ) volume (ε⁻¹ • x)

def scaledKernelDerivative (K : ℂ → ℂ) (ε : ℝ) (g : ℂ → E) (x : ℂ) : ℂ →L[ℝ] E :=
  fderiv ℝ (convolution K (fun z => g (ε • z)) (ContinuousLinearMap.lsmul ℝ ℂ) volume) (ε⁻¹ • x)

omit [CompleteSpace E] in
lemma scaledKernel_hasFDerivAt {K : ℂ → ℂ} (hK : ContDiff ℝ ∞ K)
    (hc : HasCompactSupport K) {ε : ℝ} (hε : ε ≠ 0) {g : ℂ → E}
    (hg : Continuous g) (x : ℂ) :
    HasFDerivAt (scaledKernelPotential K ε g) (scaledKernelDerivative K ε g x) x := by
  have hgε : Continuous (fun z : ℂ => g (ε • z)) := by fun_prop
  have hd := hc.hasFDerivAt_convolution_left (μ := volume) (ContinuousLinearMap.lsmul ℝ ℂ)
    (hK.of_le (by simp)) hgε.locallyIntegrable (ε⁻¹ • x)
  have hd' := (hd.comp x ((hasFDerivAt_id x).const_smul ε⁻¹)).const_smul ε
  have he : ε • (fderiv ℝ (convolution K (fun z => g (ε • z))
      (ContinuousLinearMap.lsmul ℝ ℂ) volume) (ε⁻¹ • x)).comp
        (ε⁻¹ • ContinuousLinearMap.id ℝ ℂ) = scaledKernelDerivative K ε g x := by
    ext v
    simp only [smul_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,map_smul,
      smul_smul,mul_inv_cancel₀ hε,one_smul,scaledKernelDerivative]
  rw [←hd.fderiv] at hd'
  rw [he] at hd'
  exact hd'

omit [NormedSpace ℂ E] [CompleteSpace E] in
lemma scaled_holder_bound {g : ℂ → E} {H ε : ℝ} (hε : 0 ≤ ε)
    (hHg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) (x y : ℂ) :
    ‖g (ε • x)-g (ε • y)‖ ≤ (H*ε^((1:ℝ)/3))*‖x-y‖^((1:ℝ)/3) := by
  have h := hHg (ε • x) (ε • y)
  rw [←smul_sub,norm_smul,Real.norm_of_nonneg hε,Real.mul_rpow hε (norm_nonneg _)] at h
  exact h.trans_eq (by ring)

lemma scaledKernel_derivative_bound {K : ℂ → ℂ} (hK : ContDiff ℝ ∞ K)
    (hc : HasCompactSupport K) {ε : ℝ} (hε : 0 ≤ ε) {g : ℂ → E}
    (hg : Continuous g) {H : ℝ} (hH : 0 ≤ H)
    (hHg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) (x : ℂ) :
    ‖scaledKernelDerivative K ε g x‖ ≤ (H*kernelMomentOne K)*ε^((1:ℝ)/3) := by
  have hd := compactKernel_schauder_first hK hc
    (g := fun z : ℂ => g (ε • z)) (by fun_prop)
    (mul_nonneg hH (Real.rpow_nonneg hε ((1:ℝ)/3))) (scaled_holder_bound hε hHg) (ε⁻¹ • x)
  exact hd.trans_eq (by ring)

lemma scaledKernel_derivative_lipschitz {K : ℂ → ℂ} (hK : ContDiff ℝ ∞ K)
    (hc : HasCompactSupport K) {ε : ℝ} (hε : 0 < ε) {g : ℂ → E}
    (hg : Continuous g) {H : ℝ} (hH : 0 ≤ H)
    (hHg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) (x y : ℂ) :
    ‖scaledKernelDerivative K ε g x-scaledKernelDerivative K ε g y‖ ≤
      (H*kernelMomentTwo K)*(ε^((1:ℝ)/3)*ε⁻¹)*‖x-y‖ := by
  have hd := compactKernel_schauder_second hK hc
    (g := fun z : ℂ => g (ε • z)) (by fun_prop)
    (mul_nonneg hH (Real.rpow_nonneg hε.le ((1:ℝ)/3))) (scaled_holder_bound hε.le hHg) (ε⁻¹ • x) (ε⁻¹ • y)
  rw [←smul_sub,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hε.le)] at hd
  exact hd.trans_eq (by ring)

omit [CompleteSpace E] in
lemma scaledKernel_value_bound {K : ℂ → ℂ} (hK : Continuous K)
    (hc : HasCompactSupport K) {ε : ℝ} (hε : 0 ≤ ε) {g : ℂ → E}
    {M : ℝ} (hM : ∀ x, ‖g x‖ ≤ M) (x : ℂ) :
    ‖scaledKernelPotential K ε g x‖ ≤ ((∫ w : ℂ, ‖K w‖)*M)*ε := by
  rw [scaledKernelPotential,norm_smul,Real.norm_of_nonneg hε]
  have hb : ‖convolution K (fun z => g (ε • z)) (ContinuousLinearMap.lsmul ℝ ℂ) volume (ε⁻¹ • x)‖ ≤
      (∫ w : ℂ, ‖K w‖)*M := by
    have hin : ∀ w : ℂ, ‖K w • g (ε • (ε⁻¹ • x-w))‖ ≤ ‖K w‖*M := by
      intro w
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
    apply (norm_integral_le_of_norm_le ((hK.integrable_of_hasCompactSupport hc).norm.mul_const M)
      (Eventually.of_forall hin)).trans_eq
    exact integral_mul_const _ _
  exact (mul_le_mul_of_nonneg_left hb hε).trans_eq (by ring)

lemma eighth_rpow_third (j : ℕ) : (((1:ℝ)/8)^j)^((1:ℝ)/3)=((1:ℝ)/2)^j := by
  have hbase : ((1:ℝ)/8)^((1:ℝ)/3)=(1:ℝ)/2 := by
    have h := Real.pow_rpow_inv_natCast (by norm_num : (0:ℝ)≤1/2) (by decide : (3:ℕ)≠0)
    norm_num at h ⊢
  rw [←Real.rpow_natCast_mul (by norm_num),mul_comm,Real.rpow_mul (by norm_num),Real.rpow_natCast,hbase]

lemma eighth_scale_lipschitz (j : ℕ) :
    ((((1:ℝ)/8)^j)^((1:ℝ)/3))*(((1:ℝ)/8)^j)⁻¹=(4:ℝ)^j := by
  rw [eighth_rpow_third,←inv_pow,←mul_pow]
  norm_num

end

open scoped ContDiff Topology
open Set Filter MeasureTheory

 
def annularCauchyKernel (b : ContDiffBump (0:ℂ)) (z : ℂ) : ℂ :=
  (b z-b ((8:ℝ) • z)) • z⁻¹

lemma annularCauchyKernel_smooth (b : ContDiffBump (0:ℂ)) :
    ContDiff ℝ ∞ (annularCauchyKernel b) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z=0
  · subst z
    have h0 : ContDiffAt ℝ ∞ (fun _ : ℂ => (0:ℂ)) 0 := contDiffAt_const
    apply h0.congr_of_eventuallyEq
    have ht : Tendsto (fun z : ℂ => (8:ℝ) • z) (𝓝 0) (𝓝 0) := by
      have hcont : Continuous (fun z : ℂ => (8:ℝ) • z) := by fun_prop
      simpa only [smul_zero] using hcont.tendsto (0:ℂ)
    filter_upwards [b.eventuallyEq_one, ht.eventually b.eventuallyEq_one] with w hw hw'
    simp only [annularCauchyKernel,hw,hw',Pi.one_apply,sub_self,zero_smul]
  · exact (b.contDiff.contDiffAt.sub
      (b.contDiff.comp (contDiff_id.const_smul (8:ℝ))).contDiffAt).smul
      (contDiffAt_id.inv hz)

lemma annularCauchyKernel_compactSupport (b : ContDiffBump (0:ℂ)) :
    HasCompactSupport (annularCauchyKernel b) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0:ℂ) b.rOut)
  intro z hz
  have hz' : b.rOut < ‖z‖ := by
    simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hz
  have hz8 : b.rOut ≤ ‖(8:ℝ) • z‖ := by
    rw [norm_smul]
    norm_num
    linarith [norm_nonneg z]
  rw [annularCauchyKernel,b.zero_of_le_dist (by simpa only [dist_zero_right] using hz'.le),
    b.zero_of_le_dist (by simpa only [dist_zero_right] using hz8),sub_self,zero_smul]


 

open scoped Topology
open Set Filter Finset
section
variable {X F : Type*} [PseudoMetricSpace X] [NormedAddCommGroup F] [CompleteSpace F]

lemma dyadic_summable : Summable (fun j : ℕ => ((1:ℝ)/2)^j) :=
  summable_geometric_of_norm_lt_one (by norm_num)

lemma dyadic_tsum : (∑' j : ℕ, ((1:ℝ)/2)^j) = 2 := by
  rw [tsum_geometric_of_norm_lt_one (by norm_num : ‖(1:ℝ)/2‖<1)]
  norm_num

lemma four_pow_sum_le (N : ℕ) : ∑ j ∈ range N, (4:ℝ)^j ≤ 4^N := by
  induction N with
  | zero => norm_num
  | succ N h =>
    rw [sum_range_succ,pow_succ]
    nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤4) N]

omit [PseudoMetricSpace X] in
lemma dyadicSeries_summable (f : ℕ → X → F) (A : ℝ)
    (hA : ∀ j x, ‖f j x‖≤A*((1:ℝ)/2)^j) (x : X) : Summable (fun j => f j x) :=
  (dyadic_summable.mul_left A).of_norm_bounded (fun j => hA j x)

lemma dyadicSeries_split_bound (f : ℕ → X → F) {A B : ℝ} (_hA₀ : 0≤A) (hB₀ : 0≤B)
    (hA : ∀ j x, ‖f j x‖≤A*((1:ℝ)/2)^j)
    (hB : ∀ j x y, ‖f j x-f j y‖≤B*4^j*dist x y) (x y : X) (N : ℕ) :
    ‖(∑' j, f j x)-(∑' j, f j y)‖ ≤ B*dist x y*4^N+4*A*((1:ℝ)/2)^N := by
  have hsx := dyadicSeries_summable f A hA x
  have hsy := dyadicSeries_summable f A hA y
  have hs := hsx.sub hsy
  rw [←hsx.tsum_sub hsy,←hs.sum_add_tsum_nat_add N]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · calc
      ‖∑ j ∈ range N, (f j x-f j y)‖ ≤ ∑ j ∈ range N, ‖f j x-f j y‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ range N, B*4^j*dist x y := sum_le_sum (fun j _ => hB j x y)
      _ = B*dist x y*(∑ j ∈ range N, (4:ℝ)^j) := by rw [mul_sum]; apply sum_congr rfl; intros; ring
      _ ≤ B*dist x y*4^N := mul_le_mul_of_nonneg_left (four_pow_sum_le N) (mul_nonneg hB₀ dist_nonneg)
  · have htail : HasSum (fun j : ℕ => 2*A*(((1:ℝ)/2)^N)*((1:ℝ)/2)^j)
        (4*A*((1:ℝ)/2)^N) := by
      have h := dyadic_summable.hasSum.mul_left (2*A*((1:ℝ)/2)^N)
      rw [dyadic_tsum] at h
      have he : 2*A*((1:ℝ)/2)^N*2 = 4*A*((1:ℝ)/2)^N := by ring
      rw [he] at h
      exact h
    apply tsum_of_norm_bounded htail
    intro j
    calc
      ‖f (j+N) x-f (j+N) y‖ ≤ ‖f (j+N) x‖+‖f (j+N) y‖ := norm_sub_le _ _
      _ ≤ A*((1:ℝ)/2)^(j+N)+A*((1:ℝ)/2)^(j+N) := add_le_add (hA _ _) (hA _ _)
      _ = _ := by rw [pow_add]; ring

 
lemma dyadic_cubic_scale {d : ℝ} (hd : 0<d) (hd₁ : d≤1) :
    ∃ N : ℕ, d*4^N ≤ d^((1:ℝ)/3) ∧ ((1:ℝ)/2)^N ≤ 2*d^((1:ℝ)/3) := by
  let t : ℝ := d^((1:ℝ)/3)
  have ht : 0<t := Real.rpow_pos_of_pos hd _
  have ht₁ : t≤1 := Real.rpow_le_one hd.le hd₁ (by norm_num)
  obtain ⟨N,hlo,hhi⟩ := exists_nat_pow_near_of_lt_one ht ht₁
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1:ℝ)/2<1)
  have hc : t^3=d := by
    dsimp [t]
    rw [←Real.rpow_natCast,←Real.rpow_mul hd.le]
    norm_num
  have hn : (((1:ℝ)/2)^N)^2*4^N=1 := by
    rw [←pow_mul, Nat.mul_comm N 2, pow_mul, ←mul_pow]
    norm_num
  have hhi₂ : t^2 ≤ (((1:ℝ)/2)^N)^2 := pow_le_pow_left₀ ht.le hhi 2
  refine ⟨N,?_,?_⟩
  · have h : t^2*4^N≤1 := (mul_le_mul_of_nonneg_right hhi₂ (by positivity)).trans_eq hn
    calc
      d*4^N = t*(t^2*4^N) := by rw [←hc]; ring
      _ ≤ t*1 := mul_le_mul_of_nonneg_left h ht.le
      _ = _ := mul_one t
  · rw [pow_succ] at hlo
    change ((1:ℝ)/2)^N ≤ 2*t
    linarith

theorem dyadicSeries_holder (f : ℕ → X → F) {A B : ℝ} (hA₀ : 0≤A) (hB₀ : 0≤B)
    (hA : ∀ j x, ‖f j x‖≤A*((1:ℝ)/2)^j)
    (hB : ∀ j x y, ‖f j x-f j y‖≤B*4^j*dist x y) (x y : X) :
    ‖(∑' j, f j x)-(∑' j, f j y)‖ ≤ (B+8*A)*(dist x y)^((1:ℝ)/3) := by
  by_cases hzero : dist x y=0
  · have he : ∀ j, f j x=f j y := fun j => sub_eq_zero.mp (norm_eq_zero.mp
      (le_antisymm (by simpa only [hzero,mul_zero] using hB j x y) (norm_nonneg _)))
    simp only [he,sub_self,norm_zero]
    positivity
  have hd : 0<dist x y := lt_of_le_of_ne dist_nonneg (Ne.symm hzero)
  by_cases hd₁ : dist x y≤1
  · obtain ⟨N,hhead,htail⟩ := dyadic_cubic_scale hd hd₁
    apply (dyadicSeries_split_bound f hA₀ hB₀ hA hB x y N).trans
    have hh := mul_le_mul_of_nonneg_left hhead hB₀
    have ht := mul_le_mul_of_nonneg_left htail (mul_nonneg (by norm_num : (0:ℝ)≤4) hA₀)
    nlinarith
  · have hsx := dyadicSeries_summable f A hA x
    have hsy := dyadicSeries_summable f A hA y
    have hb : ‖(∑' j, f j x)-(∑' j, f j y)‖ ≤ 4*A := by
      have hsum : HasSum (fun j : ℕ => A*((1:ℝ)/2)^j) (2*A) := by
        have h := dyadic_summable.hasSum.mul_left A
        rw [dyadic_tsum] at h
        have he : A*2 = 2*A := by ring
        rw [he] at h
        exact h
      exact (norm_sub_le _ _).trans ((add_le_add
        (tsum_of_norm_bounded hsum (fun j => hA j x))
        (tsum_of_norm_bounded hsum (fun j => hA j y))).trans_eq (by ring))
    have hr : 1≤(dist x y)^((1:ℝ)/3) := Real.one_le_rpow (le_of_not_ge hd₁) (by norm_num)
    exact hb.trans ((le_mul_of_one_le_right (by positivity) hr).trans
      (mul_le_mul_of_nonneg_right (by linarith : 4*A≤B+8*A) (Real.rpow_nonneg dist_nonneg _)))

end

open scoped ContDiff Topology
open Set Filter MeasureTheory
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def dyadicKernelPotential (K : ℂ → ℂ) (g : ℂ → E) (x : ℂ) : E :=
  ∑' j : ℕ, scaledKernelPotential K (((1:ℝ)/8)^j) g x

def dyadicKernelDerivative (K : ℂ → ℂ) (g : ℂ → E) (x : ℂ) : ℂ →L[ℝ] E :=
  ∑' j : ℕ, scaledKernelDerivative K (((1:ℝ)/8)^j) g x

lemma dyadicKernel_value_summable {K : ℂ → ℂ} (hK : Continuous K)
    (hc : HasCompactSupport K) {g : ℂ → E} {M : ℝ} (hM : ∀ x, ‖g x‖ ≤ M) (x : ℂ) :
    Summable (fun j : ℕ => scaledKernelPotential K (((1:ℝ)/8)^j) g x) := by
  apply ((summable_geometric_of_norm_lt_one (by norm_num : ‖(1:ℝ)/8‖ < 1)).mul_left
    ((∫ w : ℂ, ‖K w‖)*M)).of_norm_bounded
  intro j
  exact scaledKernel_value_bound hK hc (by positivity) hM x

lemma dyadicKernel_derivative_bound {K : ℂ → ℂ} (hK : ContDiff ℝ ∞ K)
    (hc : HasCompactSupport K) {g : ℂ → E} (hg : Continuous g) {H : ℝ} (hH : 0 ≤ H)
    (hHg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) (j : ℕ) (x : ℂ) :
    ‖scaledKernelDerivative K (((1:ℝ)/8)^j) g x‖ ≤ (H*kernelMomentOne K)*((1:ℝ)/2)^j := by
  simpa only [eighth_rpow_third] using scaledKernel_derivative_bound hK hc (ε := ((1:ℝ)/8)^j) (by positivity) hg hH hHg x

lemma dyadicKernel_derivative_lipschitz {K : ℂ → ℂ} (hK : ContDiff ℝ ∞ K)
    (hc : HasCompactSupport K) {g : ℂ → E} (hg : Continuous g) {H : ℝ} (hH : 0 ≤ H)
    (hHg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) (j : ℕ) (x y : ℂ) :
    ‖scaledKernelDerivative K (((1:ℝ)/8)^j) g x-scaledKernelDerivative K (((1:ℝ)/8)^j) g y‖ ≤
      (H*kernelMomentTwo K)*4^j*dist x y := by
  simpa only [eighth_scale_lipschitz,dist_eq_norm] using scaledKernel_derivative_lipschitz
    hK hc (ε := ((1:ℝ)/8)^j) (by positivity) hg hH hHg x y

theorem dyadicKernel_hasFDerivAt {K : ℂ → ℂ} (hK : ContDiff ℝ ∞ K)
    (hc : HasCompactSupport K) {g : ℂ → E} (hg : Continuous g) {M H : ℝ}
    (hM : ∀ x, ‖g x‖ ≤ M) (hH : 0 ≤ H)
    (hHg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) (x : ℂ) :
    HasFDerivAt (dyadicKernelPotential K g) (dyadicKernelDerivative K g x) x := by
  apply hasFDerivAt_tsum (dyadic_summable.mul_left (H*kernelMomentOne K))
  · intro j x
    exact scaledKernel_hasFDerivAt hK hc (by positivity) hg x
  · exact dyadicKernel_derivative_bound hK hc hg hH hHg
  · exact dyadicKernel_value_summable hK.continuous hc hM (0:ℂ)

theorem dyadicKernel_derivative_holder {K : ℂ → ℂ} (hK : ContDiff ℝ ∞ K)
    (hc : HasCompactSupport K) {g : ℂ → E} (hg : Continuous g) {H : ℝ}
    (hH : 0 ≤ H) (hHg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) (x y : ℂ) :
    ‖dyadicKernelDerivative K g x-dyadicKernelDerivative K g y‖ ≤
      (H*(kernelMomentTwo K+8*kernelMomentOne K))*‖x-y‖^((1:ℝ)/3) := by
  have h := dyadicSeries_holder (fun j => scaledKernelDerivative K (((1:ℝ)/8)^j) g)
    (mul_nonneg hH (kernelMomentOne_nonneg K)) (mul_nonneg hH (kernelMomentTwo_nonneg K))
    (dyadicKernel_derivative_bound hK hc hg hH hHg)
    (dyadicKernel_derivative_lipschitz hK hc hg hH hHg) x y
  rw [dist_eq_norm] at h
  exact h.trans_eq (by ring)

lemma dyadicKernel_derivative_continuous {K : ℂ → ℂ} (hK : ContDiff ℝ ∞ K)
    (hc : HasCompactSupport K) {g : ℂ → E} (hg : Continuous g) {H : ℝ}
    (hH : 0 ≤ H) (hHg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) :
    Continuous (dyadicKernelDerivative K g) := by
  have hsc (j : ℕ) : Continuous (scaledKernelDerivative K (((1:ℝ)/8)^j) g) := by
    have hge : Continuous (fun z : ℂ => g ((((1:ℝ)/8)^j) • z)) := by fun_prop
    have hs := hc.contDiff_convolution_left (μ := volume) (ContinuousLinearMap.lsmul ℝ ℂ)
      hK hge.locallyIntegrable
    exact (hs.continuous_fderiv (by simp)).comp (by fun_prop)
  exact continuous_tsum hsc (dyadic_summable.mul_left (H*kernelMomentOne K))
    (dyadicKernel_derivative_bound hK hc hg hH hHg)

theorem dyadicKernel_contDiff_one {K : ℂ → ℂ} (hK : ContDiff ℝ ∞ K)
    (hc : HasCompactSupport K) {g : ℂ → E} (hg : Continuous g) {M H : ℝ}
    (hM : ∀ x, ‖g x‖ ≤ M) (hH : 0 ≤ H)
    (hHg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) :
    ContDiff ℝ 1 (dyadicKernelPotential K g) := by
  apply contDiff_one_iff_hasFDerivAt.mpr
  exact ⟨dyadicKernelDerivative K g,dyadicKernel_derivative_continuous hK hc hg hH hHg,
    dyadicKernel_hasFDerivAt hK hc hg hM hH hHg⟩

end

open scoped ContDiff Topology
open Set Filter MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

 
def physicalScaledKernel (K : ℂ → ℂ) (ε : ℝ) (w : ℂ) : ℂ :=
  ε⁻¹ • K (ε⁻¹ • w)

omit [CompleteSpace E] in
lemma scaledKernel_asConvolution (K : ℂ → ℂ) {ε : ℝ} (hε : 0 < ε)
    (g : ℂ → E) (x : ℂ) :
    scaledKernelPotential K ε g x =
      MeasureTheory.convolution (physicalScaledKernel K ε) g (ContinuousLinearMap.lsmul ℝ ℂ) volume x := by
  let f : ℂ → E := fun w => K w • g (x-ε • w)
  have hchange := Measure.integral_comp_inv_smul_of_nonneg volume f hε.le
  rw [Complex.finrank_real_complex] at hchange
  have hleft : scaledKernelPotential K ε g x = ε • ∫ w : ℂ, f w := by
    rw [scaledKernelPotential,MeasureTheory.convolution]
    congr 1
    apply integral_congr_ae
    apply Eventually.of_forall
    intro w
    simp only [f,ContinuousLinearMap.lsmul_apply,smul_sub,smul_smul,
      mul_inv_cancel₀ hε.ne',one_smul]
  have hright : MeasureTheory.convolution (physicalScaledKernel K ε) g (ContinuousLinearMap.lsmul ℝ ℂ) volume x =
      ε⁻¹ • ∫ w : ℂ, f (ε⁻¹ • w) := by
    rw [MeasureTheory.convolution,←integral_smul]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro w
    simp only [physicalScaledKernel,f,ContinuousLinearMap.lsmul_apply,smul_smul,
      mul_inv_cancel₀ hε.ne',one_smul,smul_assoc]
  rw [hleft,hright,hchange,smul_smul]
  congr 1
  field_simp

lemma physicalScaledKernel_integrable {K : ℂ → ℂ} (hK : Integrable K)
    {ε : ℝ} (hε : ε ≠ 0) : Integrable (physicalScaledKernel K ε) :=
  (hK.comp_smul (inv_ne_zero hε)).smul ε⁻¹

omit [CompleteSpace E] in
lemma scaledKernel_value_bound_integrable {K : ℂ → ℂ} (hK : Integrable K)
    {ε : ℝ} (hε : 0 ≤ ε) {g : ℂ → E}
    {M : ℝ} (hM : ∀ x, ‖g x‖ ≤ M) (x : ℂ) :
    ‖scaledKernelPotential K ε g x‖ ≤ ((∫ w : ℂ, ‖K w‖)*M)*ε := by
  rw [scaledKernelPotential,norm_smul,Real.norm_of_nonneg hε]
  have hb : ‖MeasureTheory.convolution K (fun z => g (ε • z)) (ContinuousLinearMap.lsmul ℝ ℂ) volume (ε⁻¹ • x)‖ ≤
      (∫ w : ℂ, ‖K w‖)*M := by
    have hin : ∀ w : ℂ, ‖K w • g (ε • (ε⁻¹ • x-w))‖ ≤ ‖K w‖*M := by
      intro w
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
    apply (norm_integral_le_of_norm_le (hK.norm.mul_const M)
      (Eventually.of_forall hin)).trans_eq
    exact integral_mul_const _ _
  exact (mul_le_mul_of_nonneg_left hb hε).trans_eq (by ring)

lemma locallyIntegrable_complex_inv_series : LocallyIntegrable (fun z : ℂ => z⁻¹) := by
  apply locallyIntegrable_of_norm_le_rpow (C := 1) (α := 1) (by simp) (by norm_num)
  · exact ae_of_all _ fun z => by simp only [norm_inv,Real.rpow_neg_one,one_mul,le_refl]
  · exact measurable_inv.aestronglyMeasurable

def cutoffCauchyKernel (b : ContDiffBump (0:ℂ)) (w : ℂ) : ℂ := b w • w⁻¹

lemma cutoffCauchyKernel_integrableNecessity (b : ContDiffBump (0:ℂ)) : Integrable (cutoffCauchyKernel b) := by
  have hi := locallyIntegrable_complex_inv_series.integrable_smul_left_of_hasCompactSupport
    b.continuous b.hasCompactSupport
  exact hi

lemma physicalScaled_cutoff (b : ContDiffBump (0:ℂ)) {ε : ℝ} (hε : ε ≠ 0) (w : ℂ) :
    physicalScaledKernel (cutoffCauchyKernel b) ε w = b (ε⁻¹ • w) • w⁻¹ := by
  change ε⁻¹ • (b (ε⁻¹ • w) • (ε⁻¹ • w)⁻¹) = _
  rw [smul_comm]
  congr 1
  simp [Complex.real_smul,mul_inv_rev,mul_left_comm,hε]

lemma physicalScaled_annular (b : ContDiffBump (0:ℂ)) (j : ℕ) (w : ℂ) :
    physicalScaledKernel (annularCauchyKernel b) (((1:ℝ)/8)^j) w =
      physicalScaledKernel (cutoffCauchyKernel b) (((1:ℝ)/8)^j) w-
      physicalScaledKernel (cutoffCauchyKernel b) (((1:ℝ)/8)^(j+1)) w := by
  rw [physicalScaled_cutoff b (by positivity),physicalScaled_cutoff b (by positivity),←sub_smul]
  change (((1:ℝ)/8)^j)⁻¹ •
    ((b ((((1:ℝ)/8)^j)⁻¹ • w)-b ((8:ℝ) • ((((1:ℝ)/8)^j)⁻¹ • w))) •
      ((((1:ℝ)/8)^j)⁻¹ • w)⁻¹) = _
  rw [smul_comm]
  have hh : (((1:ℝ)/8)^j)⁻¹ • (((((1:ℝ)/8)^j)⁻¹ • w)⁻¹) = w⁻¹ := by
    simp [Complex.real_smul,mul_inv_rev,mul_left_comm]
  rw [hh]
  congr 2
  rw [pow_succ,mul_inv_rev,smul_smul]
  norm_num

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_CauchyDuality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl )
open SymplecticBallPacking.Hamiltonian (Plane )
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset

open scoped ContDiff Topology
open Set Filter MeasureTheory
namespace HigherDimensionalBallPacking.Rigidity
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma annularPotential_difference (b : ContDiffBump (0:ℂ))
    {g : ℂ → E} (hg : Continuous g) {M : ℝ} (hM : ∀ x, ‖g x‖ ≤ M)
    (j : ℕ) (x : ℂ) :
    scaledKernelPotential (annularCauchyKernel b) (((1:ℝ)/8)^j) g x =
      scaledKernelPotential (cutoffCauchyKernel b) (((1:ℝ)/8)^j) g x-
      scaledKernelPotential (cutoffCauchyKernel b) (((1:ℝ)/8)^(j+1)) g x := by
  rw [scaledKernel_asConvolution _ (by positivity),
    scaledKernel_asConvolution _ (by positivity),scaledKernel_asConvolution _ (by positivity)]
  have hi (k : ℕ) : Integrable (fun w : ℂ =>
      physicalScaledKernel (cutoffCauchyKernel b) (((1:ℝ)/8)^k) w • g (x-w)) :=
    (physicalScaledKernel_integrable (cutoffCauchyKernel_integrableNecessity b) (by positivity)).smul_bdd M
      (hg.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (ae_of_all _ fun w => hM (x-w))
  simp only [MeasureTheory.convolution,ContinuousLinearMap.lsmul_apply,physicalScaled_annular,
    sub_smul]
  exact integral_sub (hi j) (hi (j+1))

omit [CompleteSpace E] in
lemma cutoffPotential_scale_zero (b : ContDiffBump (0:ℂ)) {g : ℂ → E}
    {M : ℝ} (hM : ∀ x, ‖g x‖ ≤ M) (x : ℂ) :
    Tendsto (fun j : ℕ => scaledKernelPotential (cutoffCauchyKernel b) (((1:ℝ)/8)^j) g x)
      atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun j => scaledKernel_value_bound_integrable
    (cutoffCauchyKernel_integrableNecessity b) (ε := ((1:ℝ)/8)^j) (by positivity) hM x)
  simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one
    (by norm_num : ‖(1:ℝ)/8‖ < 1)).const_mul ((∫ w : ℂ, ‖cutoffCauchyKernel b w‖)*M)

 
lemma dyadicKernel_cutoff_identity (b : ContDiffBump (0:ℂ)) {g : ℂ → E}
    (hg : Continuous g) {M : ℝ} (hM : ∀ x, ‖g x‖ ≤ M) :
    dyadicKernelPotential (annularCauchyKernel b) g =
      MeasureTheory.convolution (cutoffCauchyKernel b) g (ContinuousLinearMap.lsmul ℝ ℂ) volume := by
  funext x
  let v (j : ℕ) := scaledKernelPotential (cutoffCauchyKernel b) (((1:ℝ)/8)^j) g x
  have he (n : ℕ) : (∑ j ∈ Finset.range n,
      scaledKernelPotential (annularCauchyKernel b) (((1:ℝ)/8)^j) g x) = v 0-v n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ,ih,annularPotential_difference b hg hM n x]
      change v 0-v n+(v n-v (n+1))=v 0-v (n+1)
      abel
  have ht := (dyadicKernel_value_summable (annularCauchyKernel_smooth b).continuous
    (annularCauchyKernel_compactSupport b) hM x).hasSum.tendsto_sum_nat
  have ht' : Tendsto (fun n => v 0-v n) atTop (𝓝 (v 0)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub (cutoffPotential_scale_zero b hM x)
  have hu : dyadicKernelPotential (annularCauchyKernel b) g x = v 0 :=
    tendsto_nhds_unique ht (ht'.congr (fun n => (he n).symm))
  rw [hu]
  simp only [v,pow_zero,scaledKernelPotential,inv_one,one_smul]

 
theorem cutoffCauchy_contDiff_oneNecessity (b : ContDiffBump (0:ℂ)) {g : ℂ → E}
    (hg : Continuous g) {M H : ℝ} (hM : ∀ x, ‖g x‖ ≤ M) (hH : 0 ≤ H)
    (hHg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) :
    ContDiff ℝ 1 (MeasureTheory.convolution (cutoffCauchyKernel b) g
      (ContinuousLinearMap.lsmul ℝ ℂ) volume) := by
  rw [←dyadicKernel_cutoff_identity b hg hM]
  exact dyadicKernel_contDiff_one (annularCauchyKernel_smooth b)
    (annularCauchyKernel_compactSupport b) hg hM hH hHg

theorem cutoffCauchy_hasFDerivAtNecessity (b : ContDiffBump (0:ℂ)) {g : ℂ → E}
    (hg : Continuous g) {M H : ℝ} (hM : ∀ x, ‖g x‖ ≤ M) (hH : 0 ≤ H)
    (hHg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) (x : ℂ) :
    HasFDerivAt (MeasureTheory.convolution (cutoffCauchyKernel b) g
      (ContinuousLinearMap.lsmul ℝ ℂ) volume)
      (dyadicKernelDerivative (annularCauchyKernel b) g x) x := by
  rw [←dyadicKernel_cutoff_identity b hg hM]
  exact dyadicKernel_hasFDerivAt (annularCauchyKernel_smooth b)
    (annularCauchyKernel_compactSupport b) hg hM hH hHg x

theorem cutoffCauchy_fderiv_holder (b : ContDiffBump (0:ℂ)) {g : ℂ → E}
    (hg : Continuous g) {M H : ℝ} (hM : ∀ x, ‖g x‖ ≤ M) (hH : 0 ≤ H)
    (hHg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) (x y : ℂ) :
    ‖fderiv ℝ (MeasureTheory.convolution (cutoffCauchyKernel b) g
      (ContinuousLinearMap.lsmul ℝ ℂ) volume) x-
      fderiv ℝ (MeasureTheory.convolution (cutoffCauchyKernel b) g
      (ContinuousLinearMap.lsmul ℝ ℂ) volume) y‖ ≤
        H*(kernelMomentTwo (annularCauchyKernel b)+8*kernelMomentOne (annularCauchyKernel b))*
          ‖x-y‖^((1:ℝ)/3) := by
  rw [(cutoffCauchy_hasFDerivAtNecessity b hg hM hH hHg x).fderiv,
    (cutoffCauchy_hasFDerivAtNecessity b hg hM hH hHg y).fderiv]
  exact dyadicKernel_derivative_holder (annularCauchyKernel_smooth b)
    (annularCauchyKernel_compactSupport b) hg hH hHg x y

end

 

open scoped ContDiff Topology
open Set Function Filter MeasureTheory

open scoped ContDiff Topology
open Set Filter MeasureTheory
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
 theorem cutoff_cauchy_supported_eq (b : ContDiffBump (0:ℂ)) {R : ℝ}
    (hR : 2*R ≤ b.rIn) {g : ℂ → E} (hs : tsupport g ⊆ Metric.closedBall (0:ℂ) R)
    {x : ℂ} (hx : x ∈ Metric.closedBall (0:ℂ) R) :
    convolution (fun w => b w • w⁻¹) g (ContinuousLinearMap.lsmul ℝ ℂ) volume x =
      convolution (fun w : ℂ => w⁻¹) g (ContinuousLinearMap.lsmul ℝ ℂ) volume x := by
  apply integral_congr_ae
  apply Eventually.of_forall
  intro w
  change (b w • w⁻¹) • g (x-w)=w⁻¹ • g (x-w)
  by_cases hg : g (x-w)=0
  · rw [hg,smul_zero,smul_zero]
  have hw : x-w ∈ Metric.closedBall (0:ℂ) R := hs (subset_tsupport g (by exact hg))
  have hw' : w ∈ Metric.closedBall (0:ℂ) b.rIn := by
    rw [Metric.mem_closedBall,dist_zero_right]
    have hn : ‖w‖ ≤ ‖x‖+‖x-w‖ := by
      convert norm_sub_le x (x-w) using 1
      all_goals try with_reducible_and_instances rfl
      simp only [sub_sub_cancel]
    have hx' : ‖x‖ ≤ R := by simpa only [Metric.mem_closedBall,dist_zero_right] using hx
    have hw'' : ‖x-w‖ ≤ R := by simpa only [Metric.mem_closedBall,dist_zero_right] using hw
    linarith
  rw [b.one_of_mem_closedBall hw',one_smul]

end

open scoped ContDiff Topology
open Set Filter MeasureTheory
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma cauchyTransform_eventually_cutoff {g : ℂ → E} {S : ℝ}
    (hgs : tsupport g ⊆ Metric.closedBall (0:ℂ) S) (b : ContDiffBump (0:ℂ))
    (hb : 2*S ≤ b.rIn) {x : ℂ} (hx : ‖x‖ < S) :
    cauchyTransform g =ᶠ[𝓝 x] fun z => (Real.pi:ℂ)⁻¹ •
      MeasureTheory.convolution (cutoffCauchyKernel b) g (ContinuousLinearMap.lsmul ℝ ℂ) volume z := by
  filter_upwards [Metric.closedBall_mem_nhds_of_mem (show x ∈ Metric.ball (0:ℂ) S by
    simpa only [Metric.mem_ball,dist_zero_right] using hx)] with z hz
  exact congrArg ((Real.pi:ℂ)⁻¹ • ·) (cutoff_cauchy_supported_eq b hb hgs hz).symm

 
theorem cauchyTransform_holder_contDiff_oneNecessity {g : ℂ → E} (hg : Continuous g)
    (hc : HasCompactSupport g) {M H : ℝ} (hM : ∀ x, ‖g x‖ ≤ M) (hH : 0 ≤ H)
    (hHg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) :
    ContDiff ℝ 1 (cauchyTransform g) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  obtain ⟨R,hR⟩ := hc.isBounded.subset_closedBall (0:ℂ)
  let S : ℝ := max R 0+‖x‖+1
  have hRS : R ≤ S := by dsimp [S]; linarith [le_max_left R 0,norm_nonneg x]
  have hS : 0 < S := by dsimp [S]; linarith [le_max_right R 0,norm_nonneg x]
  have hxS : ‖x‖ < S := by dsimp [S]; linarith [le_max_right R 0]
  let b : ContDiffBump (0:ℂ) := ⟨2*S,2*S+1,by positivity,by linarith⟩
  have hgs : tsupport g ⊆ Metric.closedBall (0:ℂ) S :=
    hR.trans (Metric.closedBall_subset_closedBall hRS)
  exact ((cutoffCauchy_contDiff_oneNecessity b hg hM hH hHg).const_smul (Real.pi:ℂ)⁻¹).contDiffAt
    |>.congr_of_eventuallyEq (cauchyTransform_eventually_cutoff hgs b (le_refl _) hxS)

 
theorem cauchyTransform_fderiv_holder_on (S : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : ℂ → E), Continuous g →
      tsupport g ⊆ Metric.closedBall (0:ℂ) S → ∀ M H : ℝ,
      (∀ x, ‖g x‖ ≤ M) → 0 ≤ H →
      (∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) →
      ∀ x ∈ Metric.closedBall (0:ℂ) S, ∀ y ∈ Metric.closedBall (0:ℂ) S,
      ‖fderiv ℝ (cauchyTransform g) x-fderiv ℝ (cauchyTransform g) y‖ ≤
        C*H*‖x-y‖^((1:ℝ)/3) := by
  let T : ℝ := max S 0+1
  have hST : S < T := by dsimp [T]; linarith [le_max_left S 0]
  have hT : 0 < T := by dsimp [T]; linarith [le_max_right S 0]
  let b : ContDiffBump (0:ℂ) := ⟨2*T,2*T+1,by positivity,by linarith⟩
  let C : ℝ := Real.pi⁻¹*(kernelMomentTwo (annularCauchyKernel b)+
    8*kernelMomentOne (annularCauchyKernel b))
  have hC : 0 ≤ C := mul_nonneg (inv_nonneg.mpr Real.pi_pos.le)
    (add_nonneg (kernelMomentTwo_nonneg _) (mul_nonneg (by norm_num) (kernelMomentOne_nonneg _)))
  refine ⟨C,hC,?_⟩
  intro g hg hgs M H hM hH hHg x hx y hy
  have hgs' : tsupport g ⊆ Metric.closedBall (0:ℂ) T :=
    hgs.trans (Metric.closedBall_subset_closedBall hST.le)
  have hd (z : ℂ) (hz : z ∈ Metric.closedBall (0:ℂ) S) :
      fderiv ℝ (cauchyTransform g) z = (Real.pi:ℂ)⁻¹ •
        fderiv ℝ (MeasureTheory.convolution (cutoffCauchyKernel b) g
          (ContinuousLinearMap.lsmul ℝ ℂ) volume) z := by
    have hzS : ‖z‖ ≤ S := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz
    have hzT : ‖z‖ < T := hzS.trans_lt hST
    have hder := ((cutoffCauchy_contDiff_oneNecessity b hg hM hH hHg).differentiable (by simp) z).hasFDerivAt
    exact ((hder.const_smul (Real.pi:ℂ)⁻¹).congr_of_eventuallyEq
      (cauchyTransform_eventually_cutoff hgs' b (le_refl _) hzT)).fderiv
  rw [hd x hx,hd y hy,←smul_sub,norm_smul,norm_inv,Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le]
  exact (mul_le_mul_of_nonneg_left (cutoffCauchy_fderiv_holder b hg hM hH hHg x y)
    (inv_nonneg.mpr Real.pi_pos.le)).trans_eq (by dsimp [C]; ring)

end

open scoped ContDiff Topology
open Set Filter MeasureTheory
section

lemma compactKernel_convolution_tendsto_bounded
    {A E F : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (L : A →L[ℝ] E →L[ℝ] F) {K : ℂ → A} (hK : Continuous K) (hc : HasCompactSupport K)
    {g : ℕ → ℂ → E} (hg : ∀ j, Continuous (g j)) {v : ℂ → E}
    (hv : ∀ w, Tendsto (fun j => g j w) atTop (𝓝 (v w)))
    {M : ℝ} (hM : ∀ j w, ‖g j w‖ ≤ M) (x : ℂ) :
    Tendsto (fun j => MeasureTheory.convolution K (g j) L volume x) atTop
      (𝓝 (MeasureTheory.convolution K v L volume x)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun w : ℂ => ‖L‖*‖K w‖*M)
  · apply Eventually.of_forall
    intro j
    exact ((L.continuous.comp hK).clm_apply
      ((hg j).comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · apply Eventually.of_forall
    intro j
    apply ae_of_all
    intro w
    exact (L.le_opNorm₂ (K w) (g j (x-w))).trans
      (mul_le_mul_of_nonneg_left (hM j (x-w)) (mul_nonneg (ContinuousLinearMap.opNorm_nonneg L) (norm_nonneg (K w))))
  · exact ((hK.integrable_of_hasCompactSupport hc).norm.const_mul ‖L‖).mul_const M
  · apply ae_of_all
    intro w
    exact ((L (K w)).continuous.tendsto _).comp (hv (x-w))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

lemma scaledKernelDerivative_tendsto {K : ℂ → ℂ} (hK : ContDiff ℝ ∞ K)
    (hc : HasCompactSupport K) {g : ℕ → ℂ → E} (hg : ∀ j, Continuous (g j))
    {v : ℂ → E} (hv : Continuous v)
    (hgv : ∀ w, Tendsto (fun j => g j w) atTop (𝓝 (v w)))
    {M : ℝ} (hM : ∀ j w, ‖g j w‖ ≤ M) (ε : ℝ) (x : ℂ) :
    Tendsto (fun j => scaledKernelDerivative K ε (g j) x) atTop
      (𝓝 (scaledKernelDerivative K ε v x)) := by
  have he {f : ℂ → E} (hf : Continuous f) : scaledKernelDerivative K ε f x =
      MeasureTheory.convolution (fderiv ℝ K) (fun w => f (ε • w))
        ((ContinuousLinearMap.lsmul ℝ ℂ).precompL ℂ) volume (ε⁻¹ • x) := by
    have hfe : Continuous (fun w : ℂ => f (ε • w)) := by fun_prop
    exact (hc.hasFDerivAt_convolution_left (μ := volume) (ContinuousLinearMap.lsmul ℝ ℂ)
      (hK.of_le (by simp)) hfe.locallyIntegrable (ε⁻¹ • x)).fderiv
  simp_rw [he hv,he (hg _)]
  exact compactKernel_convolution_tendsto_bounded ((ContinuousLinearMap.lsmul ℝ ℂ).precompL ℂ)
    (hK.continuous_fderiv (by simp)) (hc.fderiv ℝ) (fun j => by fun_prop)
    (fun w => hgv (ε • w)) (fun j w => hM j (ε • w)) (ε⁻¹ • x)

lemma dyadicKernelDerivative_tendsto {K : ℂ → ℂ} (hK : ContDiff ℝ ∞ K)
    (hc : HasCompactSupport K) {g : ℕ → ℂ → E} (hg : ∀ j, Continuous (g j))
    {v : ℂ → E} (hv : Continuous v)
    (hgv : ∀ w, Tendsto (fun j => g j w) atTop (𝓝 (v w)))
    {M H : ℝ} (hM : ∀ j w, ‖g j w‖ ≤ M) (hH : 0 ≤ H)
    (hHg : ∀ j x y, ‖g j x-g j y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) (x : ℂ) :
    Tendsto (fun j => dyadicKernelDerivative K (g j) x) atTop (𝓝 (dyadicKernelDerivative K v x)) := by
  apply tendsto_tsum_of_dominated_convergence (dyadic_summable.mul_left (H*kernelMomentOne K))
  · intro k
    exact scaledKernelDerivative_tendsto hK hc hg hv hgv hM _ x
  · apply Eventually.of_forall
    intro j k
    exact dyadicKernel_derivative_bound hK hc (hg j) hH (hHg j) k x

lemma cutoffCauchy_fderiv_tendsto (b : ContDiffBump (0:ℂ))
    {g : ℕ → ℂ → E} (hg : ∀ j, Continuous (g j)) {v : ℂ → E} (hv : Continuous v)
    (hgv : ∀ w, Tendsto (fun j => g j w) atTop (𝓝 (v w)))
    {M H : ℝ} (hM : ∀ j w, ‖g j w‖ ≤ M) (hMv : ∀ w, ‖v w‖ ≤ M) (hH : 0 ≤ H)
    (hHg : ∀ j x y, ‖g j x-g j y‖ ≤ H*‖x-y‖^((1:ℝ)/3))
    (hHv : ∀ x y, ‖v x-v y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) (x : ℂ) :
    Tendsto (fun j => fderiv ℝ (MeasureTheory.convolution (cutoffCauchyKernel b) (g j)
      (ContinuousLinearMap.lsmul ℝ ℂ) volume) x) atTop
      (𝓝 (fderiv ℝ (MeasureTheory.convolution (cutoffCauchyKernel b) v
        (ContinuousLinearMap.lsmul ℝ ℂ) volume) x)) := by
  simp_rw [(cutoffCauchy_hasFDerivAtNecessity b hv hMv hH hHv x).fderiv,
    (cutoffCauchy_hasFDerivAtNecessity b (hg _) (hM _) hH (hHg _) x).fderiv]
  exact dyadicKernelDerivative_tendsto (annularCauchyKernel_smooth b)
    (annularCauchyKernel_compactSupport b) hg hv hgv hM hH hHg x

 

theorem cauchyTransform_fderiv_tendsto {g : ℕ → ℂ → E} (hg : ∀ j, Continuous (g j))
    {v : ℂ → E} (hv : Continuous v)
    (hgv : ∀ w, Tendsto (fun j => g j w) atTop (𝓝 (v w))) {R : ℝ}
    (hgs : ∀ j, tsupport (g j) ⊆ Metric.closedBall (0:ℂ) R)
    (hvs : tsupport v ⊆ Metric.closedBall (0:ℂ) R)
    {M H : ℝ} (hM : ∀ j w, ‖g j w‖ ≤ M) (hMv : ∀ w, ‖v w‖ ≤ M) (hH : 0 ≤ H)
    (hHg : ∀ j x y, ‖g j x-g j y‖ ≤ H*‖x-y‖^((1:ℝ)/3))
    (hHv : ∀ x y, ‖v x-v y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) (x : ℂ) :
    Tendsto (fun j => fderiv ℝ (cauchyTransform (g j)) x) atTop
      (𝓝 (fderiv ℝ (cauchyTransform v) x)) := by
  let S : ℝ := max R 0+‖x‖+1
  have hRS : R ≤ S := by dsimp [S]; linarith [le_max_left R 0,norm_nonneg x]
  have hS : 0 < S := by dsimp [S]; linarith [le_max_right R 0,norm_nonneg x]
  have hxS : ‖x‖ < S := by dsimp [S]; linarith [le_max_right R 0]
  let b : ContDiffBump (0:ℂ) := ⟨2*S,2*S+1,by positivity,by linarith⟩
  have he {f : ℂ → E} (hf : Continuous f)
      (hs : tsupport f ⊆ Metric.closedBall (0:ℂ) R) (hm : ∀ z, ‖f z‖ ≤ M)
      (hh : ∀ z w, ‖f z-f w‖ ≤ H*‖z-w‖^((1:ℝ)/3)) :
      fderiv ℝ (cauchyTransform f) x = (Real.pi:ℂ)⁻¹ •
        fderiv ℝ (MeasureTheory.convolution (cutoffCauchyKernel b) f
          (ContinuousLinearMap.lsmul ℝ ℂ) volume) x := by
    have hder := ((cutoffCauchy_contDiff_oneNecessity b hf hm hH hh).differentiable (by simp) x).hasFDerivAt
    exact ((hder.const_smul (Real.pi:ℂ)⁻¹).congr_of_eventuallyEq
      (cauchyTransform_eventually_cutoff (hs.trans (Metric.closedBall_subset_closedBall hRS))
        b (le_refl _) hxS)).fderiv
  simp_rw [he hv hvs hMv hHv,he (hg _) (hgs _) (hM _) (hHg _)]
  exact (cutoffCauchy_fderiv_tendsto b hg hv hgv hM hMv hH hHg hHv x).const_smul (Real.pi:ℂ)⁻¹

end

 

open scoped ContDiff Topology
open Set Filter MeasureTheory
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def holderMollify (b : ContDiffBump (0:ℂ)) (g : ℂ → E) : ℂ → E :=
  MeasureTheory.convolution (b.normed volume) g (ContinuousLinearMap.lsmul ℝ ℝ) volume

omit [CompleteSpace E] in
lemma holderMollify_smooth (b : ContDiffBump (0:ℂ)) {g : ℂ → E} (hg : Continuous g) :
    ContDiff ℝ ∞ (holderMollify b g) :=
  b.hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    b.contDiff_normed hg.locallyIntegrable

omit [CompleteSpace E] in
lemma holderMollify_bound (b : ContDiffBump (0:ℂ)) {g : ℂ → E} {M : ℝ}
    (hM : ∀ x, ‖g x‖ ≤ M) (x : ℂ) : ‖holderMollify b g x‖ ≤ M := by
  change ‖∫ w : ℂ, b.normed volume w • g (x-w)‖ ≤ M
  have hb : ∀ w : ℂ, ‖b.normed volume w • g (x-w)‖ ≤ b.normed volume w*M := by
    intro w
    rw [norm_smul,Real.norm_of_nonneg (b.nonneg_normed w)]
    exact mul_le_mul_of_nonneg_left (hM _) (b.nonneg_normed w)
  exact (norm_integral_le_of_norm_le (b.integrable_normed.mul_const M) (ae_of_all _ hb)).trans_eq
    (by rw [integral_mul_const,b.integral_normed,one_mul])

omit [CompleteSpace E] in
lemma holderMollify_holder (b : ContDiffBump (0:ℂ)) {g : ℂ → E} (hg : Continuous g)
    {M H : ℝ} (hM : ∀ x, ‖g x‖ ≤ M)
    (hHg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) (x y : ℂ) :
    ‖holderMollify b g x-holderMollify b g y‖ ≤ H*‖x-y‖^((1:ℝ)/3) := by
  have hi (z : ℂ) : Integrable (fun w : ℂ => b.normed volume w • g (z-w)) :=
    b.integrable_normed.smul_bdd M (hg.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (ae_of_all _ fun w => hM _)
  change ‖(∫ w : ℂ, b.normed volume w • g (x-w))-
    (∫ w : ℂ, b.normed volume w • g (y-w))‖ ≤ _
  rw [←integral_sub (hi x) (hi y)]
  have hb : ∀ w : ℂ, ‖b.normed volume w • g (x-w)-b.normed volume w • g (y-w)‖ ≤
      b.normed volume w*(H*‖x-y‖^((1:ℝ)/3)) := by
    intro w
    rw [←smul_sub,norm_smul,Real.norm_of_nonneg (b.nonneg_normed w)]
    exact mul_le_mul_of_nonneg_left (by simpa only [sub_sub_sub_cancel_right] using hHg (x-w) (y-w))
      (b.nonneg_normed w)
  exact (norm_integral_le_of_norm_le
    (b.integrable_normed.mul_const (H*‖x-y‖^((1:ℝ)/3))) (ae_of_all _ hb)).trans_eq
      (by rw [integral_mul_const,b.integral_normed,one_mul])

omit [CompleteSpace E] in
lemma holderMollify_support (b : ContDiffBump (0:ℂ)) {g : ℂ → E} {R : ℝ}
    (hgs : tsupport g ⊆ Metric.closedBall (0:ℂ) R) :
    tsupport (holderMollify b g) ⊆ Metric.closedBall (0:ℂ) (b.rOut+R) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  have hs := MeasureTheory.support_convolution_subset (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (μ := volume) (f := b.normed volume) (g := g) hx
  obtain ⟨w,hw,z,hz,rfl⟩ := hs
  have hw' : ‖w‖ ≤ b.rOut := by
    have hh := subset_tsupport (b.normed volume) hw
    rw [b.tsupport_normed_eq] at hh
    simpa only [Metric.mem_closedBall,dist_zero_right] using hh
  have hz' : ‖z‖ ≤ R := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using hgs (subset_tsupport g hz)
  simpa only [Metric.mem_closedBall,dist_zero_right] using
    (norm_add_le w z).trans (add_le_add hw' hz')

omit [CompleteSpace E] in
lemma holderMollify_compactSupport (b : ContDiffBump (0:ℂ)) {g : ℂ → E}
    (hc : HasCompactSupport g) : HasCompactSupport (holderMollify b g) :=
  b.hasCompactSupport_normed.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hc

def shrinkingHolderBump (j : ℕ) : ContDiffBump (0:ℂ) :=
  ⟨(((1:ℝ)/2)^j)/2,((1:ℝ)/2)^j,by positivity,by
    have h : 0 < ((1:ℝ)/2)^j := by positivity
    linarith⟩

lemma shrinkingHolderBump_radius_le (j : ℕ) : (shrinkingHolderBump j).rOut ≤ 1 := by
  exact pow_le_one₀ (by norm_num) (by norm_num)

lemma holderMollify_tendsto {g : ℂ → E} (hg : Continuous g) (x : ℂ) :
    Tendsto (fun j : ℕ => holderMollify (shrinkingHolderBump j) g x) atTop (𝓝 (g x)) :=
  ContDiffBump.convolution_tendsto_right_of_continuous
    (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num : ‖(1:ℝ)/2‖ < 1)) hg x

end

open scoped ContDiff Topology Classical
open Set Function Filter MeasureTheory

 
 

 

open scoped ContDiff Topology
open Set Function MeasureTheory

open scoped ContDiff Topology
open Set Function Filter MeasureTheory

 

 

open scoped ContDiff Topology
open Set Function Filter MeasureTheory

 

 

open scoped ContDiff Topology
open Set Function Filter MeasureTheory

 

 

open scoped ContDiff Topology
open Set Function Filter MeasureTheory

 

 

open scoped ContDiff Topology
open Set Function Filter MeasureTheory

 

 

open scoped ContDiff Topology
open Set Function Filter MeasureTheory

 theorem cauchyCurl_subLeft {g : ℂ → ℂ} (hg : ContDiff ℝ ∞ g) (z w : ℂ) :
    cauchyCurl (fun v => g (z-v)) w = -cauchyCurl g (z-w) := by
  have hd := ((hg.differentiable (by simp) (z-w)).hasFDerivAt).comp w
    ((hasFDerivAt_const z w).sub (hasFDerivAt_id w))
  change HasFDerivAt (fun v => g (z-v)) _ w at hd
  simp [cauchyCurl,hd.fderiv]
  ring

 theorem cauchy_integral_curl_translate {g : ℂ → ℂ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (z : ℂ) :
    (∫ w : ℂ, w⁻¹ * cauchyCurl g (z-w)) = (2*Real.pi*Complex.I)*g z := by
  have hs : ContDiff ℝ ∞ (fun w => g (z-w)) := hg.comp (contDiff_const.sub contDiff_id)
  have hsc : HasCompactSupport (fun w => g (z-w)) :=
    hc.comp_homeomorph (Homeomorph.subLeft z)
  have hh := cauchy_green_fundamental hs hsc
  simp_rw [cauchyCurl_subLeft hg,neg_div,div_eq_mul_inv,mul_comm (cauchyCurl g (z-_)),
    integral_neg,sub_zero] at hh
  linear_combination -hh

 theorem cauchyTransform_curl {g : ℂ → ℂ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (z : ℂ) :
    cauchyCurl (cauchyTransform g) z = (2*Complex.I)*g z := by
  have hd := cauchyTransform_hasFDerivAt hc hg z
  have hD : Continuous (fderiv ℝ g) := (hg.fderiv_right (m := ∞) (by simp)).continuous
  have hi (v : ℂ) : Integrable (fun w : ℂ => w⁻¹ * fderiv ℝ g (z-w) v) := by
    exact (hc.fderiv_apply (𝕜 := ℝ) v).convolutionExists_right
      (ContinuousLinearMap.lsmul ℝ ℂ) locallyIntegrable_complex_inv
        ((ContinuousLinearMap.apply ℝ ℂ v).continuous.comp hD) z
  rw [cauchyCurl,hd.fderiv]
  simp only [smul_apply,smul_eq_mul]
  rw [convolution_precompR_apply (L := ContinuousLinearMap.lsmul ℝ ℂ)
      locallyIntegrable_complex_inv (hc.fderiv (𝕜 := ℝ)) hD,
    convolution_precompR_apply (L := ContinuousLinearMap.lsmul ℝ ℂ)
      locallyIntegrable_complex_inv (hc.fderiv (𝕜 := ℝ)) hD]
  change Complex.I*((Real.pi:ℂ)⁻¹ * ∫ w : ℂ, w⁻¹ * fderiv ℝ g (z-w) 1) -
      (Real.pi:ℂ)⁻¹ * (∫ w : ℂ, w⁻¹ * fderiv ℝ g (z-w) Complex.I) = _
  calc
    _ = (Real.pi:ℂ)⁻¹ * (∫ w : ℂ, w⁻¹ * cauchyCurl g (z-w)) := by
      rw [show (fun w : ℂ => w⁻¹*cauchyCurl g (z-w)) =
        (fun w => Complex.I*(w⁻¹*fderiv ℝ g (z-w) 1) - w⁻¹*fderiv ℝ g (z-w) Complex.I) from
        funext (fun w => by dsimp only [cauchyCurl]; ring)]
      rw [integral_sub ((hi 1).const_mul _) (hi Complex.I),integral_const_mul]
      ring
    _ = _ := by
      rw [cauchy_integral_curl_translate hg hc]
      field_simp [Real.pi_ne_zero]


open scoped ContDiff Topology
open Set Function Filter MeasureTheory

 

theorem cauchyTransform_holder_curlNecessity {g : ℂ → ℂ} (hg : Continuous g)
    (hc : HasCompactSupport g) {M H : ℝ} (hM : ∀ x, ‖g x‖ ≤ M) (hH : 0 ≤ H)
    (hHg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) (x : ℂ) :
    cauchyCurl (cauchyTransform g) x = (2*Complex.I)*g x := by
  obtain ⟨R,hR⟩ := hc.isBounded.subset_closedBall (0:ℂ)
  let u (j : ℕ) := holderMollify (shrinkingHolderBump j) g
  have hus (j : ℕ) : ContDiff ℝ ∞ (u j) := holderMollify_smooth _ hg
  have huc (j : ℕ) : HasCompactSupport (u j) := holderMollify_compactSupport _ hc
  have huM (j : ℕ) (w : ℂ) : ‖u j w‖ ≤ M := holderMollify_bound _ hM w
  have huH (j : ℕ) (w z : ℂ) : ‖u j w-u j z‖ ≤ H*‖w-z‖^((1:ℝ)/3) :=
    holderMollify_holder _ hg hM hHg w z
  have huR (j : ℕ) : tsupport (u j) ⊆ Metric.closedBall (0:ℂ) (R+1) :=
    (holderMollify_support _ hR).trans (Metric.closedBall_subset_closedBall (by
      linarith [shrinkingHolderBump_radius_le j]))
  have hgR : tsupport g ⊆ Metric.closedBall (0:ℂ) (R+1) :=
    hR.trans (Metric.closedBall_subset_closedBall (by linarith))
  have hd := cauchyTransform_fderiv_tendsto (fun j => (hus j).continuous) hg
    (holderMollify_tendsto hg) huR hgR huM hM hH huH hHg x
  have hde (z : ℂ) := ((ContinuousLinearMap.apply ℝ ℂ z).continuous.tendsto _).comp hd
  have hl : Tendsto (fun j => cauchyCurl (cauchyTransform (u j)) x) atTop
      (𝓝 (cauchyCurl (cauchyTransform g) x)) :=
    ((hde 1).const_mul Complex.I).sub (hde Complex.I)
  have he : (fun j => cauchyCurl (cauchyTransform (u j)) x) =
      (fun j => (2*Complex.I)*u j x) := funext fun j => cauchyTransform_curl (hus j) (huc j) x
  rw [he] at hl
  exact tendsto_nhds_unique hl ((holderMollify_tendsto hg x).const_mul (2*Complex.I))


 

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
 def complexCauchyCurl (g : ℂ → E) (z : ℂ) : E :=
  Complex.I • fderiv ℝ g z 1 - fderiv ℝ g z Complex.I

 theorem complexCauchyCurl_dual {g : ℂ → E} (hg : Differentiable ℝ g)
    (l : E →L[ℂ] ℂ) (z : ℂ) :
    l (complexCauchyCurl g z) = cauchyCurl (fun w => l (g w)) z := by
  have hd := (l.restrictScalars ℝ).hasFDerivAt.comp z (hg z).hasFDerivAt
  change HasFDerivAt (fun w => l (g w)) _ z at hd
  simp only [complexCauchyCurl,map_sub,map_smul,cauchyCurl,hd.fderiv]
  rfl

 theorem cauchyTransform_dual [CompleteSpace E] {g : ℂ → E} (hg : Continuous g)
    (hc : HasCompactSupport g) (l : E →L[ℂ] ℂ) (z : ℂ) :
    l (cauchyTransform g z) = cauchyTransform (fun w => l (g w)) z := by
  have hi := hc.convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℂ)
    locallyIntegrable_complex_inv hg z
  have hi' : Integrable (fun w : ℂ => w⁻¹ • g (z-w)) := hi
  simp only [cauchyTransform_apply,map_smul]
  congr 1
  simpa only [map_smul] using (l.integral_comp_comm hi').symm

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_HolderCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped Manifold
open MeasureTheory
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl )
open SymplecticBallPacking.Hamiltonian (Plane )
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open MeasureTheory
open scoped Topology
open Finset
open scoped ContDiff Classical

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Filter
open Function MeasureTheory
open scoped BoundedContinuousFunction
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem cauchyTransform_holder_complexCurl {g : ℂ → E} (hg : Continuous g)
    (hc : HasCompactSupport g) {M H : ℝ} (hM : ∀ x, ‖g x‖ ≤ M) (hH : 0 ≤ H)
    (hHg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) (x : ℂ) :
    complexCauchyCurl (cauchyTransform g) x = (2*Complex.I) • g x := by
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
  intro l
  rw [complexCauchyCurl_dual
    ((cauchyTransform_holder_contDiff_oneNecessity hg hc hM hH hHg).differentiable (by simp))]
  have he : (fun w => l (cauchyTransform g w)) = cauchyTransform (fun w => l (g w)) :=
    funext (cauchyTransform_dual hg hc l)
  rw [he]
  have hMl (w : ℂ) : ‖l (g w)‖ ≤ ‖l‖*M :=
    (l.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hM w) (norm_nonneg _))
  have hHl (w z : ℂ) : ‖l (g w)-l (g z)‖ ≤ (‖l‖*H)*‖w-z‖^((1:ℝ)/3) := by
    rw [←map_sub]
    exact (l.le_opNorm _).trans ((mul_le_mul_of_nonneg_left (hHg w z) (norm_nonneg _)).trans_eq
      (mul_assoc _ _ _).symm)
  have hh := cauchyTransform_holder_curlNecessity (g := fun w => l (g w))
    (l.continuous.comp hg) (hc.comp_left l.map_zero)
    hMl (mul_nonneg (norm_nonneg _) hH) hHl x
  simpa only [map_smul,smul_eq_mul] using hh

lemma closedBall_subset_exterior {R r : ℝ} {x : ℂ} (hx : R+r < ‖x‖) :
    Metric.closedBall x r ⊆ {z : ℂ | R < ‖z‖} := by
  intro z hz
  have hh : ‖x‖ ≤ ‖z‖ + r := by
    have ht := norm_sub_le x z
    have hz' : ‖x-z‖ ≤ r := by
      simpa only [Metric.mem_closedBall,dist_eq_norm,norm_sub_rev] using hz
    linarith [norm_le_insert' x z]
  change R < ‖z‖
  linarith

omit [CompleteSpace E] in
lemma holomorphic_exterior_deriv_bound {f : ℂ → E} {R M : ℝ}
    (hd : DifferentiableOn ℂ f {z : ℂ | R < ‖z‖})
    (hM : ∀ z, ‖f z‖ ≤ M) {x : ℂ} (hx : R+1 < ‖x‖) :
    ‖deriv f x‖ ≤ M := by
  simpa only [div_one] using Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by norm_num : (0:ℝ)<1) (hd.diffContOnCl_ball (closedBall_subset_exterior hx))
    (fun z _ => hM z)

lemma holomorphic_exterior_secondDeriv_bound {f : ℂ → E} {R M : ℝ}
    (hd : DifferentiableOn ℂ f {z : ℂ | R < ‖z‖})
    (hM : ∀ z, ‖f z‖ ≤ M) {x : ℂ} (hx : R+1 < ‖x‖) :
    ‖deriv (deriv f) x‖ ≤ 2*M := by
  simpa [iteratedDeriv_succ] using Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    2 (by norm_num : (0:ℝ)<1)
    (hd.diffContOnCl_ball (closedBall_subset_exterior hx)) (fun z _ => hM z)

omit [CompleteSpace E] in
lemma real_fderiv_eq_complex_deriv {f : ℂ → E} {x : ℂ}
    (hx : DifferentiableAt ℂ f x) :
    fderiv ℝ f x = ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv f x)).restrictScalars ℝ) :=
  (hx.hasDerivAt.hasFDerivAt.restrictScalars ℝ).fderiv

omit [CompleteSpace E] in
lemma real_fderiv_norm_eq_deriv {f : ℂ → E} {x : ℂ} (hx : DifferentiableAt ℂ f x) :
    ‖fderiv ℝ f x‖ = ‖deriv f x‖ := by
  rw [hx.fderiv_restrictScalars ℝ,ContinuousLinearMap.norm_restrictScalars,
    ←norm_deriv_eq_norm_fderiv]

omit [CompleteSpace E] in
lemma real_fderiv_sub_norm_eq_deriv {f : ℂ → E} {x y : ℂ}
    (hx : DifferentiableAt ℂ f x) (hy : DifferentiableAt ℂ f y) :
    ‖fderiv ℝ f x-fderiv ℝ f y‖ = ‖deriv f x-deriv f y‖ := by
  rw [real_fderiv_eq_complex_deriv hx,real_fderiv_eq_complex_deriv hy,
    ←ContinuousLinearMap.restrictScalars_sub,ContinuousLinearMap.norm_restrictScalars]
  have he : ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv f x) -
      ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv f y) =
      ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv f x-deriv f y) := by
    ext
    simp only [sub_apply,ContinuousLinearMap.smulRight_apply,smul_sub]
  rw [he]
  simp

lemma holomorphic_exterior_fderiv_lipschitz_near {f : ℂ → E} {R M : ℝ}
    (hd : DifferentiableOn ℂ f {z : ℂ | R < ‖z‖})
    (hM : ∀ z, ‖f z‖ ≤ M) {x y : ℂ} (hx : R+2 < ‖x‖)
    (hxy : ‖x-y‖ ≤ 1) :
    ‖fderiv ℝ f x-fderiv ℝ f y‖ ≤ (2*M)*‖x-y‖ := by
  have ho : IsOpen {z : ℂ | R < ‖z‖} := isOpen_lt continuous_const continuous_norm
  have hb : Metric.closedBall x 1 ⊆ {z : ℂ | R+1 < ‖z‖} :=
    closedBall_subset_exterior (by linarith)
  have hbx : x ∈ Metric.closedBall x 1 := Metric.mem_closedBall_self (by norm_num)
  have hby : y ∈ Metric.closedBall x 1 := by
    simpa only [Metric.mem_closedBall,dist_eq_norm,norm_sub_rev] using hxy
  have ha (z : ℂ) (hz : z ∈ Metric.closedBall x 1) : DifferentiableAt ℂ f z :=
    hd.differentiableAt (ho.mem_nhds (by have hh : R+1 < ‖z‖ := hb hz; change R < ‖z‖; linarith))
  rw [real_fderiv_sub_norm_eq_deriv (ha x hbx) (ha y hby)]
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z hz => (hd.deriv ho).differentiableAt
      (ho.mem_nhds (by have hh : R+1 < ‖z‖ := hb hz; change R < ‖z‖; linarith)))
    (fun z hz => holomorphic_exterior_secondDeriv_bound hd hM (hb hz))
    (convex_closedBall x (1:ℝ)) hby hbx
  exact h

theorem global_holder_fderiv_of_holomorphic_exterior {f : ℂ → E} {R M : ℝ}
    (hf : ContDiff ℝ 1 f) (hd : DifferentiableOn ℂ f {z : ℂ | R < ‖z‖})
    (hM : ∀ z, ‖f z‖ ≤ M)
    (hlocal : ∀ S : ℝ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Metric.closedBall (0:ℂ) S, ∀ y ∈ Metric.closedBall (0:ℂ) S,
      ‖fderiv ℝ f x-fderiv ℝ f y‖ ≤ C*‖x-y‖^((1:ℝ)/3)) :
    ∃ B K : ℝ, 0 ≤ B ∧ 0 ≤ K ∧ (∀ x, ‖fderiv ℝ f x‖ ≤ B) ∧
      ∀ x y, ‖fderiv ℝ f x-fderiv ℝ f y‖ ≤ K*‖x-y‖^((1:ℝ)/3) := by
  have hM0 : 0 ≤ M := (norm_nonneg (f 0)).trans (hM 0)
  have ho : IsOpen {z : ℂ | R < ‖z‖} := isOpen_lt continuous_const continuous_norm
  have hDf : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  obtain ⟨D,hD⟩ := (isCompact_closedBall (0:ℂ) (R+1)).exists_bound_of_continuousOn hDf.continuousOn
  let B := max D M
  have hB0 : 0 ≤ B := hM0.trans (le_max_right _ _)
  have hB (x : ℂ) : ‖fderiv ℝ f x‖ ≤ B := by
    by_cases hx : ‖x‖ ≤ R+1
    · exact (hD x (by simpa only [Metric.mem_closedBall,dist_zero_right] using hx)).trans
        (le_max_left _ _)
    · have hx' : R+1 < ‖x‖ := lt_of_not_ge hx
      rw [real_fderiv_norm_eq_deriv (hd.differentiableAt
        (ho.mem_nhds (show R < ‖x‖ by linarith)))]
      exact (holomorphic_exterior_deriv_bound hd hM hx').trans (le_max_right _ _)
  obtain ⟨C,hC0,hC⟩ := hlocal (R+3)
  let K := C+2*B+2*M
  have hKC : C ≤ K := by dsimp [K]; linarith
  have hKB : 2*B ≤ K := by dsimp [K]; linarith
  have hKM : 2*M ≤ K := by dsimp [K]; linarith
  refine ⟨B,K,hB0,hC0.trans hKC,hB,?_⟩
  intro x y
  have hp : 0 ≤ ‖x-y‖^((1:ℝ)/3) := Real.rpow_nonneg (norm_nonneg _) _
  by_cases hxy : ‖x-y‖ ≤ 1
  · by_cases hx : ‖x‖ ≤ R+2
    · have hy : ‖y‖ ≤ R+3 := by
        have ht : ‖y‖ ≤ ‖x‖+‖x-y‖ := by simpa only [norm_sub_rev] using norm_le_insert' y x
        linarith
      exact (hC x (by simp only [Metric.mem_closedBall,dist_zero_right]; linarith)
        y (by simpa only [Metric.mem_closedBall,dist_zero_right] using hy)).trans
        (mul_le_mul_of_nonneg_right hKC hp)
    · have hh := holomorphic_exterior_fderiv_lipschitz_near hd hM (lt_of_not_ge hx) hxy
      exact hh.trans ((mul_le_mul_of_nonneg_left
        (Real.self_le_rpow_of_le_one (norm_nonneg _) hxy (by norm_num : (1:ℝ)/3 ≤ 1))
        (mul_nonneg (by norm_num) hM0)).trans (mul_le_mul_of_nonneg_right hKM hp))
  · have hh : ‖fderiv ℝ f x-fderiv ℝ f y‖ ≤ 2*B :=
      (norm_sub_le _ _).trans (by linarith [hB x,hB y])
    have hpow : 1 ≤ ‖x-y‖^((1:ℝ)/3) := Real.one_le_rpow (le_of_not_ge hxy) (by norm_num)
    exact hh.trans ((le_mul_of_one_le_right (mul_nonneg (by norm_num) hB0) hpow).trans
      (mul_le_mul_of_nonneg_right hKB hp))

end

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

 theorem cauchyTransform_apply_swap (g : ℂ → E) (z : ℂ) :
    cauchyTransform g z = (Real.pi:ℂ)⁻¹ • ∫ w : ℂ, (z-w)⁻¹ • g w := by
  rw [cauchyTransform,Pi.smul_apply,convolution_eq_swap]
  rfl

 theorem cauchyTransform_tendsto_zero {g : ℂ → E} (hg : Continuous g)
    (hc : HasCompactSupport g) :
    Tendsto (cauchyTransform g) (cocompact ℂ) (𝓝 0) := by
  have : (cocompact ℂ).IsCountablyGenerated := by
    rw [←Metric.cobounded_eq_cocompact,←comap_norm_atTop]
    infer_instance
  have hi : Integrable g := hg.integrable_of_hasCompactSupport hc
  obtain ⟨R,hR⟩ := hc.isBounded.exists_norm_le
  have hlarge : ∀ᶠ z : ℂ in cocompact ℂ, R+1 ≤ ‖z‖ :=
    tendsto_norm_cocompact_atTop.eventually (eventually_ge_atTop (R+1))
  have hi' (z : ℂ) : Integrable (fun w : ℂ => (z-w)⁻¹ • g w) := by
    exact convolutionExistsAt_iff_integrable_swap.mp
      (hc.convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℂ)
        locallyIntegrable_complex_inv hg z)
  have hb : ∀ᶠ z : ℂ in cocompact ℂ, ∀ᵐ w : ℂ, ‖(z-w)⁻¹ • g w‖ ≤ ‖g w‖ := by
    filter_upwards [hlarge] with z hz
    apply ae_of_all
    intro w
    by_cases hw : w∈tsupport g
    · have hn : 1≤‖z-w‖ := by
        have hh := hR w hw
        have ht := norm_sub_norm_le z w
        linarith
      rw [norm_smul,norm_inv]
      exact mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ hn)
    · simp only [image_eq_zero_of_notMem_tsupport hw,smul_zero,norm_zero,le_refl]
  have hl : ∀ᵐ w : ℂ, Tendsto (fun z : ℂ => (z-w)⁻¹ • g w) (cocompact ℂ) (𝓝 0) := by
    apply ae_of_all
    intro w
    have ht : Tendsto (fun z : ℂ => z-w) (cocompact ℂ) (cocompact ℂ) :=
      (Homeomorph.subRight w).isClosedEmbedding.tendsto_cocompact
    have hinv : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 (0:ℂ)) := by
      rw [←Metric.cobounded_eq_cocompact]
      exact tendsto_inv₀_cobounded
    simpa only [Function.comp_def,zero_smul] using (hinv.comp ht).smul_const (g w)
  have ht := tendsto_integral_filter_of_dominated_convergence (fun w : ℂ => ‖g w‖)
    (Eventually.of_forall (fun z => (hi' z).aestronglyMeasurable)) hb hi.norm hl
  simp only [integral_zero] at ht
  have he : cauchyTransform g = (fun z => (Real.pi:ℂ)⁻¹ • ∫ w : ℂ, (z-w)⁻¹ • g w) :=
    funext (cauchyTransform_apply_swap g)
  rw [he]
  simpa only [smul_zero] using ht.const_smul (Real.pi:ℂ)⁻¹

end

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

lemma cauchyTransform_holder_holomorphic_off {g : ℂ → E} (hg : Continuous g)
    (hc : HasCompactSupport g) {M H : ℝ} (hM : ∀ x, ‖g x‖ ≤ M) (hH : 0 ≤ H)
    (hHg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) {x : ℂ} (hx : g x=0) :
    DifferentiableAt ℂ (cauchyTransform g) x := by
  apply differentiableAt_complex_iff_differentiableAt_real.mpr
  refine ⟨(cauchyTransform_holder_contDiff_oneNecessity hg hc hM hH hHg).differentiable (by simp) x,?_⟩
  have hh := cauchyTransform_holder_complexCurl hg hc hM hH hHg x
  rw [hx,smul_zero] at hh
  exact (sub_eq_zero.mp hh).symm

theorem cauchyTransform_holder_global {g : ℂ → E} (hg : Continuous g)
    (hc : HasCompactSupport g) {M H : ℝ} (hM : ∀ x, ‖g x‖ ≤ M) (hH : 0 ≤ H)
    (hHg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) :
    ∃ A B K : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ K ∧
      (∀ x, ‖cauchyTransform g x‖ ≤ A) ∧
      (∀ x, ‖fderiv ℝ (cauchyTransform g) x‖ ≤ B) ∧
      (∀ x y, ‖cauchyTransform g x-cauchyTransform g y‖ ≤ K*‖x-y‖^((1:ℝ)/3)) ∧
      (∀ x y, ‖fderiv ℝ (cauchyTransform g) x-fderiv ℝ (cauchyTransform g) y‖ ≤
        K*‖x-y‖^((1:ℝ)/3)) := by
  have hf := cauchyTransform_holder_contDiff_oneNecessity hg hc hM hH hHg
  let f0 : ZeroAtInftyContinuousMap ℂ E :=
    ⟨⟨cauchyTransform g,hf.continuous⟩,cauchyTransform_tendsto_zero hg hc⟩
  obtain ⟨A,hA⟩ := f0.isBounded_range.exists_norm_le
  have hA' (x : ℂ) : ‖cauchyTransform g x‖ ≤ A := hA _ ⟨x,rfl⟩
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA' 0)
  obtain ⟨R,hR⟩ := hc.isBounded.subset_closedBall (0:ℂ)
  have hd : DifferentiableOn ℂ (cauchyTransform g) {z : ℂ | R < ‖z‖} := by
    intro x hx
    apply (cauchyTransform_holder_holomorphic_off hg hc hM hH hHg ?_).differentiableWithinAt
    apply image_eq_zero_of_notMem_tsupport
    intro h
    have hh := hR h
    simp only [Metric.mem_closedBall,dist_zero_right] at hh
    exact (not_le_of_gt hx) hh
  have hlocal (S : ℝ) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Metric.closedBall (0:ℂ) S, ∀ y ∈ Metric.closedBall (0:ℂ) S,
      ‖fderiv ℝ (cauchyTransform g) x-fderiv ℝ (cauchyTransform g) y‖ ≤
        C*‖x-y‖^((1:ℝ)/3) := by
    obtain ⟨C,hC0,hC⟩ := cauchyTransform_fderiv_holder_on (E := E) (max R S)
    refine ⟨C*H,mul_nonneg hC0 hH,?_⟩
    intro x hx y hy
    exact hC g hg (hR.trans (Metric.closedBall_subset_closedBall (le_max_left _ _)))
      M H hM hH hHg x (Metric.closedBall_subset_closedBall (le_max_right _ _) hx)
      y (Metric.closedBall_subset_closedBall (le_max_right _ _) hy)
  obtain ⟨B,K,hB0,hK0,hB,hK⟩ := global_holder_fderiv_of_holomorphic_exterior hf hd hA' hlocal
  have hL : LipschitzWith ⟨B,hB0⟩ (cauchyTransform g) :=
    lipschitzWith_of_nnnorm_fderiv_le (hf.differentiable (by simp)) (fun x => hB x)
  refine ⟨A,B,K+B+2*A,hA0,hB0,by positivity,hA',hB,?_,?_⟩
  · intro x y
    have hp : 0 ≤ ‖x-y‖^((1:ℝ)/3) := Real.rpow_nonneg (norm_nonneg _) _
    by_cases hxy : ‖x-y‖ ≤ 1
    · have hh : ‖cauchyTransform g x-cauchyTransform g y‖ ≤ B*‖x-y‖ := by
        have ht := hL.dist_le_mul x y
        change dist (cauchyTransform g x) (cauchyTransform g y) ≤ B*dist x y at ht
        simpa only [dist_eq_norm] using ht
      exact hh.trans ((mul_le_mul_of_nonneg_left
        (Real.self_le_rpow_of_le_one (norm_nonneg _) hxy (by norm_num : (1:ℝ)/3 ≤ 1)) hB0).trans
          (mul_le_mul_of_nonneg_right (by linarith : B ≤ K+B+2*A) hp))
    · have hh : ‖cauchyTransform g x-cauchyTransform g y‖ ≤ 2*A :=
        (norm_sub_le _ _).trans (by linarith [hA' x,hA' y])
      exact hh.trans ((le_mul_of_one_le_right (by positivity : 0 ≤ 2*A)
        (Real.one_le_rpow (le_of_not_ge hxy) (by norm_num : 0 ≤ (1:ℝ)/3))).trans
          (mul_le_mul_of_nonneg_right (by linarith : 2*A ≤ K+B+2*A) hp))
  · intro x y
    exact (hK x y).trans (mul_le_mul_of_nonneg_right (by linarith : K ≤ K+B+2*A)
      (Real.rpow_nonneg (norm_nonneg _) _))

omit [CompleteSpace E] in
lemma integrableKernel_smul_convolution_tendsto {K : ℂ → ℂ} (hK : Integrable K)
    {g : ℕ → ℂ → E} (hg : ∀ j, Continuous (g j)) {v : ℂ → E}
    (hgv : ∀ w, Tendsto (fun j => g j w) atTop (𝓝 (v w)))
    {M : ℝ} (hM : ∀ j w, ‖g j w‖ ≤ M) (x : ℂ) :
    Tendsto (fun j => MeasureTheory.convolution K (g j) (ContinuousLinearMap.lsmul ℝ ℂ) volume x)
      atTop (𝓝 (MeasureTheory.convolution K v (ContinuousLinearMap.lsmul ℝ ℂ) volume x)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun w : ℂ => ‖K w‖*M)
  · apply Eventually.of_forall
    intro j
    exact hK.aestronglyMeasurable.smul
      ((hg j).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · apply Eventually.of_forall
    intro j
    apply ae_of_all
    intro w
    change ‖K w • g j (x-w)‖ ≤ _
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hM j (x-w)) (norm_nonneg _)
  · exact hK.norm.mul_const M
  · apply ae_of_all
    intro w
    exact (hgv (x-w)).const_smul (K w)

omit [CompleteSpace E] in
lemma cauchyTransform_tendsto_compact_data {g : ℕ → ℂ → E} (hg : ∀ j, Continuous (g j))
    {v : ℂ → E} (hgv : ∀ w, Tendsto (fun j => g j w) atTop (𝓝 (v w))) {R : ℝ}
    (hgs : ∀ j, tsupport (g j) ⊆ Metric.closedBall (0:ℂ) R)
    (hvs : tsupport v ⊆ Metric.closedBall (0:ℂ) R)
    {M : ℝ} (hM : ∀ j w, ‖g j w‖ ≤ M) (x : ℂ) :
    Tendsto (fun j => cauchyTransform (g j) x) atTop (𝓝 (cauchyTransform v x)) := by
  let S : ℝ := max R 0+‖x‖+1
  have hRS : R ≤ S := by dsimp [S]; linarith [le_max_left R 0,norm_nonneg x]
  have hS : 0 < S := by dsimp [S]; linarith [le_max_right R 0,norm_nonneg x]
  have hxS : ‖x‖ < S := by dsimp [S]; linarith [le_max_right R 0]
  let b : ContDiffBump (0:ℂ) := ⟨2*S,2*S+1,by positivity,by linarith⟩
  have he {f : ℂ → E} (hs : tsupport f ⊆ Metric.closedBall (0:ℂ) R) :
      cauchyTransform f x = (Real.pi:ℂ)⁻¹ • MeasureTheory.convolution
        (cutoffCauchyKernel b) f (ContinuousLinearMap.lsmul ℝ ℂ) volume x := by
    exact congrArg ((Real.pi:ℂ)⁻¹ • ·) (cutoff_cauchy_supported_eq b (le_refl _)
      (hs.trans (Metric.closedBall_subset_closedBall hRS))
      (show x ∈ Metric.closedBall (0:ℂ) S by
        simpa only [Metric.mem_closedBall,dist_zero_right] using hxS.le)).symm
  simp_rw [he hvs,he (hgs _)]
  exact (integrableKernel_smul_convolution_tendsto (cutoffCauchyKernel_integrableNecessity b)
    hg hgv hM x).const_smul (Real.pi:ℂ)⁻¹

omit [CompleteSpace E] in
lemma cauchyTransform_add_compact {g h : ℂ → E} (hg : Continuous g)
    (hh : Continuous h) (hgc : HasCompactSupport g) (hhc : HasCompactSupport h) :
    cauchyTransform (g+h) = cauchyTransform g+cauchyTransform h := by
  ext x
  simp only [cauchyTransform_apply,Pi.add_apply,smul_add]
  have hi : Integrable (fun w : ℂ => w⁻¹ • g (x-w)) :=
    hgc.convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℂ) locallyIntegrable_complex_inv hg x
  have hi' : Integrable (fun w : ℂ => w⁻¹ • h (x-w)) :=
    hhc.convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℂ) locallyIntegrable_complex_inv hh x
  rw [integral_add hi hi',smul_add]

omit [CompleteSpace E] in
lemma cauchyTransform_real_smul (c : ℝ) (g : ℂ → E) :
    cauchyTransform (c • g) = c • cauchyTransform g := by
  ext x
  simp only [cauchyTransform_apply,Pi.smul_apply,smul_comm (n := c),integral_smul]

end

universe u v
variable (K : Type u) [MetricSpace K]

abbrev OffDiagonal := {p : K × K // p.1 ≠ p.2}

variable (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E]

def holderGraph (α : ℝ) : Submodule ℝ ((K →ᵇ E) × (OffDiagonal K →ᵇ E)) where
  carrier := {p | ∀ z : OffDiagonal K,
    p.1 z.val.1 - p.1 z.val.2 = (dist z.val.1 z.val.2)^α • p.2 z}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq z
    change (p.1 z.val.1+q.1 z.val.1)-(p.1 z.val.2+q.1 z.val.2) = _
    rw [show (p.1 z.val.1+q.1 z.val.1)-(p.1 z.val.2+q.1 z.val.2) =
      (p.1 z.val.1-p.1 z.val.2)+(q.1 z.val.1-q.1 z.val.2) by abel, hp z, hq z]
    exact (smul_add _ _ _).symm
  smul_mem' := by
    intro c p hp z
    change c • p.1 z.val.1-c • p.1 z.val.2 = _
    rw [← smul_sub, hp z, smul_comm]
    rfl

instance holderGraph_isClosed (α : ℝ) : IsClosed (↑(holderGraph K E α) : Set ((K →ᵇ E) × (OffDiagonal K →ᵇ E))) := by
  change IsClosed {p : (K →ᵇ E) × (OffDiagonal K →ᵇ E) | ∀ z : OffDiagonal K,
    p.1 z.val.1 - p.1 z.val.2 = (dist z.val.1 z.val.2)^α • p.2 z}
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro z
  exact isClosed_eq
    (((BoundedContinuousFunction.evalCLM ℝ z.val.1).continuous.comp continuous_fst).sub
      ((BoundedContinuousFunction.evalCLM ℝ z.val.2).continuous.comp continuous_fst))
    (((BoundedContinuousFunction.evalCLM ℝ z).continuous.comp continuous_snd).const_smul _)

abbrev HolderSpace (α : ℝ) := ↥(holderGraph K E α)

instance holderSpace_complete [CompleteSpace E] (α : ℝ) : CompleteSpace (HolderSpace K E α) :=
  IsClosed.completeSpace_coe

variable {K E}

def holderValue (α : ℝ) : HolderSpace K E α →L[ℝ] (K →ᵇ E) :=
  (ContinuousLinearMap.fst ℝ _ _).comp (holderGraph K E α).subtypeL

def holderDifference (α : ℝ) : HolderSpace K E α →L[ℝ] (OffDiagonal K →ᵇ E) :=
  (ContinuousLinearMap.snd ℝ _ _).comp (holderGraph K E α).subtypeL

@[simp] theorem holderValue_apply (α : ℝ) (f : HolderSpace K E α) (x : K) :
    holderValue α f x = f.val.1 x := rfl

@[simp] theorem holderDifference_apply (α : ℝ) (f : HolderSpace K E α) (z : OffDiagonal K) :
    holderDifference α f z = f.val.2 z := rfl

theorem holderSpace_relation (α : ℝ) (f : HolderSpace K E α) (x y : K) (hxy : x≠y) :
    holderValue α f x - holderValue α f y =
      (dist x y)^α • holderDifference α f ⟨(x,y),hxy⟩ := f.property ⟨(x,y),hxy⟩

theorem holderValue_injective (α : ℝ) : Function.Injective (holderValue (K := K) (E := E) α) := by
  intro f g h
  apply Subtype.ext
  apply Prod.ext
  · exact h
  · ext z
    have hf := f.property z
    have hg := g.property z
    have h0 : (dist z.val.1 z.val.2)^α ≠ 0 :=
      (Real.rpow_pos_of_pos (dist_pos.mpr z.property) α).ne'
    have he : (dist z.val.1 z.val.2)^α • f.val.2 z = (dist z.val.1 z.val.2)^α • g.val.2 z := by
      rw [← hf, ← hg]
      exact congrArg (fun F : K →ᵇ E => F z.val.1-F z.val.2) h
    exact (smul_right_injective E h0) he

theorem holderSpace_estimate (α : ℝ) (hα : 0<α) (f : HolderSpace K E α) (x y : K) :
    ‖holderValue α f x - holderValue α f y‖ ≤ ‖f‖ * (dist x y)^α := by
  by_cases hxy : x=y
  · subst y
    simp [Real.zero_rpow hα.ne']
  rw [holderSpace_relation α f x y hxy, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg dist_nonneg α)]
  have hb : ‖holderDifference α f ⟨(x,y),hxy⟩‖ ≤ ‖f‖ := by
    exact (f.val.2.norm_coe_le_norm _).trans (le_max_right _ _)
  exact (mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg dist_nonneg α)).trans_eq (mul_comm _ _)

def holderSpaceMk (α : ℝ) (f : K →ᵇ E) (H : ℝ) (_hH : 0≤H)
    (hf : ∀ x y : K, ‖f x-f y‖ ≤ H*(dist x y)^α) : HolderSpace K E α := by
  let g : OffDiagonal K →ᵇ E := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun z => ((dist z.val.1 z.val.2)^α)⁻¹ • (f z.val.1-f z.val.2))
    (by
      have hd : Continuous (fun z : OffDiagonal K => dist z.val.1 z.val.2) :=
        (continuous_fst.comp continuous_subtype_val).dist
          (continuous_snd.comp continuous_subtype_val)
      have hp : ∀ z : OffDiagonal K, dist z.val.1 z.val.2 ≠ 0 :=
        fun z => dist_ne_zero.mpr z.property
      exact ((hd.rpow_const (fun z => Or.inl (hp z))).inv₀
        (fun z => (Real.rpow_pos_of_pos (dist_pos.mpr z.property) α).ne')).smul
        ((f.continuous.comp (continuous_fst.comp continuous_subtype_val)).sub
          (f.continuous.comp (continuous_snd.comp continuous_subtype_val))))
    H (by
      intro z
      have hw : 0<(dist z.val.1 z.val.2)^α := Real.rpow_pos_of_pos (dist_pos.mpr z.property) α
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hw)]
      exact (mul_le_mul_of_nonneg_left (hf z.val.1 z.val.2) (inv_nonneg.mpr hw.le)).trans_eq
        (by rw [mul_comm H, ← mul_assoc, inv_mul_cancel₀ hw.ne', one_mul]))
  refine ⟨(f,g),fun z => ?_⟩
  change f z.val.1-f z.val.2 = (dist z.val.1 z.val.2)^α •
    (((dist z.val.1 z.val.2)^α)⁻¹ • (f z.val.1-f z.val.2))
  rw [smul_smul, mul_inv_cancel₀ (Real.rpow_pos_of_pos (dist_pos.mpr z.property) α).ne', one_smul]

@[simp] theorem holderValue_mk (α : ℝ) (f : K →ᵇ E) (H : ℝ) (hH : 0≤H)
    (hf : ∀ x y : K, ‖f x-f y‖ ≤ H*(dist x y)^α) :
    holderValue α (holderSpaceMk α f H hH hf) = f := rfl

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_HolderCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl )
open SymplecticBallPacking.Hamiltonian (Plane )
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
namespace HigherDimensionalBallPacking.Rigidity
universe u v
variable {K : Type u} {E F : Type v} [TopologicalSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

 
def sectionApply (M : K →ᵇ (E →L[ℝ] F)) (v : K →ᵇ E) : K →ᵇ F :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun z => M z (v z)) (M.continuous.clm_apply v.continuous)
    (‖M‖*‖v‖) (fun z => (M z).le_opNorm (v z) |>.trans
      (mul_le_mul (M.norm_coe_le_norm z) (v.norm_coe_le_norm z)
        (norm_nonneg (v z)) (norm_nonneg M)))

theorem sectionApply_norm (M : K →ᵇ (E →L[ℝ] F)) (v : K →ᵇ E) :
    ‖sectionApply M v‖ ≤ ‖M‖*‖v‖ := by
  apply (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg M) (norm_nonneg v))).mpr
  intro z
  exact (M z).le_opNorm (v z) |>.trans
    (mul_le_mul (M.norm_coe_le_norm z) (v.norm_coe_le_norm z)
      (norm_nonneg (v z)) (norm_nonneg M))

def sectionCLM (M : K →ᵇ (E →L[ℝ] F)) : (K →ᵇ E) →L[ℝ] (K →ᵇ F) :=
  LinearMap.mkContinuous
    { toFun := sectionApply M
      map_add' := fun v w => by ext z; exact (M z).map_add _ _
      map_smul' := fun c v => by ext z; exact (M z).map_smul c (v z) }
    ‖M‖ (sectionApply_norm M)

@[simp] theorem sectionCLM_apply (M : K →ᵇ (E →L[ℝ] F)) (v : K →ᵇ E) (z : K) :
    sectionCLM M v z = M z (v z) := rfl

def sectionOperatorCLM : (K →ᵇ (E →L[ℝ] F)) →L[ℝ] ((K →ᵇ E) →L[ℝ] (K →ᵇ F)) :=
  LinearMap.mkContinuous
    { toFun := sectionCLM
      map_add' := fun M N => by ext v z; rfl
      map_smul' := fun c M => by ext v z; rfl }
    1 (fun M => by
      change ‖sectionCLM M‖ ≤ 1*‖M‖
      rw [one_mul]
      exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg M) (sectionApply_norm M))

@[simp] theorem sectionOperatorCLM_apply (M : K →ᵇ (E →L[ℝ] F)) :
    sectionOperatorCLM M = sectionCLM M := rfl

 

def superposeBCF (f : E →ᵇ F) (base : C(K,E)) (v : K →ᵇ E) : K →ᵇ F :=
  f.compContinuous ⟨fun z => base z + v z, base.continuous.add v.continuous⟩

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
@[simp] theorem superposeBCF_apply (f : E →ᵇ F) (base : C(K,E)) (v : K →ᵇ E) (z : K) :
    superposeBCF f base v z = f (base z + v z) := rfl


def compactCoefficient (f : E → F) (hf : Continuous f) (hc : HasCompactSupport f) : E →ᵇ F :=
  ({ toFun := f, continuous_toFun := hf, hasCompactSupport' := hc } :
    CompactlySupportedContinuousMap E F).toBoundedContinuousFunction

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
@[simp] theorem compactCoefficient_apply (f : E → F) (hf : Continuous f)
    (hc : HasCompactSupport f) (x : E) : compactCoefficient f hf hc x = f x := rfl

end HigherDimensionalBallPacking.Rigidity

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
namespace HigherDimensionalBallPacking.Rigidity
universe u v
variable {K : Type u} [MetricSpace K]
variable {E F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance instNormedAddCommGroupHolderSpace (G : Type v) [NormedAddCommGroup G] [NormedSpace ℝ G] (α : ℝ) :
    NormedAddCommGroup (HolderSpace K G α) := inferInstance

def pairLeft (G : Type v) [NormedAddCommGroup G] [NormedSpace ℝ G] :
    (K →ᵇ G) →L[ℝ] (OffDiagonal K →ᵇ G) :=
  BoundedContinuousFunction.compContinuousCLM G ℝ
    ⟨fun z => z.val.1, continuous_fst.comp continuous_subtype_val⟩

def pairRight (G : Type v) [NormedAddCommGroup G] [NormedSpace ℝ G] :
    (K →ᵇ G) →L[ℝ] (OffDiagonal K →ᵇ G) :=
  BoundedContinuousFunction.compContinuousCLM G ℝ
    ⟨fun z => z.val.2, continuous_snd.comp continuous_subtype_val⟩

@[simp] theorem pairLeft_apply (v : K →ᵇ E) (z : OffDiagonal K) : pairLeft E v z = v z.val.1 := rfl
@[simp] theorem pairRight_apply (v : K →ᵇ E) (z : OffDiagonal K) : pairRight E v z = v z.val.2 := rfl

theorem pairLeft_norm (v : K →ᵇ E) : ‖pairLeft E v‖ ≤ ‖v‖ :=
  BoundedContinuousFunction.norm_compContinuous_le _ _
theorem pairRight_norm (v : K →ᵇ E) : ‖pairRight E v‖ ≤ ‖v‖ :=
  BoundedContinuousFunction.norm_compContinuous_le _ _

theorem holderValue_norm (α : ℝ) (v : HolderSpace K E α) : ‖holderValue α v‖ ≤ ‖v‖ :=
  le_max_left _ _
theorem holderDifference_norm (α : ℝ) (v : HolderSpace K E α) : ‖holderDifference α v‖ ≤ ‖v‖ :=
  le_max_right _ _

def holderApply (α : ℝ) (M : HolderSpace K (E →L[ℝ] F) α) (v : HolderSpace K E α) :
    HolderSpace K F α :=
  ⟨(sectionCLM (holderValue α M) (holderValue α v),
    sectionCLM (holderDifference α M) (pairLeft E (holderValue α v)) +
      sectionCLM (pairRight (E →L[ℝ] F) (holderValue α M)) (holderDifference α v)), by
    intro z
    change M.val.1 z.val.1 (v.val.1 z.val.1)-M.val.1 z.val.2 (v.val.1 z.val.2) =
      (dist z.val.1 z.val.2)^α •
        (M.val.2 z (v.val.1 z.val.1)+M.val.1 z.val.2 (v.val.2 z))
    calc
      _ = (M.val.1 z.val.1-M.val.1 z.val.2) (v.val.1 z.val.1) +
          M.val.1 z.val.2 (v.val.1 z.val.1-v.val.1 z.val.2) := by
        simp only [sub_apply,map_sub]
        abel
      _ = _ := by
        rw [M.property z,v.property z]
        simp only [smul_apply,map_smul,smul_add]⟩

@[simp] theorem holderApply_value (α : ℝ) (M : HolderSpace K (E →L[ℝ] F) α)
    (v : HolderSpace K E α) (x : K) :
    holderValue α (holderApply α M v) x = holderValue α M x (holderValue α v x) := rfl

theorem holderApply_norm (α : ℝ) (M : HolderSpace K (E →L[ℝ] F) α) (v : HolderSpace K E α) :
    ‖holderApply α M v‖ ≤ 2*‖M‖*‖v‖ := by
  apply max_le
  · exact (sectionApply_norm _ _).trans ((mul_le_mul (holderValue_norm α M) (holderValue_norm α v)
      (norm_nonneg _) (norm_nonneg _)).trans (by nlinarith [norm_nonneg M,norm_nonneg v]))
  · refine (norm_add_le _ _).trans ?_
    have h1 := (sectionApply_norm (holderDifference α M) (pairLeft E (holderValue α v))).trans
      (mul_le_mul (holderDifference_norm α M) ((pairLeft_norm _).trans (holderValue_norm α v))
        (norm_nonneg _) (norm_nonneg _))
    have h2 := (sectionApply_norm (pairRight (E →L[ℝ] F) (holderValue α M)) (holderDifference α v)).trans
      (mul_le_mul ((pairRight_norm _).trans (holderValue_norm α M)) (holderDifference_norm α v)
        (norm_nonneg _) (norm_nonneg _))
    exact (add_le_add h1 h2).trans_eq (by ring)

def holderCLM (α : ℝ) (M : HolderSpace K (E →L[ℝ] F) α) :
    HolderSpace K E α →L[ℝ] HolderSpace K F α :=
  LinearMap.mkContinuous
    { toFun := holderApply α M
      map_add' := by
        intro v w
        apply holderValue_injective α
        ext x
        exact (M.val.1 x).map_add _ _
      map_smul' := by
        intro c v
        apply holderValue_injective α
        ext x
        exact (M.val.1 x).map_smul c (v.val.1 x) }
    (2*‖M‖) (holderApply_norm α M)

@[simp] theorem holderCLM_apply (α : ℝ) (M : HolderSpace K (E →L[ℝ] F) α)
    (v : HolderSpace K E α) (x : K) :
    holderValue α (holderCLM α M v) x = holderValue α M x (holderValue α v x) := rfl

end HigherDimensionalBallPacking.Rigidity

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
namespace HigherDimensionalBallPacking.Rigidity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def holderDiskRestrict (R : ℝ) :
    HolderSpace ℂ E ((1:ℝ)/3) →L[ℝ] (Metric.closedBall (0:ℂ) R →ᵇ E) :=
  (BoundedContinuousFunction.compContinuousCLM E ℝ ⟨Subtype.val,continuous_subtype_val⟩).comp
    (holderValue ((1:ℝ)/3))

@[simp] lemma holderDiskRestrict_apply (R : ℝ) (u : HolderSpace ℂ E ((1:ℝ)/3))
    (x : Metric.closedBall (0:ℂ) R) : holderDiskRestrict R u x=holderValue ((1:ℝ)/3) u x := rfl

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_MarkedInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl )
open SymplecticBallPacking.Hamiltonian (Plane )
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology

namespace HigherDimensionalBallPacking.Rigidity
open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

local instance instNormedAddCommGroupBoundedContinuousFunctionComplexContinuousLinearMapRealId_solutions : NormedAddCommGroup (ℂ →ᵇ (ℂ →L[ℝ] E)) := inferInstance

omit [CompleteSpace E] in
theorem segmentIntegrand_continuous (A : ℂ →ᵇ (ℂ →L[ℝ] E)) (x y : ℂ) :
    Continuous (fun t : ℝ => A (x+t • (y-x)) (y-x)) :=
  (A.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const

def linearSegmentIntegral (x y : ℂ) : (ℂ →ᵇ (ℂ →L[ℝ] E)) →L[ℝ] E :=
  LinearMap.mkContinuous
    { toFun := fun A => ∫ t in (0:ℝ)..1, A (x+t • (y-x)) (y-x)
      map_add' := by
        intro A B
        exact intervalIntegral.integral_add
          ((segmentIntegrand_continuous A x y).intervalIntegrable _ _)
          ((segmentIntegrand_continuous B x y).intervalIntegrable _ _)
      map_smul' := fun c A => intervalIntegral.integral_smul c _ }
    ‖y-x‖ (fun A => by
      change ‖∫ t in (0:ℝ)..1, A (x+t • (y-x)) (y-x)‖ ≤ ‖y-x‖*‖A‖
      have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1)
        (fun t _ => ((A (x+t • (y-x))).le_opNorm (y-x)).trans
          (mul_le_mul_of_nonneg_right (A.norm_coe_le_norm _) (norm_nonneg _)))
      simpa only [sub_zero,abs_one,one_mul,mul_comm] using h)

omit [CompleteSpace E] in
@[simp] theorem linearSegmentIntegral_apply (x y : ℂ) (A : ℂ →ᵇ (ℂ →L[ℝ] E)) :
    linearSegmentIntegral x y A = ∫ t in (0:ℝ)..1, A (x+t • (y-x)) (y-x) := rfl

abbrev C1HolderAmbient (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) :=
  HolderSpace ℂ E α × HolderSpace ℂ (ℂ →L[ℝ] E) α

def c1HolderGraph (α : ℝ) : Submodule ℝ (C1HolderAmbient E α) where
  carrier := {p | ∀ x y : ℂ, holderValue α p.1 y - holderValue α p.1 x =
    linearSegmentIntegral x y (holderValue α p.2)}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq x y
    change (holderValue α p.1 y+holderValue α q.1 y) -
      (holderValue α p.1 x+holderValue α q.1 x) =
      linearSegmentIntegral x y (holderValue α p.2+holderValue α q.2)
    rw [map_add,← hp x y,← hq x y]
    abel
  smul_mem' := by
    intro c p hp x y
    change c • holderValue α p.1 y - c • holderValue α p.1 x =
      linearSegmentIntegral x y (c • holderValue α p.2)
    rw [map_smul,← hp x y,smul_sub]

instance c1HolderGraph_isClosed (α : ℝ) :
    IsClosed (↑(c1HolderGraph (E := E) α) : Set (C1HolderAmbient E α)) := by
  change IsClosed {p : C1HolderAmbient E α | ∀ x y : ℂ,
    holderValue α p.1 y - holderValue α p.1 x = linearSegmentIntegral x y (holderValue α p.2)}
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro x
  apply isClosed_iInter
  intro y
  exact isClosed_eq
    ((((BoundedContinuousFunction.evalCLM ℝ y).continuous.comp (holderValue α).continuous).comp continuous_fst).sub
      (((BoundedContinuousFunction.evalCLM ℝ x).continuous.comp (holderValue α).continuous).comp continuous_fst))
    (((linearSegmentIntegral x y).continuous.comp (holderValue α).continuous).comp continuous_snd)

abbrev C1HolderSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (α : ℝ) :=
  ↥(c1HolderGraph (E := E) α)

instance c1HolderSpace_complete (α : ℝ) : CompleteSpace (C1HolderSpace E α) :=
  IsClosed.completeSpace_coe

def c1HolderValue (α : ℝ) : C1HolderSpace E α →L[ℝ] HolderSpace ℂ E α :=
  (ContinuousLinearMap.fst ℝ _ _).comp (c1HolderGraph α).subtypeL

def c1HolderDeriv (α : ℝ) : C1HolderSpace E α →L[ℝ] HolderSpace ℂ (ℂ →L[ℝ] E) α :=
  (ContinuousLinearMap.snd ℝ _ _).comp (c1HolderGraph α).subtypeL

@[simp] theorem c1HolderValue_apply (α : ℝ) (u : C1HolderSpace E α) :
    c1HolderValue α u = u.val.1 := rfl
@[simp] theorem c1HolderDeriv_apply (α : ℝ) (u : C1HolderSpace E α) :
    c1HolderDeriv α u = u.val.2 := rfl

theorem linearSegmentIntegral_remainder (A : ℂ →ᵇ (ℂ →L[ℝ] E)) (x h : ℂ) :
    linearSegmentIntegral x (x+h) A - A x h =
      ∫ t in (0:ℝ)..1, (A (x+t • h)-A x) h := by
  rw [linearSegmentIntegral_apply,add_sub_cancel_left]
  simp only [sub_apply]
  rw [intervalIntegral.integral_sub
    (by simpa only [add_sub_cancel_left] using
      (segmentIntegrand_continuous A x (x+h)).intervalIntegrable (0:ℝ) 1)
    (continuous_const.intervalIntegrable _ _)]
  simp only [intervalIntegral.integral_const,sub_zero,one_smul]

 
theorem c1Holder_hasFDerivAt (α : ℝ) (u : C1HolderSpace E α) (x : ℂ) :
    HasFDerivAt (holderValue α (c1HolderValue α u)) (holderValue α (c1HolderDeriv α u) x) x := by
  let f := holderValue α (c1HolderValue α u)
  let A := holderValue α (c1HolderDeriv α u)
  change HasFDerivAt (f : ℂ → E) (A x) x
  rw [hasFDerivAt_iff_isLittleO_nhds_zero,Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ,hδ,hA⟩ := Metric.continuousAt_iff.mp A.continuous.continuousAt ε hε
  filter_upwards [Metric.ball_mem_nhds (0:ℂ) hδ] with h hh
  have hh' : ‖h‖<δ := by simpa only [Metric.mem_ball,dist_zero_right] using hh
  have he : f (x+h)-f x-A x h = ∫ t in (0:ℝ)..1, (A (x+t • h)-A x) h := by
    rw [show f (x+h)-f x=linearSegmentIntegral x (x+h) A from u.property x (x+h)]
    exact linearSegmentIntegral_remainder A x h
  rw [he]
  have hb : ∀ t ∈ uIcc (0:ℝ) 1, ‖(A (x+t • h)-A x) h‖ ≤ ε*‖h‖ := by
    intro t ht
    have ht' : t ∈ Icc (0:ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0:ℝ)≤1)] using ht
    have hd : dist (x+t • h) x < δ := by
      rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht'.1]
      exact (mul_le_of_le_one_left (norm_nonneg _) ht'.2).trans_lt hh'
    have hz : ‖A (x+t • h)-A x‖ ≤ ε := by
      simpa only [dist_eq_norm] using (hA hd).le
    exact ((A (x+t • h)-A x).le_opNorm h).trans (mul_le_mul_of_nonneg_right hz (norm_nonneg h))
  simpa only [sub_zero,abs_one,one_mul,mul_one] using intervalIntegral.norm_integral_le_of_norm_le_const
    (fun t ht => hb t (uIoc_subset_uIcc ht))

@[simp] theorem c1Holder_fderiv (α : ℝ) (u : C1HolderSpace E α) (x : ℂ) :
    fderiv ℝ (holderValue α (c1HolderValue α u)) x = holderValue α (c1HolderDeriv α u) x :=
  (c1Holder_hasFDerivAt α u x).fderiv

end HigherDimensionalBallPacking.Rigidity

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
namespace HigherDimensionalBallPacking.Rigidity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

 
lemma c1HolderValue_injective (α : ℝ) : Function.Injective (c1HolderValue (E := E) α) := by
  intro u v h
  apply Subtype.ext
  apply Prod.ext
  · exact h
  · apply holderValue_injective α
    apply BoundedContinuousFunction.ext
    intro x
    change holderValue α (c1HolderDeriv α u) x = holderValue α (c1HolderDeriv α v) x
    rw [←c1Holder_fderiv,←c1Holder_fderiv,h]

 

def c1HolderMk (α : ℝ) (f : ℂ → E) (hf : ContDiff ℝ 1 f)
    (A B K : ℝ) (hK0 : 0 ≤ K)
    (hA : ∀ x, ‖f x‖ ≤ A) (hB : ∀ x, ‖fderiv ℝ f x‖ ≤ B)
    (hKf : ∀ x y, ‖f x-f y‖ ≤ K*(dist x y)^α)
    (hKD : ∀ x y, ‖fderiv ℝ f x-fderiv ℝ f y‖ ≤ K*(dist x y)^α) :
    C1HolderSpace E α := by
  let fB : ℂ →ᵇ E := BoundedContinuousFunction.ofNormedAddCommGroup f hf.continuous A hA
  let DB : ℂ →ᵇ (ℂ →L[ℝ] E) := BoundedContinuousFunction.ofNormedAddCommGroup
    (fderiv ℝ f) (hf.continuous_fderiv (by norm_num)) B hB
  refine ⟨(holderSpaceMk α fB K hK0 hKf,holderSpaceMk α DB K hK0 hKD),?_⟩
  intro x y
  change f y-f x = linearSegmentIntegral x y DB
  rw [linearSegmentIntegral_apply]
  have hder (t : ℝ) : HasDerivAt (fun s : ℝ => f (x+s • (y-x)))
      (DB (x+t • (y-x)) (y-x)) t := by
    change HasDerivAt (fun s : ℝ => f (x+s • (y-x)))
      (fderiv ℝ f (x+t • (y-x)) (y-x)) t
    have hh := (hasDerivAt_id t).smul_const (y-x)
    have hh' := hh.const_add x
    simpa only [id_eq,one_smul,Function.comp_def] using
      ((hf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t hh')
  symm
  simpa only [one_smul,zero_smul,add_zero,add_sub_cancel] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hder t)
      ((segmentIntegrand_continuous DB x y).intervalIntegrable (0:ℝ) 1)

@[simp] theorem c1HolderMk_value (α : ℝ) (f : ℂ → E) (hf : ContDiff ℝ 1 f)
    (A B K : ℝ) (hK0 : 0 ≤ K)
    (hA : ∀ x, ‖f x‖ ≤ A) (hB : ∀ x, ‖fderiv ℝ f x‖ ≤ B)
    (hKf : ∀ x y, ‖f x-f y‖ ≤ K*(dist x y)^α)
    (hKD : ∀ x y, ‖fderiv ℝ f x-fderiv ℝ f y‖ ≤ K*(dist x y)^α) (x : ℂ) :
    holderValue α (c1HolderValue α (c1HolderMk α f hf A B K hK0 hA hB hKf hKD)) x = f x := rfl

end HigherDimensionalBallPacking.Rigidity

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
namespace HigherDimensionalBallPacking.Rigidity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def compactHolderSubmodule (R : ℝ) : Submodule ℝ (HolderSpace ℂ E ((1:ℝ)/3)) where
  carrier := {u | ∀ x : ℂ, R < ‖x‖ → holderValue ((1:ℝ)/3) u x=0}
  zero_mem' := by simp
  add_mem' := by intro u v hu hv x hx; simpa using congrArg₂ (·+·) (hu x hx) (hv x hx)
  smul_mem' := by intro c u hu x hx; simpa using congrArg (c • ·) (hu x hx)

instance compactHolderSubmodule_isClosed (R : ℝ) :
    IsClosed (↑(compactHolderSubmodule (E := E) R) : Set (HolderSpace ℂ E ((1:ℝ)/3))) := by
  change IsClosed {u : HolderSpace ℂ E ((1:ℝ)/3) |
    ∀ x : ℂ, R < ‖x‖ → holderValue ((1:ℝ)/3) u x=0}
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro x
  apply isClosed_iInter
  intro _
  exact isClosed_eq (((BoundedContinuousFunction.evalCLM ℝ x).continuous).comp
    (holderValue ((1:ℝ)/3)).continuous) continuous_const

abbrev CompactHolderSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ) :=
  ↥(compactHolderSubmodule (E := E) R)

instance compactHolderSpace_complete [CompleteSpace E] (R : ℝ) :
    CompleteSpace (CompactHolderSpace E R) := IsClosed.completeSpace_coe

def compactHolderValue (R : ℝ) : CompactHolderSpace E R →L[ℝ] (ℂ →ᵇ E) :=
  (holderValue ((1:ℝ)/3)).comp (compactHolderSubmodule R).subtypeL

@[simp] lemma compactHolderValue_apply (R : ℝ) (u : CompactHolderSpace E R) (x : ℂ) :
    compactHolderValue R u x = holderValue ((1:ℝ)/3) u.val x := rfl

lemma compactHolderValue_support (R : ℝ) (u : CompactHolderSpace E R) :
    tsupport (compactHolderValue R u) ⊆ Metric.closedBall (0:ℂ) R := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  by_contra h
  have hx' : R < ‖x‖ := by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using h
  exact hx (u.property x hx')

lemma compactHolderValue_compactSupport (R : ℝ) (u : CompactHolderSpace E R) :
    HasCompactSupport (compactHolderValue R u) :=
  (isCompact_closedBall (0:ℂ) R).of_isClosed_subset (isClosed_tsupport _) (compactHolderValue_support R u)

lemma compactHolderValue_bound (R : ℝ) (u : CompactHolderSpace E R) (x : ℂ) :
    ‖compactHolderValue R u x‖ ≤ ‖u‖ := by
  exact ((compactHolderValue R u).norm_coe_le_norm x).trans (le_max_left _ _)

lemma compactHolderValue_holder (R : ℝ) (u : CompactHolderSpace E R) (x y : ℂ) :
    ‖compactHolderValue R u x-compactHolderValue R u y‖ ≤ ‖u‖*‖x-y‖^((1:ℝ)/3) := by
  simpa only [compactHolderValue_apply,dist_eq_norm,Submodule.norm_coe] using
    holderSpace_estimate ((1:ℝ)/3) (by norm_num) u.val x y

end HigherDimensionalBallPacking.Rigidity

open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter
namespace HigherDimensionalBallPacking.Rigidity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

local instance instNormedAddCommGroupCompactHolderSpace (R : ℝ) : NormedAddCommGroup (CompactHolderSpace E R) := inferInstance
local instance instNormedSpaceRealCompactHolderSpace (R : ℝ) : NormedSpace ℝ (CompactHolderSpace E R) := inferInstance
local instance instNormedAddCommGroupC1HolderSpaceHDivRealOfNat : NormedAddCommGroup (C1HolderSpace E ((1:ℝ)/3)) := inferInstance
local instance instNormedSpaceRealC1HolderSpaceHDivOfNat : NormedSpace ℝ (C1HolderSpace E ((1:ℝ)/3)) := inferInstance

lemma compactHolderCauchy_exists (R : ℝ) (u : CompactHolderSpace E R) :
    ∃ v : C1HolderSpace E ((1:ℝ)/3), ∀ x,
      holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) v) x =
        cauchyTransform (compactHolderValue R u) x := by
  have hg := (compactHolderValue R u).continuous
  have hc := compactHolderValue_compactSupport R u
  have hM := compactHolderValue_bound R u
  have hH := compactHolderValue_holder R u
  obtain ⟨A,B,K,_,_,hK,hA,hB,hKf,hKD⟩ := cauchyTransform_holder_global
    hg hc hM (norm_nonneg u) hH
  refine ⟨c1HolderMk ((1:ℝ)/3) (cauchyTransform (compactHolderValue R u))
    (cauchyTransform_holder_contDiff_oneNecessity hg hc hM (norm_nonneg u) hH) A B K hK hA hB
    (by simpa only [dist_eq_norm] using hKf) (by simpa only [dist_eq_norm] using hKD),?_⟩
  intro x
  rfl

def compactHolderCauchy (R : ℝ) (u : CompactHolderSpace E R) : C1HolderSpace E ((1:ℝ)/3) :=
  Classical.choose (compactHolderCauchy_exists R u)

@[simp] theorem compactHolderCauchy_value (R : ℝ) (u : CompactHolderSpace E R) (x : ℂ) :
    holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) (compactHolderCauchy R u)) x =
      cauchyTransform (compactHolderValue R u) x := Classical.choose_spec (compactHolderCauchy_exists R u) x

 
def compactHolderCauchyLM (R : ℝ) : CompactHolderSpace E R →ₗ[ℝ] C1HolderSpace E ((1:ℝ)/3) where
  toFun := compactHolderCauchy R
  map_add' := by
    intro u v
    apply c1HolderValue_injective
    apply holderValue_injective
    apply BoundedContinuousFunction.ext
    intro x
    simp only [compactHolderCauchy_value,map_add,BoundedContinuousFunction.add_apply]
    exact congrFun (cauchyTransform_add_compact (compactHolderValue R u).continuous
      (compactHolderValue R v).continuous (compactHolderValue_compactSupport R u)
      (compactHolderValue_compactSupport R v)) x
  map_smul' := by
    intro c u
    apply c1HolderValue_injective
    apply holderValue_injective
    apply BoundedContinuousFunction.ext
    intro x
    simp only [compactHolderCauchy_value,map_smul,BoundedContinuousFunction.smul_apply,
      RingHom.id_apply]
    exact congrFun (cauchyTransform_real_smul c (compactHolderValue R u)) x

@[simp] lemma compactHolderCauchyLM_value (R : ℝ) (u : CompactHolderSpace E R) (x : ℂ) :
    holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) (compactHolderCauchyLM R u)) x =
      cauchyTransform (compactHolderValue R u) x := compactHolderCauchy_value R u x

lemma compactHolderCauchy_continuous (R : ℝ) : Continuous (compactHolderCauchyLM (E := E) R) := by
  apply (compactHolderCauchyLM (E := E) R).continuous_of_seq_closed_graph
  intro u v w huv huw
  apply c1HolderValue_injective
  apply holderValue_injective
  apply BoundedContinuousFunction.ext
  intro x
  let ev : C1HolderSpace E ((1:ℝ)/3) →L[ℝ] E :=
    (BoundedContinuousFunction.evalCLM ℝ x).comp
      ((holderValue ((1:ℝ)/3)).comp (c1HolderValue ((1:ℝ)/3)))
  have hw := (ev.continuous.tendsto w).comp huw
  change Tendsto (fun j => holderValue ((1:ℝ)/3)
    (c1HolderValue ((1:ℝ)/3) (compactHolderCauchyLM R (u j))) x) atTop
    (𝓝 (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) w) x)) at hw
  simp only [compactHolderCauchyLM_value] at hw
  obtain ⟨M,hM⟩ := (Metric.isBounded_range_of_tendsto u huv).exists_norm_le
  have hpoint (z : ℂ) : Tendsto (fun j => compactHolderValue R (u j) z) atTop
      (𝓝 (compactHolderValue R v z)) :=
    (((BoundedContinuousFunction.evalCLM ℝ z).comp (compactHolderValue R)).continuous.tendsto v).comp huv
  have ht := cauchyTransform_tendsto_compact_data (fun j => (compactHolderValue R (u j)).continuous)
    hpoint (fun j => compactHolderValue_support R (u j)) (compactHolderValue_support R v)
    (fun j z => (compactHolderValue_bound R (u j) z).trans (hM _ ⟨j,rfl⟩)) x
  rw [compactHolderCauchyLM_value]
  exact tendsto_nhds_unique hw ht

 
def compactHolderCauchyCLM (R : ℝ) : CompactHolderSpace E R →L[ℝ] C1HolderSpace E ((1:ℝ)/3) where
  toLinearMap := compactHolderCauchyLM R
  cont := compactHolderCauchy_continuous R

@[simp] theorem compactHolderCauchyCLM_value (R : ℝ) (u : CompactHolderSpace E R) (x : ℂ) :
    holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) (compactHolderCauchyCLM R u)) x =
      cauchyTransform (compactHolderValue R u) x := compactHolderCauchy_value R u x

end HigherDimensionalBallPacking.Rigidity

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
namespace HigherDimensionalBallPacking.Rigidity
variable {K E F : Type*} [MetricSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

 
def holderMap (α : ℝ) (L : E →L[ℝ] F) : HolderSpace K E α →L[ℝ] HolderSpace K F α :=
  (((L.compLeftContinuousBounded K).prodMap (L.compLeftContinuousBounded (OffDiagonal K))).comp
    (holderGraph K E α).subtypeL).codRestrict (holderGraph K F α) (by
      intro u z
      change L (holderValue α u z.val.1)-L (holderValue α u z.val.2) =
        (dist z.val.1 z.val.2)^α • L (holderDifference α u z)
      rw [← map_sub,holderSpace_relation α u z.val.1 z.val.2 z.property,map_smul])

@[simp] theorem holderMap_value (α : ℝ) (L : E →L[ℝ] F) (u : HolderSpace K E α) (x : K) :
    holderValue α (holderMap α L u) x = L (holderValue α u x) := rfl

variable [CompleteSpace E] [CompleteSpace F]

def compactHolderMap (R : ℝ) (L : E →L[ℝ] F) : CompactHolderSpace E R →L[ℝ] CompactHolderSpace F R :=
  ((holderMap ((1:ℝ)/3) L).comp (compactHolderSubmodule R).subtypeL).codRestrict
    (compactHolderSubmodule R) (by
      intro u x hx
      change L (holderValue ((1:ℝ)/3) u.val x)=0
      rw [u.property x hx,map_zero])

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem compactHolderMap_value (R : ℝ) (L : E →L[ℝ] F) (u : CompactHolderSpace E R) (x : ℂ) :
    compactHolderValue R (compactHolderMap R L u) x = L (compactHolderValue R u x) := rfl

end HigherDimensionalBallPacking.Rigidity

open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter
namespace HigherDimensionalBallPacking.Rigidity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

 
def compactCRInverse (R : ℝ) : CompactHolderSpace E R →L[ℝ] C1HolderSpace E ((1:ℝ)/3) :=
  (compactHolderCauchyCLM R).comp
    (compactHolderMap R (((Complex.I/2) • ContinuousLinearMap.id ℂ E).restrictScalars ℝ))

def compactCRInverseValue (R : ℝ) (u : CompactHolderSpace E R) : ℂ →ᵇ E :=
  holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) (compactCRInverse R u))

@[simp] lemma compactCRInverseValue_apply (R : ℝ) (u : CompactHolderSpace E R) (x : ℂ) :
    compactCRInverseValue R u x = cauchyTransform (fun z => (Complex.I/2) • compactHolderValue R u z) x := by
  exact compactHolderCauchyCLM_value R _ x

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_FrameFredholm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl )
open SymplecticBallPacking.Hamiltonian (Plane )
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
namespace HigherDimensionalBallPacking.Rigidity
section
universe v
variable {E F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def c1LowerOrderCLM (M : HolderSpace ℂ (E →L[ℝ] F) ((1:ℝ)/3)) :
    C1HolderSpace E ((1:ℝ)/3) →L[ℝ] HolderSpace ℂ F ((1:ℝ)/3) :=
  (holderCLM ((1:ℝ)/3) M).comp (c1HolderValue ((1:ℝ)/3))

@[simp] lemma c1LowerOrderCLM_value (M : HolderSpace ℂ (E →L[ℝ] F) ((1:ℝ)/3))
    (u : C1HolderSpace E ((1:ℝ)/3)) (x : ℂ) :
    holderValue ((1:ℝ)/3) (c1LowerOrderCLM M u) x =
      holderValue ((1:ℝ)/3) M x (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) u) x) := rfl

end

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
section
universe v
variable {E X : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup X] [NormedSpace ℝ X]


def holderConstantCLM (α : ℝ) : E →L[ℝ] HolderSpace ℂ E α :=
  LinearMap.mkContinuous
    { toFun := fun c => ⟨(BoundedContinuousFunction.const ℂ c,0),by intro z;simp⟩
      map_add' := fun c d => by apply holderValue_injective α; ext z; rfl
      map_smul' := fun c d => by apply holderValue_injective α; ext z; rfl }
    1 (fun c => by
      change max ‖BoundedContinuousFunction.const ℂ c‖ ‖(0 : OffDiagonal ℂ →ᵇ E)‖ ≤ 1*‖c‖
      rw [norm_zero,one_mul]
      exact max_le (BoundedContinuousFunction.norm_const_le c) (norm_nonneg c))

omit [CompleteSpace E] in
@[simp] lemma holderConstantCLM_value (α : ℝ) (c : E) (z : ℂ) :
    holderValue α (holderConstantCLM α c) z=c := rfl

def c1HolderEval (α : ℝ) (z : ℂ) : C1HolderSpace E α →L[ℝ] E :=
  (BoundedContinuousFunction.evalCLM ℝ z).comp ((holderValue α).comp (c1HolderValue α))

@[simp] lemma c1HolderEval_apply (α : ℝ) (z : ℂ) (u : C1HolderSpace E α) :
    c1HolderEval α z u=holderValue α (c1HolderValue α u) z := rfl



end

 

section
open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
universe u v
variable {K : Type u} [MetricSpace K]
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ E] in
theorem boundedLipschitz_holder_estimate (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (f : K →ᵇ E) {L : NNReal} (hf : LipschitzWith L f) (x y : K) :
    ‖f x-f y‖ ≤ ((L:ℝ)+2*‖f‖)*(dist x y)^α := by
  by_cases hd : dist x y ≤ 1
  · have h := hf.dist_le_mul x y
    rw [dist_eq_norm] at h
    exact h.trans ((mul_le_mul_of_nonneg_left
      (Real.self_le_rpow_of_le_one dist_nonneg hd hα₁) L.coe_nonneg).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (Real.rpow_nonneg dist_nonneg α)))
  · have hr : 1≤(dist x y)^α := Real.one_le_rpow (le_of_not_ge hd) hα₀
    have hb : ‖f x-f y‖ ≤ 2*‖f‖ :=
      (norm_sub_le _ _).trans ((add_le_add (f.norm_coe_le_norm x) (f.norm_coe_le_norm y)).trans_eq (by ring))
    calc
      ‖f x-f y‖ ≤ 2*‖f‖ := hb
      _ ≤ (2*‖f‖)*(dist x y)^α := le_mul_of_one_le_right (by positivity) hr
      _ ≤ ((L:ℝ)+2*‖f‖)*(dist x y)^α :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left L.coe_nonneg) (Real.rpow_nonneg dist_nonneg α)

def holderOfLipschitz (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (f : K →ᵇ E) {L : NNReal} (hf : LipschitzWith L f) : HolderSpace K E α :=
  holderSpaceMk α f ((L:ℝ)+2*‖f‖) (by positivity)
    (boundedLipschitz_holder_estimate α hα₀ hα₁ f hf)

@[simp] theorem holderOfLipschitz_apply (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (f : K →ᵇ E) {L : NNReal} (hf : LipschitzWith L f) (x : K) :
    holderValue α (holderOfLipschitz α hα₀ hα₁ f hf) x = f x := rfl

def compactSmoothHolder (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) : HolderSpace E F α :=
  holderOfLipschitz α hα₀ hα₁ (compactCoefficient f hf.continuous hc)
    (Classical.choose_spec (ContDiff.lipschitzWith_of_hasCompactSupport hc hf (by simp)))

@[simp] theorem compactSmoothHolder_apply (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (x : E) :
    holderValue α (compactSmoothHolder α hα₀ hα₁ f hf hc) x = f x := rfl

end

 

 

open Set Function Filter Topology

 

 

open Set Function Filter Topology
open scoped NNReal

 

 

open scoped NNReal
open Set Function Filter Topology

 

 

open Set Function Filter Topology

 

 

open Set Function Filter Topology

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter

open scoped ContDiff Topology
open Set Function Filter

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_HolderCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl )
open SymplecticBallPacking.Hamiltonian (Plane )
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal

open scoped ContDiff Topology
open Set Function Filter

open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter



open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
namespace HigherDimensionalBallPacking.Rigidity
universe u v
variable {P : Type u} [TopologicalSpace P]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

abbrev UnitTime := Set.Icc (0:ℝ) 1

def unitExtend (f : C(UnitTime,F)) : C(ℝ,F) :=
  f.comp ⟨Set.projIcc 0 1 (by norm_num), continuous_projIcc⟩

omit [NormedSpace ℝ F] [CompleteSpace F] in
@[simp] theorem unitExtend_coe (f : C(UnitTime,F)) (t : UnitTime) :
    unitExtend f t = f t := by simp [unitExtend]

def unitMean : C(UnitTime,F) →L[ℝ] F :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ t in (0:ℝ)..1, unitExtend f t
      map_add' := by
        intro f g
        exact intervalIntegral.integral_add
          ((unitExtend f).continuous.intervalIntegrable _ _)
          ((unitExtend g).continuous.intervalIntegrable _ _)
      map_smul' := fun c f => intervalIntegral.integral_smul c _ }
    1 (by
      intro f
      change ‖∫ t in (0:ℝ)..1, unitExtend f t‖ ≤ 1*‖f‖
      simpa using intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (0:ℝ)) (b := 1) (fun t _ => f.norm_coe_le_norm (Set.projIcc 0 1 (by norm_num) t)))

omit [CompleteSpace F] in
theorem unitMean_norm (f : C(UnitTime,F)) : ‖unitMean f‖ ≤ ‖f‖ := by
  change ‖∫ t in (0:ℝ)..1, unitExtend f t‖ ≤ ‖f‖
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := 1) (fun t _ => f.norm_coe_le_norm (Set.projIcc 0 1 (by norm_num) t))

def sectionMean (g : (P × UnitTime) →ᵇ F) : P →ᵇ F :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p => unitMean (g.toContinuousMap.curry p))
    (unitMean.continuous.comp g.toContinuousMap.curry.continuous)
    ‖g‖ (by
      intro p
      exact (unitMean_norm _).trans ((ContinuousMap.norm_le _ (norm_nonneg g)).mpr
        (fun t => g.norm_coe_le_norm (p,t))))

omit [CompleteSpace F] in
@[simp] theorem sectionMean_apply (g : (P × UnitTime) →ᵇ F) (p : P) :
    sectionMean g p = ∫ t in (0:ℝ)..1, g (p,Set.projIcc 0 1 (by norm_num) t) := rfl

omit [CompleteSpace F] in
theorem sectionMean_norm (g : (P × UnitTime) →ᵇ F) : ‖sectionMean g‖ ≤ ‖g‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg g)).mpr
  intro p
  exact (unitMean_norm _).trans ((ContinuousMap.norm_le _ (norm_nonneg g)).mpr
    (fun t => g.norm_coe_le_norm (p,t)))

def sectionMeanCLM : ((P × UnitTime) →ᵇ F) →L[ℝ] (P →ᵇ F) :=
  LinearMap.mkContinuous
    { toFun := sectionMean
      map_add' := by
        intro f g
        ext p
        change unitMean ((f+g).toContinuousMap.curry p) = _
        change unitMean (f.toContinuousMap.curry p+g.toContinuousMap.curry p) = _
        exact unitMean.map_add _ _
      map_smul' := by
        intro c f
        ext p
        change unitMean (c • f.toContinuousMap.curry p) = _
        exact unitMean.map_smul c _ }
    1 (fun g => by
      change ‖sectionMean g‖ ≤ 1*‖g‖
      simpa only [one_mul] using sectionMean_norm g)

omit [CompleteSpace F] in
@[simp] theorem sectionMeanCLM_apply (g : (P × UnitTime) →ᵇ F) (p : P) :
    sectionMeanCLM g p = ∫ t in (0:ℝ)..1, g (p,Set.projIcc 0 1 (by norm_num) t) := rfl

end HigherDimensionalBallPacking.Rigidity

namespace HigherDimensionalBallPacking.Rigidity
universe u v
variable {K : Type u} [MetricSpace K]
variable {E F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance holderCalculusNormedAddCommGroup
    (G : Type v) [NormedAddCommGroup G] [NormedSpace ℝ G] (α : ℝ) :
    NormedAddCommGroup (HolderSpace K G α) := inferInstance



theorem compactCoefficient_lipschitz {f : E → F} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    LipschitzWith ‖compactCoefficient (fderiv ℝ f) (hf.continuous_fderiv (by simp)) (hc.fderiv ℝ)‖₊ f := by
  apply lipschitzWith_of_nnnorm_fderiv_le (hf.differentiable (by simp))
  intro x
  exact_mod_cast (compactCoefficient (fderiv ℝ f) (hf.continuous_fderiv (by simp))
    (hc.fderiv ℝ)).norm_coe_le_norm x

def holderPost (α : ℝ) (hα : 0<α) (f : E → F) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (u : HolderSpace K E α) : HolderSpace K F α :=
  holderSpaceMk α (superposeBCF (compactCoefficient f hf.continuous hc) 0 (holderValue α u))
    (‖compactCoefficient (fderiv ℝ f) (hf.continuous_fderiv (by simp)) (hc.fderiv ℝ)‖*‖u‖)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by
      intro x y
      change ‖f (0+holderValue α u x)-f (0+holderValue α u y)‖ ≤ _
      simp only [zero_add]
      exact ((compactCoefficient_lipschitz hf hc).norm_sub_le _ _).trans
        ((mul_le_mul_of_nonneg_left (holderSpace_estimate α hα u x y) (norm_nonneg _)).trans_eq
          (by rw [mul_assoc])))

@[simp] theorem holderPost_apply (α : ℝ) (hα : 0<α) (f : E → F) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (u : HolderSpace K E α) (x : K) :
    holderValue α (holderPost α hα f hf hc u) x = f (holderValue α u x) := by
  change f (0+holderValue α u x) = _
  rw [zero_add]

theorem segmentSection_bound (u : K →ᵇ E) (p : OffDiagonal K × UnitTime) :
    ‖u p.1.val.2 + (p.2 : ℝ) • (u p.1.val.1-u p.1.val.2)‖ ≤ 3*‖u‖ := by
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg p.2.property.1]
  have hs : ‖u p.1.val.1-u p.1.val.2‖ ≤ 2*‖u‖ :=
    (norm_sub_le _ _).trans (by linarith [u.norm_coe_le_norm p.1.val.1,u.norm_coe_le_norm p.1.val.2])
  have ht := mul_le_mul p.2.property.2 hs (norm_nonneg _) (show (0:ℝ)≤1 by norm_num)
  linarith [u.norm_coe_le_norm p.1.val.2]

 

def segmentSection : (K →ᵇ E) →L[ℝ] ((OffDiagonal K × UnitTime) →ᵇ E) :=
  LinearMap.mkContinuous
    { toFun := fun u => BoundedContinuousFunction.ofNormedAddCommGroup
        (fun p => u p.1.val.2 + (p.2 : ℝ) • (u p.1.val.1-u p.1.val.2))
        (by fun_prop) (3*‖u‖) (segmentSection_bound u)
      map_add' := by
        intro u v
        apply BoundedContinuousFunction.ext
        intro p
        change (u p.1.val.2+v p.1.val.2)+(p.2:ℝ) •
            ((u p.1.val.1+v p.1.val.1)-(u p.1.val.2+v p.1.val.2)) =
          (u p.1.val.2+(p.2:ℝ) • (u p.1.val.1-u p.1.val.2))+
          (v p.1.val.2+(p.2:ℝ) • (v p.1.val.1-v p.1.val.2))
        simp only [smul_add,smul_sub]
        abel
      map_smul' := by
        intro c u
        apply BoundedContinuousFunction.ext
        intro p
        change c • u p.1.val.2+(p.2:ℝ) • (c • u p.1.val.1-c • u p.1.val.2) =
          c • (u p.1.val.2+(p.2:ℝ) • (u p.1.val.1-u p.1.val.2))
        module }
    3 (fun u => BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _
      (by positivity) (segmentSection_bound u))

@[simp] theorem segmentSection_apply (u : K →ᵇ E) (p : OffDiagonal K × UnitTime) :
    segmentSection u p = u p.1.val.2 + (p.2 : ℝ) • (u p.1.val.1-u p.1.val.2) := rfl

def differencePull : (OffDiagonal K →ᵇ E) →L[ℝ] ((OffDiagonal K × UnitTime) →ᵇ E) :=
  BoundedContinuousFunction.compContinuousCLM E ℝ ⟨Prod.fst,continuous_fst⟩

@[simp] theorem differencePull_apply (v : OffDiagonal K →ᵇ E) (p : OffDiagonal K × UnitTime) :
    differencePull v p = v p.1 := rfl

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_NonlinearCR
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl )
open SymplecticBallPacking.Hamiltonian (Plane )
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction

namespace HigherDimensionalBallPacking.Rigidity
open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
universe u v
variable {K : Type u} [MetricSpace K]
variable {E F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def scalarSectionCLM (w : K →ᵇ ℝ) : (K →ᵇ E) →L[ℝ] (K →ᵇ E) :=
  LinearMap.mkContinuous
    { toFun := fun u => w • u
      map_add' := fun u v => smul_add w u v
      map_smul' := by
        intro c u
        ext x
        change w x • (c • u x) = c • (w x • u x)
        exact smul_comm _ _ _ }
    ‖w‖ (norm_smul_le w)

@[simp] theorem scalarSectionCLM_apply (w : K →ᵇ ℝ) (u : K →ᵇ E) (x : K) :
    scalarSectionCLM w u x = w x • u x := rfl

def pairDistance : C(OffDiagonal K,ℝ) :=
  ⟨fun p => dist p.val.1 p.val.2,
    (continuous_fst.comp continuous_subtype_val).dist (continuous_snd.comp continuous_subtype_val)⟩

@[simp] theorem pairDistance_apply (p : OffDiagonal K) :
    pairDistance p = dist p.val.1 p.val.2 := rfl

theorem pairDistance_pos (p : OffDiagonal K) : 0<pairDistance p := dist_pos.mpr p.property

def holderNearWeight : OffDiagonal K →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p => (1+pairDistance p)⁻¹)
    ((show Continuous (fun p : OffDiagonal K => (1:ℝ)+pairDistance p) from continuous_const.add pairDistance.continuous).inv₀ (fun p => by have hd := pairDistance_pos p; positivity))
    1 (fun p => by
      have hd := pairDistance_pos p
      rw [Real.norm_of_nonneg (by positivity)]
      exact inv_le_one_of_one_le₀ (by linarith [pairDistance_pos p]))

@[simp] theorem holderNearWeight_apply (p : OffDiagonal K) :
    holderNearWeight p = (1+pairDistance p)⁻¹ := rfl

theorem divided_rpow_le_one {d α : ℝ} (hd : 0<d) (hα₀ : 0≤α) (hα₁ : α≤1) :
    d^(1-α)/(1+d) ≤ 1 := by
  apply (div_le_one (by positivity : 0<1+d)).mpr
  by_cases h : d≤1
  · exact (Real.rpow_le_one hd.le h (by linarith)).trans (by linarith)
  · have hh := Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤d) (show 1-α≤1 by linarith)
    rw [Real.rpow_one] at hh
    exact hh.trans (by linarith)

def holderFarWeight (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1) : OffDiagonal K →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p => (pairDistance p)^(1-α)/(1+pairDistance p))
    ((pairDistance.continuous.rpow_const (fun p => Or.inl (pairDistance_pos p).ne')).div
      (continuous_const.add pairDistance.continuous) (fun p => by have hd := pairDistance_pos p; positivity))
    1 (fun p => by
      have hd := pairDistance_pos p
      rw [Real.norm_of_nonneg (by positivity)]
      exact divided_rpow_le_one (pairDistance_pos p) hα₀ hα₁)

@[simp] theorem holderFarWeight_apply (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1) (p : OffDiagonal K) :
    holderFarWeight α hα₀ hα₁ p = (pairDistance p)^(1-α)/(1+pairDistance p) := rfl

theorem holderFarWeight_relation (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1) (p : OffDiagonal K) :
    (pairDistance p)^α * holderFarWeight α hα₀ hα₁ p = 1-holderNearWeight p := by
  rw [holderFarWeight_apply,holderNearWeight_apply,← mul_div_assoc,
    ← Real.rpow_add (pairDistance_pos p)]
  rw [show α+(1-α)=1 by ring,Real.rpow_one]
  have hd := pairDistance_pos p
  field_simp [show (1+pairDistance p)≠0 by positivity]
  ring

def holderBaseDifference (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (base : C(K,E)) {L : NNReal} (hb : LipschitzWith L base) : OffDiagonal K →ᵇ E :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p => ((1+pairDistance p)⁻¹ * (pairDistance p)^(-α)) • (base p.val.1-base p.val.2))
    (by
      apply Continuous.smul
      · exact ((show Continuous (fun p : OffDiagonal K => (1:ℝ)+pairDistance p) from continuous_const.add pairDistance.continuous).inv₀ (fun p => by have hd := pairDistance_pos p; positivity)).mul
          (pairDistance.continuous.rpow_const (fun p => Or.inl (pairDistance_pos p).ne'))
      · exact (base.continuous.comp (continuous_fst.comp continuous_subtype_val)).sub
          (base.continuous.comp (continuous_snd.comp continuous_subtype_val)))
    L (fun p => by
      have hd := pairDistance_pos p
      rw [norm_smul,Real.norm_of_nonneg (by positivity)]
      have hh : ‖base p.val.1-base p.val.2‖ ≤ L*pairDistance p := by
        simpa only [dist_eq_norm,pairDistance_apply] using hb.dist_le_mul p.val.1 p.val.2
      refine (mul_le_mul_of_nonneg_left hh (by positivity)).trans ?_
      have he : (pairDistance p)^(-α)*pairDistance p = (pairDistance p)^(1-α) := by
        calc
          _ = (pairDistance p)^(-α)*(pairDistance p)^1 := by rw [Real.rpow_one]
          _ = (pairDistance p)^(-α+1) := (Real.rpow_add (pairDistance_pos p) (-α) 1).symm
          _ = _ := by congr 1; ring
      calc
        _ = L*((pairDistance p)^(1-α)/(1+pairDistance p)) := by rw [← he]; ring
        _ ≤ L*1 := mul_le_mul_of_nonneg_left
          (divided_rpow_le_one (pairDistance_pos p) hα₀ hα₁) L.property
        _ = L := mul_one _)

@[simp] theorem holderBaseDifference_apply (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (base : C(K,E)) {L : NNReal} (hb : LipschitzWith L base) (p : OffDiagonal K) :
    holderBaseDifference α hα₀ hα₁ base hb p =
      ((1+pairDistance p)⁻¹*(pairDistance p)^(-α)) • (base p.val.1-base p.val.2) := rfl

theorem holderBaseDifference_relation (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (base : C(K,E)) {L : NNReal} (hb : LipschitzWith L base) (p : OffDiagonal K) :
    (pairDistance p)^α • holderBaseDifference α hα₀ hα₁ base hb p =
      holderNearWeight p • (base p.val.1-base p.val.2) := by
  rw [holderBaseDifference_apply,holderNearWeight_apply,smul_smul]
  congr 1
  rw [mul_left_comm,← Real.rpow_add (pairDistance_pos p),add_neg_cancel,Real.rpow_zero,mul_one]

def baseSegment (base : C(K,E)) : C(OffDiagonal K × UnitTime,E) :=
  ⟨fun p => base p.1.val.2+(p.2:ℝ) • (base p.1.val.1-base p.1.val.2),by fun_prop⟩

@[simp] theorem baseSegment_apply (base : C(K,E)) (p : OffDiagonal K × UnitTime) :
    baseSegment base p = base p.1.val.2+(p.2:ℝ) • (base p.1.val.1-base p.1.val.2) := rfl

variable [CompleteSpace F]

def profileWeightedDifference (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (base : C(K,E)) {L : NNReal} (hb : LipschitzWith L base)
    (u : HolderSpace K E α) : OffDiagonal K →ᵇ E :=
  holderBaseDifference α hα₀ hα₁ base hb + scalarSectionCLM holderNearWeight (holderDifference α u)

theorem profileWeightedDifference_relation (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (base : C(K,E)) {L : NNReal} (hb : LipschitzWith L base)
    (u : HolderSpace K E α) (p : OffDiagonal K) :
    (pairDistance p)^α • profileWeightedDifference α hα₀ hα₁ base hb u p =
      holderNearWeight p • ((base p.val.1+holderValue α u p.val.1)-
        (base p.val.2+holderValue α u p.val.2)) := by
  change (pairDistance p)^α • (holderBaseDifference α hα₀ hα₁ base hb p +
    holderNearWeight p • holderDifference α u p) = _
  rw [smul_add,holderBaseDifference_relation,smul_comm ((pairDistance p)^α) (holderNearWeight p),
    ← show holderValue α u p.val.1-holderValue α u p.val.2 =
      (pairDistance p)^α • holderDifference α u p from u.property p]
  module

def profilePostDifference (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (base : C(K,E)) {L : NNReal} (hb : LipschitzWith L base)
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (u : HolderSpace K E α) : OffDiagonal K →ᵇ F :=
  sectionMeanCLM (sectionCLM (superposeBCF
    (compactCoefficient (fderiv ℝ f) (hf.continuous_fderiv (by simp)) (hc.fderiv ℝ))
    (baseSegment base) (segmentSection (holderValue α u)))
    (differencePull (profileWeightedDifference α hα₀ hα₁ base hb u))) +
  scalarSectionCLM (holderFarWeight α hα₀ hα₁)
    (pairLeft F (superposeBCF (compactCoefficient f hf.continuous hc) base (holderValue α u)) -
      pairRight F (superposeBCF (compactCoefficient f hf.continuous hc) base (holderValue α u)))

theorem segment_fderiv_integral (f : E → F) (hf : ContDiff ℝ ∞ f) (a b : E) :
    (∫ t in (0:ℝ)..1, fderiv ℝ f (a+t • (b-a)) (b-a)) = f b-f a := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => f (a+t • (b-a)))
      (fderiv ℝ f (a+t • (b-a)) (b-a)) t :=
    ((hf.differentiable (by simp)) (a+t • (b-a))).hasFDerivAt.comp_hasDerivAt t
      (by simpa only [one_smul,id_eq] using ((hasDerivAt_id t).smul_const (b-a)).const_add a)
  have hi : IntervalIntegrable (fun t : ℝ => fderiv ℝ f (a+t • (b-a)) (b-a))
      MeasureTheory.volume 0 1 :=
    (((hf.continuous_fderiv (by simp)).comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply
      continuous_const).intervalIntegrable _ _
  simpa only [one_smul,zero_smul,add_zero,add_sub_cancel] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi

omit [CompleteSpace F] in
theorem profilePostDifference_integral (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (base : C(K,E)) {L : NNReal} (hb : LipschitzWith L base)
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (u : HolderSpace K E α) (p : OffDiagonal K) :
    profilePostDifference α hα₀ hα₁ base hb f hf hc u p =
      (∫ t in (0:ℝ)..1,
        fderiv ℝ f (base p.val.2+holderValue α u p.val.2 +
          t • ((base p.val.1+holderValue α u p.val.1)-(base p.val.2+holderValue α u p.val.2)))
          (profileWeightedDifference α hα₀ hα₁ base hb u p)) +
      holderFarWeight α hα₀ hα₁ p • (f (base p.val.1+holderValue α u p.val.1)-
        f (base p.val.2+holderValue α u p.val.2)) := by
  change (∫ t in (0:ℝ)..1, (fderiv ℝ f)
    (baseSegment base (p,Set.projIcc 0 1 (by norm_num) t) +
      segmentSection (holderValue α u) (p,Set.projIcc 0 1 (by norm_num) t))
    (profileWeightedDifference α hα₀ hα₁ base hb u p)) + _ = _
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0:ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0:ℝ)≤1)] using ht
  dsimp only
  rw [Set.projIcc_of_mem (by norm_num : (0:ℝ)≤1) ht']
  congr 2
  simp only [baseSegment_apply,segmentSection_apply]
  module

theorem profilePostDifference_relation (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (base : C(K,E)) {L : NNReal} (hb : LipschitzWith L base)
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (u : HolderSpace K E α) (p : OffDiagonal K) :
    (pairDistance p)^α • profilePostDifference α hα₀ hα₁ base hb f hf hc u p =
      f (base p.val.1+holderValue α u p.val.1)-f (base p.val.2+holderValue α u p.val.2) := by
  let a := base p.val.2+holderValue α u p.val.2
  let b := base p.val.1+holderValue α u p.val.1
  rw [profilePostDifference_integral,smul_add,smul_smul,holderFarWeight_relation,
    ← intervalIntegral.integral_smul]
  change (∫ t in (0:ℝ)..1, (pairDistance p)^α •
    fderiv ℝ f (a+t • (b-a)) (profileWeightedDifference α hα₀ hα₁ base hb u p)) +
      (1-holderNearWeight p) • (f b-f a) = f b-f a
  have he : (∫ t in (0:ℝ)..1, (pairDistance p)^α •
      fderiv ℝ f (a+t • (b-a)) (profileWeightedDifference α hα₀ hα₁ base hb u p)) =
        holderNearWeight p • (f b-f a) := by
    rw [← segment_fderiv_integral f hf a b,← intervalIntegral.integral_smul]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [← map_smul,profileWeightedDifference_relation,map_smul]
  rw [he]
  module

def holderProfilePost (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (base : C(K,E)) {L : NNReal} (hb : LipschitzWith L base)
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (u : HolderSpace K E α) : HolderSpace K F α :=
  ⟨(superposeBCF (compactCoefficient f hf.continuous hc) base (holderValue α u),
    profilePostDifference α hα₀ hα₁ base hb f hf hc u),
    fun p => (profilePostDifference_relation α hα₀ hα₁ base hb f hf hc u p).symm⟩

@[simp] theorem holderProfilePost_apply (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (base : C(K,E)) {L : NNReal} (hb : LipschitzWith L base)
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (u : HolderSpace K E α) (x : K) :
    holderValue α (holderProfilePost α hα₀ hα₁ base hb f hf hc u) x =
      f (base x+holderValue α u x) := rfl

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_SquareBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl )
open SymplecticBallPacking.Hamiltonian (Plane )
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
namespace HigherDimensionalBallPacking.Rigidity

def decayRatio (C : ℝ) : ℝ := 64*C/(1+64*C)








open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian








open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian








open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end


