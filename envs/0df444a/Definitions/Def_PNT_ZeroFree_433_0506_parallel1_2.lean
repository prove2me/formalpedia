-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0506_parallel1_2
-- name    : PNT_ZeroFree_433_0506_parallel1_2
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T11:13:52.191695+00:00
-- url     : https://prove2.me/theorems/b0d996c8-9338-480a-8ed6-66c832f4f2aa
-- title:
--   Zero-free region foundations: Detector.GramPeriodicPoisson [0506_parallel1_2]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Detector.GramPeriodicPoisson
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Detector/GramPeriodicPoisson.lean#L386-L645

import Definitions.Def_PNT_ZeroFree_433_0506_parallel1_1

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Detector/GramPeriodicPoisson.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical FourierTransform SchwartzMap RealInnerProductSpace

namespace ProbeGramPeriodicPoisson


open scoped LineDeriv


open EisensteinSchwartzPoisson hiding O


def cartesianPoint (p : ℤ × ℤ) : ℂ := complexPoint (p.1:ℝ) (p.2:ℝ)

theorem joint_cartesian_summable_norm (W : 𝓢(Joint, ℂ)) :
    Summable (fun p : (ℤ × ℤ) × (ℤ × ℤ) =>
      ‖W (point (cartesianPoint p.1) (cartesianPoint p.2))‖) := by
  have hs := planeMajorant_cartesian_summable.mul_of_nonneg
    planeMajorant_cartesian_summable
    (fun _ => by unfold planeMajorant; positivity)
    (fun _ => by unfold planeMajorant; positivity)
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun _ => norm_le_product_majorant W _ _) (hs.mul_left (productDecayConstant W))

theorem partialFourier_cartesian_summable_norm (W : 𝓢(Joint, ℂ)) :
    Summable (fun p : (ℤ × ℤ) × (ℤ × ℤ) =>
      ‖partialFourier W (cartesianPoint p.2) (cartesianPoint p.1)‖) := by
  have hs := planeMajorant_cartesian_summable.mul_of_nonneg
    planeMajorant_cartesian_summable
    (fun _ => by unfold planeMajorant; positivity)
    (fun _ => by unfold planeMajorant; positivity)
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun _ => norm_partialFourier_le W _ _) (hs.mul_left (secondDecayBound (𝓕 W)))

theorem rightSlice_isometry (x : ℂ) : Isometry (fun y : ℂ => point x y) := by
  apply Isometry.of_dist_eq
  intro y z
  simp only [dist_eq_norm, point_eq_add, add_sub_add_left_eq_sub, ← map_sub]
  exact WithLp.norm_toLp_snd 2 ℂ ℂ (y-z)

def rightSlice (W : 𝓢(Joint, ℂ)) (x : ℂ) : 𝓢(ℂ, ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ
    (by simp only [point_eq_add]; fun_prop : (fun y : ℂ => point x y).HasTemperateGrowth)
    (rightSlice_isometry x).antilipschitz W

@[simp] theorem rightSlice_apply (W : 𝓢(Joint, ℂ)) (x y : ℂ) :
    rightSlice W x y = W (point x y) := rfl

theorem rightSlice_poisson (W : 𝓢(Joint, ℂ)) (x : ℂ) :
    (∑' p : ℤ × ℤ, W (point x (cartesianPoint p))) =
      ∑' p : ℤ × ℤ, partialFourier W (cartesianPoint p) x := by
  have h := integer_pair_poisson (rightSlice W x)
  have hcoe : (rightSlice W x : ℂ → ℂ) = fun y => W (point x y) := rfl
  simpa only [rightSlice_apply, SchwartzMap.fourier_coe, hcoe, partialFourier, cartesianPoint] using h


def blockMap (A : ℂ ≃L[ℝ] ℂ) : Joint ≃L[ℝ] Joint :=
  ((A.toLinearEquiv.prodCongr A.toLinearEquiv).withLpCongr 2).toContinuousLinearEquiv

@[simp] theorem blockMap_apply (A : ℂ ≃L[ℝ] ℂ) (z : Joint) :
    blockMap A z = point (A z.fst) (A z.snd) := rfl

@[simp] theorem blockMap_symm_apply (A : ℂ ≃L[ℝ] ℂ) (z : Joint) :
    (blockMap A).symm z = point (A.symm z.fst) (A.symm z.snd) := rfl

theorem blockMap_det (A : ℂ ≃L[ℝ] ℂ) :
    LinearMap.det (blockMap A : Joint →ₗ[ℝ] Joint) =
      LinearMap.det (A : ℂ →ₗ[ℝ] ℂ) ^ 2 := by
  have h := LinearMap.det_conj
    ((A : ℂ →ₗ[ℝ] ℂ).prodMap (A : ℂ →ₗ[ℝ] ℂ))
    (WithLp.linearEquiv 2 ℝ (ℂ × ℂ)).symm
  rw [LinearMap.det_prodMap] at h
  convert! h using 1 <;> first | rfl | ring

def jointInverseJacobian (A : Joint ≃L[ℝ] Joint) : ℝ :=
  |(LinearMap.det (A : Joint →ₗ[ℝ] Joint))⁻¹|

theorem jointInverseJacobian_blockMap (A : ℂ ≃L[ℝ] ℂ) :
    jointInverseJacobian (blockMap A) = inverseJacobian A ^ 2 := by
  rw [jointInverseJacobian, blockMap_det, ← inv_pow, abs_pow]
  rfl

def jointDual (A : Joint ≃L[ℝ] Joint) : Joint →L[ℝ] Joint :=
  A.symm.toContinuousLinearMap.adjoint

theorem joint_inner_linear_dual (A : Joint ≃L[ℝ] Joint) (x y : Joint) :
    inner ℝ (A x) (jointDual A y) = inner ℝ x y := by
  rw [jointDual, ContinuousLinearMap.adjoint_inner_right]
  simp

theorem jointDual_blockMap (A : ℂ ≃L[ℝ] ℂ) (ξ η : ℂ) :
    jointDual (blockMap A) (point ξ η) = point (dualMap A ξ) (dualMap A η) := by
  apply ext_inner_left ℝ
  intro z
  rw [jointDual, ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ (point (A.symm z.fst) (A.symm z.snd)) (point ξ η) = _
  simp only [point, WithLp.prod_inner_apply, dualMap,
    ContinuousLinearMap.adjoint_inner_right]
  rfl

theorem joint_integral_comp_linearEquiv (A : Joint ≃L[ℝ] Joint) (f : Joint → ℂ) :
    (∫ x : Joint, f (A x)) = jointInverseJacobian A • ∫ x : Joint, f x := by
  have h := integral_map_equiv («μ» := (volume : Measure Joint))
    A.toHomeomorph.toMeasurableEquiv f
  have hm : Measure.map A (volume : Measure Joint) =
      ENNReal.ofReal (jointInverseJacobian A) • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume A.toLinearEquiv.isUnit_det'.ne_zero
  change (∫ y : Joint, f y ∂Measure.map A volume) = (∫ x : Joint, f (A x)) at h
  rw [hm, integral_smul_measure, ENNReal.toReal_ofReal
    (show 0 ≤ jointInverseJacobian A from abs_nonneg _)] at h
  exact h.symm

theorem joint_fourier_comp_linearEquiv (A : Joint ≃L[ℝ] Joint)
    (f : Joint → ℂ) (w : Joint) :
    𝓕 (f ∘ A) w = jointInverseJacobian A • 𝓕 f (jointDual A w) := by
  let H : Joint → ℂ := fun z => Real.fourierChar (-inner ℝ z (jointDual A w)) • f z
  calc
    𝓕 (f ∘ A) w = ∫ x : Joint, H (A x) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        simp only [H, joint_inner_linear_dual, Function.comp_apply]
        rfl
    _ = jointInverseJacobian A • ∫ z : Joint, H z := joint_integral_comp_linearEquiv A H
    _ = _ := rfl

def jointTranslate (W : 𝓢(Joint, ℂ)) (b : Joint) : 𝓢(Joint, ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (g := fun z : Joint => z+b)
    (by fun_prop) (isometry_add_right b).antilipschitz W

def jointAffine (W : 𝓢(Joint, ℂ)) (A : Joint ≃L[ℝ] Joint) (b : Joint) : 𝓢(Joint, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A (jointTranslate W b)

@[simp] theorem jointAffine_apply (W : 𝓢(Joint, ℂ)) (A : Joint ≃L[ℝ] Joint) (b z : Joint) :
    jointAffine W A b z = W (A z+b) := rfl

theorem joint_fourier_affine (W : 𝓢(Joint, ℂ)) (A : Joint ≃L[ℝ] Joint) (b w : Joint) :
    (𝓕 (jointAffine W A b)) w =
      jointInverseJacobian A •
        (Real.fourierChar (inner ℝ b (jointDual A w)) • (𝓕 W) (jointDual A w)) := by
  rw [congrFun (SchwartzMap.fourier_coe _) w]
  change 𝓕 ((fun z => W (z+b)) ∘ A) w = _
  rw [joint_fourier_comp_linearEquiv]
  have ht : 𝓕 (fun z => W (z+b)) (jointDual A w) =
      Real.fourierChar (inner ℝ b (jointDual A w)) • 𝓕 (W : Joint → ℂ) (jointDual A w) :=
    congrFun (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar
      (volume : Measure Joint) (innerₗ Joint) (W : Joint → ℂ) b) (jointDual A w)
  rw [ht]
  rw [congrFun (SchwartzMap.fourier_coe W) (jointDual A w)]


def jointFrequency (c : ℂ) (hc : c ≠ 0) (p : (ℤ × ℤ) × (ℤ × ℤ)) : Joint :=
  point (eisensteinDualFrequency c hc p.1) (eisensteinDualFrequency c hc p.2)

open ActualEisensteinCubic ConcreteTraceCRT


theorem joint_dual_summable_norm (W : 𝓢(Joint, ℂ)) (A : Joint ≃L[ℝ] Joint) :
    Summable (fun p : (ℤ × ℤ) × (ℤ × ℤ) =>
      ‖(𝓕 W) (jointDual A (point (cartesianPoint p.1) (cartesianPoint p.2)))‖) := by
  have hJ : 0 < jointInverseJacobian A :=
    abs_pos.mpr (inv_ne_zero A.toLinearEquiv.isUnit_det'.ne_zero)
  have hs := joint_cartesian_summable_norm (𝓕 (jointAffine W A 0))
  have hn (p : (ℤ × ℤ) × (ℤ × ℤ)) :
      ‖(𝓕 (jointAffine W A 0)) (point (cartesianPoint p.1) (cartesianPoint p.2))‖ =
      jointInverseJacobian A *
        ‖(𝓕 W) (jointDual A (point (cartesianPoint p.1) (cartesianPoint p.2)))‖ := by
    rw [joint_fourier_affine]
    simp [abs_of_pos hJ]
  simp_rw [hn] at hs
  have hi := hs.mul_left (jointInverseJacobian A)⁻¹
  simpa only [← mul_assoc, inv_mul_cancel₀ hJ.ne', one_mul] using hi

theorem jointFrequency_summable_norm (W : 𝓢(Joint, ℂ)) (c : ℂ) (hc : c ≠ 0) :
    Summable (fun p : (ℤ × ℤ) × (ℤ × ℤ) => ‖(𝓕 W) (jointFrequency c hc p)‖) := by
  have h := joint_dual_summable_norm W (blockMap (eisensteinLatticeMap c hc))
  simpa only [jointDual_blockMap, jointFrequency, eisensteinDualFrequency, cartesianPoint] using h

abbrev Residue (c : O) := O ⧸ Ideal.span {c}

def quotientPair (c : O) (m : O × O) : Residue c × Residue c :=
  (Ideal.Quotient.mk (Ideal.span {c}) m.1, Ideal.Quotient.mk (Ideal.span {c}) m.2)

def representativePair (c : O) (r : Residue c × Residue c) : O × O :=
  (GaussianShiftedPartition.representative c r.1, GaussianShiftedPartition.representative c r.2)


end ProbeGramPeriodicPoisson

end

end OAI

end


