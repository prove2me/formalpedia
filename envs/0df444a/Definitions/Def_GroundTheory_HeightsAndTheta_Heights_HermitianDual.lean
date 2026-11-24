-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianDual
-- name    : GroundTheory_HeightsAndTheta_Heights_HermitianDual
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:10:26.31567+00:00
-- url     : https://prove2.me/theorems/f01b001e-46f0-4029-9d35-0eaa0dd4c235
-- title:
--   Hermitian Dual
-- statement:
--   Definitions and structural lemmas for Hermitian Dual, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HermitianDual.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianTensor
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FibreSpace_inner_equiv_9aa4479f01dc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
universe u
namespace GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt
noncomputable section
variable {K : Type*} [Field K]
section DualCoord
variable (σ : K →+* ℂ) (E : Type*) [AddCommGroup E] [Module (𝓞 K) E]
def dualCoord :
    Fibre σ (Module.Dual (𝓞 K) E) →ₗ[ComplexAt σ] Module.Dual (ComplexAt σ) (Fibre σ E) :=
  LinearMap.liftBaseChange (ComplexAt σ) (Module.Dual.baseChange (ComplexAt σ))
variable {σ E}
theorem dualCoord_tmul_tmul (z w : ComplexAt σ) (φ : Module.Dual (𝓞 K) E) (e : E) :
    dualCoord σ E (z ⊗ₜ φ) (w ⊗ₜ e) = z * (algebraMap (𝓞 K) (ComplexAt σ) (φ e) * w) := by
  rw [dualCoord, LinearMap.liftBaseChange_tmul, LinearMap.smul_apply,
    Module.Dual.baseChange_apply_tmul, smul_eq_mul, Algebra.smul_def]
theorem dualCoord_injective [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E] :
    Function.Injective (dualCoord σ E) := by
  classical
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' (𝓞 K) E
  obtain ⟨s, hs⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hf)
  let φ : Fin n → Module.Dual (𝓞 K) E := fun i ↦ LinearMap.proj i ∘ₗ s
  let g : Fin n → E := fun i ↦ f (fun j ↦ if i = j then 1 else 0)
  have hdecomp : ∀ e : E, ∑ i, φ i e • g i = e := by
    intro e
    have h1 : f (s e) = e := by rw [← LinearMap.comp_apply, hs, LinearMap.id_apply]
    conv_rhs => rw [← h1, LinearMap.pi_apply_eq_sum_univ f (s e)]
    rfl
  have hψ : ∀ ψ : Module.Dual (𝓞 K) E, ∑ i, ψ (g i) • φ i = ψ := by
    intro ψ
    refine LinearMap.ext fun e ↦ ?_
    rw [LinearMap.sum_apply]
    conv_rhs => rw [← hdecomp e]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul, mul_comm]
  have hrec : ∀ x, ∑ i, dualCoord σ E x (1 ⊗ₜ g i) ⊗ₜ φ i = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero, LinearMap.zero_apply, zero_tmul, Finset.sum_const_zero]
    | add x y hx hy =>
      simp only [map_add, LinearMap.add_apply, add_tmul, Finset.sum_add_distrib, hx, hy]
    | tmul z ψ =>
      conv_rhs => rw [← hψ ψ]
      rw [tmul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [dualCoord_tmul_tmul, mul_one, ← smul_tmul, Algebra.smul_def, mul_comm]
  intro x y hxy
  rw [← hrec x, ← hrec y, hxy]
theorem dualCoord_conjMap (x : Fibre σ (Module.Dual (𝓞 K) E)) (u : Fibre σ E) :
    dualCoord (conjugate σ) E (conjMap σ _ x) (conjMap σ E u) = conj σ (dualCoord σ E x u) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul z φ =>
    induction u using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add u v hu hv => simp only [map_add, hu, hv]
    | tmul w e =>
      rw [conjMap_tmul, conjMap_tmul, dualCoord_tmul_tmul, dualCoord_tmul_tmul, map_mul, map_mul]
      rfl
theorem conjMap_surjective : Function.Surjective (conjMap σ E) := by
  intro v
  induction v using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | add v v' hv hv' =>
    obtain ⟨u, rfl⟩ := hv
    obtain ⟨u', rfl⟩ := hv'
    exact ⟨u + u', map_add _ _ _⟩
  | tmul w e =>
    refine ⟨ofComplex σ (starRingEnd ℂ ((ofComplex (conjugate σ)).symm w)) ⊗ₜ e, ?_⟩
    rw [conjMap_tmul, conj_ofComplex, Complex.conj_conj]
    rfl
end DualCoord
variable [NumberField K]
variable {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E]
omit [NumberField K] [Module.Projective (𝓞 K) E] in

theorem fibre_finite (σ : K →+* ℂ) : Module.Finite ℂ (Fibre σ E) := by
  have : Module.Finite ℂ (ComplexAt σ) := Module.Finite.equiv (ofComplex σ).toLinearEquiv
  exact Module.Finite.trans (ComplexAt σ) (Fibre σ E)
variable (h : HermitianMetric K E)
instance (σ : K →+* ℂ) : FiniteDimensional ℂ (FibreSpace h σ) := fibre_finite (E := E) σ
instance (σ : K →+* ℂ) : CompleteSpace (FibreSpace h σ) := FiniteDimensional.complete ℂ _
def dualFunctional (σ : K →+* ℂ) (x : Fibre σ (Module.Dual (𝓞 K) E)) :
    StrongDual ℂ (FibreSpace h σ) :=
  LinearMap.toContinuousLinearMap ((ofComplex σ).symm.toLinearMap ∘ₗ
    ((dualCoord σ E x).restrictScalars ℂ) ∘ₗ (FibreSpace.equiv h σ).symm.toLinearMap)
def riesz (σ : K →+* ℂ) (x : Fibre σ (Module.Dual (𝓞 K) E)) : FibreSpace h σ :=
  (InnerProductSpace.toDual ℂ (FibreSpace h σ)).symm (dualFunctional h σ x)
theorem inner_riesz (σ : K →+* ℂ) (x : Fibre σ (Module.Dual (𝓞 K) E)) (v : FibreSpace h σ) :
    inner ℂ (riesz h σ x) v =
      (ofComplex σ).symm (dualCoord σ E x ((FibreSpace.equiv h σ).symm v)) := by
  rw [riesz, InnerProductSpace.toDual_symm_apply]
  rfl
theorem riesz_add (σ : K →+* ℂ) (x y : Fibre σ (Module.Dual (𝓞 K) E)) :
    riesz h σ (x + y) = riesz h σ x + riesz h σ y := by
  refine ext_inner_right ℂ fun v ↦ ?_
  rw [inner_add_left, inner_riesz, inner_riesz, inner_riesz, map_add, LinearMap.add_apply, map_add]
theorem riesz_smul (σ : K →+* ℂ) (c : ℂ) (x : Fibre σ (Module.Dual (𝓞 K) E)) :
    riesz h σ (c • x) = starRingEnd ℂ c • riesz h σ x := by
  refine ext_inner_right ℂ fun v ↦ ?_
  have hc : c • x = ofComplex σ c • x := by
    rw [fibre_smul_eq σ _ (ofComplex σ c) x, AlgEquiv.symm_apply_apply]
  rw [inner_smul_left, Complex.conj_conj, inner_riesz, inner_riesz, hc, map_smul,
    LinearMap.smul_apply, smul_eq_mul, map_mul, AlgEquiv.symm_apply_apply]
theorem riesz_eq_zero (σ : K →+* ℂ) (x : Fibre σ (Module.Dual (𝓞 K) E)) (hx : riesz h σ x = 0) :
    x = 0 := by
  refine dualCoord_injective (σ := σ) ?_
  rw [map_zero]
  refine LinearMap.ext fun u ↦ ?_
  have := inner_riesz h σ x (FibreSpace.equiv h σ u)
  rw [hx, inner_zero_left, LinearEquiv.symm_apply_apply] at this
  rw [LinearMap.zero_apply]
  exact (ofComplex σ).symm.injective (by rw [← this, map_zero])
@[instance_reducible]
def dualCore (σ : K →+* ℂ) : InnerProductSpace.Core ℂ (Fibre σ (Module.Dual (𝓞 K) E)) where
  inner x y := inner ℂ (riesz h σ y) (riesz h σ x)
  conj_inner_symm x y := inner_conj_symm _ _
  re_inner_nonneg x := inner_self_nonneg
  add_left x y z := by rw [riesz_add, inner_add_right]
  smul_left x y r := by rw [riesz_smul, inner_smul_right]
  definite x hx := riesz_eq_zero h σ x (inner_self_eq_zero.mp hx)
theorem riesz_conjMap (σ : K →+* ℂ) (x : Fibre σ (Module.Dual (𝓞 K) E)) :
    riesz h (conjugate σ) (conjMap σ _ x) =
      FibreSpace.equiv h (conjugate σ)
        (conjMap σ E ((FibreSpace.equiv h σ).symm (riesz h σ x))) := by
  refine ext_inner_right ℂ fun v ↦ ?_
  obtain ⟨u, hu⟩ := conjMap_surjective (σ := σ) ((FibreSpace.equiv h (conjugate σ)).symm v)
  have hv : v = FibreSpace.equiv h (conjugate σ) (conjMap σ E u) := by
    rw [hu, LinearEquiv.apply_symm_apply]
  rw [inner_riesz, hv, LinearEquiv.symm_apply_apply, dualCoord_conjMap, FibreSpace.inner_equiv,
    h.form_conj]
  rw [← FibreSpace.inner_equiv, LinearEquiv.apply_symm_apply, inner_riesz,
    LinearEquiv.symm_apply_apply]
  rfl
def HermitianMetric.dual : HermitianMetric K (Module.Dual (𝓞 K) E) where
  form σ := dualCore h σ
  form_conj σ x y := by
    change inner ℂ (riesz h _ (conjMap σ _ y)) (riesz h _ (conjMap σ _ x)) =
      starRingEnd ℂ (inner ℂ (riesz h σ y) (riesz h σ x))
    rw [riesz_conjMap, riesz_conjMap, FibreSpace.inner_equiv, h.form_conj]
    rfl
def HermitianBundle.dual {K : Type u} [Field K] [NumberField K] (A : HermitianBundle.{u} K) :
    HermitianBundle.{u} K :=
  ⟨Module.Dual (𝓞 K) A.carrier, A.metric.dual⟩
example : HermitianBundle GaussianField := (gaussianStandard 2).dual
end
end GroundTheory.Heights₂.Heights


