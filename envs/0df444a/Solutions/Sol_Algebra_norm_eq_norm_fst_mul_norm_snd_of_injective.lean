-- Prove2me | solution 1 for Algebra.norm_eq_norm_fst_mul_norm_snd_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/e72aa5bb-5bf6-5831-b5af-b7ec26704def

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_norm_eq_norm_fst_mul_norm_snd_of_injective

set_option autoImplicit false

open TensorProduct

namespace LinearMap p2m_export "LinearMap" "det_baseChange rank ext comp_assoc baseChange linearEquivOfInjective det_conj baseChange_comp det_prodMap id_comp conjugate" end LinearMap
p2m_open_scoped "LinearMap" in

theorem LinearMap.det_eq_det_of_injective_of_comp_eq
    {A M N : Type*} [CommRing A] [IsDomain A] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [Module.Free A M] [Module.Finite A M] [Module.Free A N] [Module.Finite A N]
    (f : M →ₗ[A] N) (hf : Function.Injective f) (hrank : Module.finrank A M = Module.finrank A N)
    (u : M →ₗ[A] M) (v : N →ₗ[A] N) (h : f ∘ₗ u = v ∘ₗ f) :
    LinearMap.det u = LinearMap.det v := by
  let K := FractionRing A
  apply IsFractionRing.injective A K
  rw [← LinearMap.det_baseChange, ← LinearMap.det_baseChange]
  have hinj : Function.Injective (f.baseChange K) := Module.Flat.lTensor_preserves_injective_linearMap _ hf
  have hdim : Module.finrank K (K ⊗[A] M) = Module.finrank K (K ⊗[A] N) := by
    rw [Module.finrank_baseChange, Module.finrank_baseChange, hrank]
  let e : K ⊗[A] M ≃ₗ[K] K ⊗[A] N := LinearMap.linearEquivOfInjective _ hinj hdim
  have he : (e : K ⊗[A] M →ₗ[K] K ⊗[A] N) = f.baseChange K := rfl
  have h1 : (e : K ⊗[A] M →ₗ[K] K ⊗[A] N) ∘ₗ u.baseChange K = v.baseChange K ∘ₗ (e : K ⊗[A] M →ₗ[K] K ⊗[A] N) := by
    rw [he, ← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, h]
  have h2 : u.baseChange K = (e.symm : K ⊗[A] N →ₗ[K] K ⊗[A] M) ∘ₗ v.baseChange K ∘ₗ (e.symm.symm : _ →ₗ[K] _) := by
    rw [LinearEquiv.symm_symm, ← h1, ← LinearMap.comp_assoc, LinearEquiv.symm_comp, LinearMap.id_comp]
  rw [h2, LinearMap.det_conj]

theorem solution
    {A B B₀ B₁ : Type*} [CommRing A] [IsDomain A] [CommRing B] [CommRing B₀] [CommRing B₁]
    [Algebra A B] [Algebra A B₀] [Algebra A B₁]
    [Module.Free A B] [Module.Finite A B] [Module.Free A B₀] [Module.Finite A B₀]
    [Module.Free A B₁] [Module.Finite A B₁]
    (φ : B →ₐ[A] B₀ × B₁) (hφ : Function.Injective φ)
    (hrank : Module.finrank A B = Module.finrank A B₀ + Module.finrank A B₁) (b : B) :
    Algebra.norm A b = Algebra.norm A (φ b).1 * Algebra.norm A (φ b).2 := by
  rw [Algebra.norm_apply, Algebra.norm_apply, Algebra.norm_apply, ← LinearMap.det_prodMap]
  refine LinearMap.det_eq_det_of_injective_of_comp_eq φ.toLinearMap hφ (by rw [Module.finrank_prod, hrank]) _ _ ?_
  refine LinearMap.ext fun x => Prod.ext ?_ ?_
  · simp [map_mul]
  · simp [map_mul]

end S_Algebra_norm_eq_norm_fst_mul_norm_snd_of_injective
end P2MW
export P2MW.S_Algebra_norm_eq_norm_fst_mul_norm_snd_of_injective (solution)
