-- Prove2me | solution 1 for Algebra.DescentCofaces.exists_finite_flat_unramified_nonempty_ringHom_iff_isCoboundary
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/b8beca12-ab6c-5dff-bf3e-a2f0aab74e89

import Mathlib
import Definitions.Def_Algebra_DescentCofaces
import Theorems.Thm_PrimeSpectrum_exists_completeOrthogonalIdempotents_forall_apply_eq_iff
import Theorems.Thm_PrimeSpectrum_exists_locallyConstant_forall_apply_eq_iff
import Theorems.Thm_PrimeSpectrum_sum_map_mul_map_eq_map_of_forall_comap_add
import Theorems.Thm_PrimeSpectrum_forall_sub_apply_eq_iff
import Theorems.Thm_Module_FaithfullyFlat_exists_submodule_forall_mem_iff_sum_mul_tmul_isBaseChange
import Theorems.Thm_Module_FaithfullyFlat_exists_completeOrthogonalIdempotents_eq_sum_tmul_of_isBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_DescentCofaces_exists_finite_flat_unramified_nonempty_ringHom_iff_isCoboundary

set_option autoImplicit false

open Algebra.DescentCofaces AlgebraicGeometry
open scoped TensorProduct

theorem solution
    (p : ℕ) (hp : p ≠ 0) (A : Type) [CommRing A] [Module.FaithfullyFlat ℤ A]
    (c : LocallyConstant (PrimeSpectrum (R₂ ℤ A)) (ZMod p))
    (hc : c.comap (Spec.topMap (c₁₂ ℤ A)).hom + c.comap (Spec.topMap (c₂₃ ℤ A)).hom =
        c.comap (Spec.topMap (c₁₃ ℤ A)).hom) :
    ∃ (B : Type) (_ : CommRing B) (_ : Nontrivial B) (_ : Module.Finite ℤ B) (_ : Module.Flat ℤ B)
      (_ : Algebra.FormallyUnramified ℤ B) (_ : A ⊗[ℤ] B ≃ₐ[A] (ZMod p → A)),
      Nonempty (B →+* ℤ) ↔
        ∃ b : LocallyConstant (PrimeSpectrum A) (ZMod p),
          c = b.comap (Spec.topMap (i₁ ℤ A)).hom - b.comap (Spec.topMap (i₂ ℤ A)).hom := by
  classical
  haveI : NeZero p := ⟨hp⟩

  have key : ∃ b : LocallyConstant (PrimeSpectrum A) (ZMod p),
      c = b.comap (Spec.topMap (i₁ ℤ A)).hom - b.comap (Spec.topMap (i₂ ℤ A)).hom := by
    obtain ⟨e, he, hce⟩ := PrimeSpectrum.exists_completeOrthogonalIdempotents_forall_apply_eq_iff c
    have hcoc : ∀ k, ∑ i, (c₁₂ ℤ A).hom (e i) * (c₂₃ ℤ A).hom (e (k - i)) = (c₁₃ ℤ A).hom (e k) := by
      refine PrimeSpectrum.sum_map_mul_map_eq_map_of_forall_comap_add
        (c₁₂ ℤ A).hom (c₂₃ ℤ A).hom (c₁₃ ℤ A).hom ⇑c e he hce ?_
      intro y
      have := congrArg (fun g : LocallyConstant _ (ZMod p) => g y) hc
      simp at this
      exact this
    obtain ⟨M, hM, hbc⟩ :=
      Module.FaithfullyFlat.exists_submodule_forall_mem_iff_sum_mul_tmul_isBaseChange e he hcoc
    obtain ⟨d, hd, hed⟩ :=
      Module.FaithfullyFlat.exists_completeOrthogonalIdempotents_eq_sum_tmul_of_isBaseChange A e he M hM hbc
    obtain ⟨b, hbd⟩ := PrimeSpectrum.exists_locallyConstant_forall_apply_eq_iff d hd
    refine ⟨b, ?_⟩
    ext y
    have h₁ : ∀ (i : ZMod p) (y : PrimeSpectrum (R₂ ℤ A)),
        b (PrimeSpectrum.comap (i₁ ℤ A).hom y) = i ↔ (i₁ ℤ A).hom (d i) ∉ y.asIdeal :=
      fun i y => by rw [hbd]; rfl
    have h₂ : ∀ (i : ZMod p) (y : PrimeSpectrum (R₂ ℤ A)),
        b (PrimeSpectrum.comap (i₂ ℤ A).hom y) = i ↔ (i₂ ℤ A).hom (d i) ∉ y.asIdeal :=
      fun i y => by rw [hbd]; rfl
    have hsub := PrimeSpectrum.forall_sub_apply_eq_iff _ _ _ _ h₁ h₂ (c y) y
    have hek : e (c y) ∉ y.asIdeal := (hce _ y).mp rfl
    have hconv : (∑ i, (i₁ ℤ A).hom (d i) * (i₂ ℤ A).hom (d (i - c y))) = e (c y) := by
      rw [hed]
      refine Finset.sum_congr rfl fun i _ => ?_
      change d i ⊗ₜ[ℤ] (1 : A) * ((1 : A) ⊗ₜ[ℤ] d (i - c y)) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hconv] at hsub
    have := (hsub.mpr hek).symm
    simp at this
    exact this

  have hU : Algebra.FormallyUnramified ℤ (ZMod p → ℤ) := inferInstance
  refine ⟨ZMod p → ℤ, inferInstance, inferInstance, inferInstance, inferInstance, by convert hU; rfl,
    Algebra.TensorProduct.piScalarRight ℤ A A (ZMod p), ?_⟩
  exact ⟨fun _ => key, fun _ => ⟨Pi.evalRingHom (fun _ : ZMod p => ℤ) 0⟩⟩

end S_Algebra_DescentCofaces_exists_finite_flat_unramified_nonempty_ringHom_iff_isCoboundary
end P2MW
export P2MW.S_Algebra_DescentCofaces_exists_finite_flat_unramified_nonempty_ringHom_iff_isCoboundary (solution)
