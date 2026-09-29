-- Prove2me | solution 1 for Algebra.finite_and_flat_of_weilRestriction_points_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/5784fce6-3b41-55cb-afb1-7a75aca701c9

import Mathlib
import Theorems.Thm_Algebra_Etale_exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi_of_rankAtStalk_eq
import Theorems.Thm_Algebra_finite_and_free_baseChange_of_weilRestriction_points_equiv_of_algEquiv_pi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_finite_and_flat_of_weilRestriction_points_equiv

set_option autoImplicit false

open scoped TensorProduct

universe u

theorem solution
    (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B] [Module.Finite A B] [Module.Free A B]
    [Algebra.Etale A B]
    (H : Type u) [CommRing H] [Algebra B H] [Module.Finite B H] [Module.Free B H]
    (W : Type u) [CommRing W] [Algebra A W]
    (e : ∀ (T : Type u) [CommRing T] [Algebra A T], (W →ₐ[A] T) ≃ (H →ₐ[B] (B ⊗[A] T)))
    (he_nat : ∀ (T T' : Type u) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (u : T →ₐ[A] T')
      (f : W →ₐ[A] T), e T' (u.comp f) = (Algebra.TensorProduct.map (AlgHom.id B B) u).comp (e T f)) :
    Module.Finite A W ∧ Module.Flat A W := by

  have hrk : ∀ p : PrimeSpectrum A, Module.rankAtStalk (R := A) B p = Module.finrank A B := by
    intro p
    simp [Module.rankAtStalk_eq_finrank_of_free]
  obtain ⟨A', _, _, hfin', het', hff', ⟨φ⟩⟩ :=
    Algebra.Etale.exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi_of_rankAtStalk_eq A B
      (Module.finrank A B) hrk

  obtain ⟨hfinW, hfreeW⟩ :=
    Algebra.finite_and_free_baseChange_of_weilRestriction_points_equiv_of_algEquiv_pi A B H W e he_nat A'
      (Module.finrank A B) φ
  haveI := hfinW; haveI := hfreeW
  haveI : Module.Flat A' (A' ⊗[A] W) := inferInstance

  exact ⟨Module.Finite.of_finite_tensorProduct_of_faithfullyFlat A', Module.Flat.of_flat_tensorProduct A W A'⟩

end S_Algebra_finite_and_flat_of_weilRestriction_points_equiv
end P2MW
export P2MW.S_Algebra_finite_and_flat_of_weilRestriction_points_equiv (solution)
