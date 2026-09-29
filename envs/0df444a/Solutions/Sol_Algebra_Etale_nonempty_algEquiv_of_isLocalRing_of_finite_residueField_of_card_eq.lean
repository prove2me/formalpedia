-- Prove2me | solution 1 for Algebra.Etale.nonempty_algEquiv_of_isLocalRing_of_finite_residueField_of_card_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/416c8dcd-2d39-5f1a-9706-49ed4d52bf40

import Mathlib
import Theorems.Thm_FiniteField_nonempty_algEquiv_of_card_eq
import Theorems.Thm_Algebra_Etale_exists_algEquiv_residue_eq_of_isLocalRing_of_isAdicComplete
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_Etale_nonempty_algEquiv_of_isLocalRing_of_finite_residueField_of_card_eq

set_option autoImplicit false

open IsLocalRing

theorem solution
    (R₀ : Type) [CommRing R₀] [IsLocalRing R₀] [IsNoetherianRing R₀] [IsAdicComplete (maximalIdeal R₀) R₀]
    (S₁ : Type) [CommRing S₁] [IsLocalRing S₁] [Algebra R₀ S₁] [IsLocalHom (algebraMap R₀ S₁)]
    [Module.Finite R₀ S₁] [Algebra.Etale R₀ S₁]
    (S₂ : Type) [CommRing S₂] [IsLocalRing S₂] [Algebra R₀ S₂] [IsLocalHom (algebraMap R₀ S₂)]
    [Module.Finite R₀ S₂] [Algebra.Etale R₀ S₂]
    [Finite (ResidueField S₁)] [Finite (ResidueField S₂)]
    (h : Nat.card (ResidueField S₁) = Nat.card (ResidueField S₂)) :
    Nonempty (S₁ ≃ₐ[R₀] S₂) := by
  classical
  obtain ⟨e₀⟩ := FiniteField.nonempty_algEquiv_of_card_eq (ResidueField R₀) (ResidueField S₁) (ResidueField S₂) h
  obtain ⟨e, -⟩ := Algebra.Etale.exists_algEquiv_residue_eq_of_isLocalRing_of_isAdicComplete R₀ S₁ S₂ e₀
  exact ⟨e⟩

end S_Algebra_Etale_nonempty_algEquiv_of_isLocalRing_of_finite_residueField_of_card_eq
end P2MW
export P2MW.S_Algebra_Etale_nonempty_algEquiv_of_isLocalRing_of_finite_residueField_of_card_eq (solution)
