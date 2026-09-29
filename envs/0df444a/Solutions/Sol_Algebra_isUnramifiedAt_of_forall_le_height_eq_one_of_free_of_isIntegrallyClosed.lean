-- Prove2me | solution 1 for Algebra.isUnramifiedAt_of_forall_le_height_eq_one_of_free_of_isIntegrallyClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/95ef7472-fbfe-538c-bacd-db30e020e98f

import Mathlib
import Theorems.Thm_Algebra_exists_le_height_eq_one_of_comap_one_div_traceDual_le_of_free_of_isIntegrallyClosed
import Theorems.Thm_Algebra_isUnramifiedAt_iff_not_le_comap_one_div_traceDual_of_free_of_isIntegrallyClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_isUnramifiedAt_of_forall_le_height_eq_one_of_free_of_isIntegrallyClosed

set_option autoImplicit false

universe u

theorem solution
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    (B : Type u) [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra A B] [Module.Finite A B] [Module.Free A B]
    (L : Type u) [Field L] [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] [Algebra.IsSeparable K L]
    (P : Ideal B) [P.IsPrime]
    (h : ∀ (Q : Ideal B) [Q.IsPrime], Q ≤ P → Q.height = 1 → Algebra.IsUnramifiedAt A Q) :
    Algebra.IsUnramifiedAt A P := by
  by_contra hP
  have hDP : ((1 / Submodule.traceDual A K (1 : Submodule B L) : Submodule B L).comap (Algebra.linearMap B L)) ≤ P := by
    by_contra hnle
    exact hP ((Algebra.isUnramifiedAt_iff_not_le_comap_one_div_traceDual_of_free_of_isIntegrallyClosed
      A K B L P).mpr hnle)
  obtain ⟨Q, hQ, hQP, hQ1, hDQ⟩ :=
    Algebra.exists_le_height_eq_one_of_comap_one_div_traceDual_le_of_free_of_isIntegrallyClosed A K B L P hDP
  haveI := hQ
  have hunr : Algebra.IsUnramifiedAt A Q := h Q hQP hQ1
  exact ((Algebra.isUnramifiedAt_iff_not_le_comap_one_div_traceDual_of_free_of_isIntegrallyClosed
    A K B L Q).mp hunr) hDQ

#print axioms solution

end S_Algebra_isUnramifiedAt_of_forall_le_height_eq_one_of_free_of_isIntegrallyClosed
end P2MW
export P2MW.S_Algebra_isUnramifiedAt_of_forall_le_height_eq_one_of_free_of_isIntegrallyClosed (solution)
