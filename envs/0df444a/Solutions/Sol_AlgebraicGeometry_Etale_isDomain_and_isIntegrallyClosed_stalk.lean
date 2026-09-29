-- Prove2me | solution 1 for AlgebraicGeometry.Etale.isDomain_and_isIntegrallyClosed_stalk
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/5032df03-49b8-5ef1-a8b7-316f8c9f8395

import Mathlib
import Theorems.Thm_Algebra_Etale_isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Etale_isDomain_and_isIntegrallyClosed_stalk

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution {U S : Scheme.{u}} (f : U ⟶ S) [Etale f]
    [IsAffine S] [IsDomain Γ(S, ⊤)] [IsIntegrallyClosed Γ(S, ⊤)] (y : U) :
    IsDomain (U.presheaf.stalk y) ∧ IsIntegrallyClosed (U.presheaf.stalk y) := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, -⟩ :=
    U.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hle : W ≤ f ⁻¹ᵁ ⊤ := le_top
  have hφ : RingHom.Etale (f.appLE ⊤ W hle).hom :=
    HasRingHomProperty.appLE @Etale f inferInstance ⟨⊤, isAffineOpen_top S⟩ ⟨W, hW⟩ hle
  letI := (f.appLE ⊤ W hle).hom.toAlgebra
  haveI : Algebra.Etale Γ(S, ⊤) Γ(U, W) := hφ
  letI := TopCat.Presheaf.algebra_section_stalk U.presheaf (⟨y, hyW⟩ : W)
  haveI := hW.isLocalization_stalk ⟨y, hyW⟩
  exact Algebra.Etale.isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime Γ(S, ⊤) Γ(U, W)
    (hW.primeIdealOf ⟨y, hyW⟩).asIdeal (U.presheaf.stalk y)

end S_AlgebraicGeometry_Etale_isDomain_and_isIntegrallyClosed_stalk
end P2MW
export P2MW.S_AlgebraicGeometry_Etale_isDomain_and_isIntegrallyClosed_stalk (solution)
