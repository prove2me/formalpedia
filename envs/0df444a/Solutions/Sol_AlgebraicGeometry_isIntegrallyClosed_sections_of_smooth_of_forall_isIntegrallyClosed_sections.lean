-- Prove2me | solution 1 for AlgebraicGeometry.isIntegrallyClosed_sections_of_smooth_of_forall_isIntegrallyClosed_sections
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/78210858-3c38-5176-b023-825881bf44c9

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk
import Theorems.Thm_AlgebraicGeometry_IsIntegral_isIntegrallyClosed_sections_of_forall_isIntegrallyClosed_stalk
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isIntegrallyClosed_sections_of_smooth_of_forall_isIntegrallyClosed_sections

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

theorem solution
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] [IsIntegral X] [IsIntegral Y]
    (hY : ∀ V : Y.Opens, IsAffineOpen V → IsIntegrallyClosed Γ(Y, V))
    (U : X.Opens) (hU : IsAffineOpen U) : IsIntegrallyClosed Γ(X, U) := by
  refine AlgebraicGeometry.IsIntegral.isIntegrallyClosed_sections_of_forall_isIntegrallyClosed_stalk
    (X := X) (fun x => ?_) U hU

  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f.base x)) isOpen_univ
  replace hV : IsAffineOpen (V : Y.Opens) := hV

  haveI : IsAffine (V : Scheme.{u}) := hV
  have hne : Nonempty (V : Scheme.{u}) := ⟨⟨f.base x, hxV⟩⟩
  haveI : IsIntegral (V : Scheme.{u}) := isIntegral_of_isOpenImmersion (Scheme.Opens.ι V)
  haveI : IsDomain Γ((V : Scheme.{u}), ⊤) := inferInstance
  haveI : IsIntegrallyClosed Γ((V : Scheme.{u}), ⊤) := by
    haveI : IsIntegrallyClosed Γ(Y, V) := hY V hV
    exact IsIntegrallyClosed.of_equiv (Scheme.Opens.topIso V).commRingCatIsoToRingEquiv.symm

  haveI : Smooth (f ∣_ V) := inferInstance
  have hx' : x ∈ f ⁻¹ᵁ V := hxV
  have h2 := (AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk (f ∣_ V) ⟨x, hx'⟩).2
  have e2 : ((f ⁻¹ᵁ V : X.Opens) : Scheme.{u}).presheaf.stalk ⟨x, hx'⟩ ≅ X.presheaf.stalk x :=
    (f ⁻¹ᵁ V).stalkIso ⟨x, hx'⟩
  haveI := h2
  exact IsIntegrallyClosed.of_equiv e2.commRingCatIsoToRingEquiv

#print axioms solution

end S_AlgebraicGeometry_isIntegrallyClosed_sections_of_smooth_of_forall_isIntegrallyClosed_sections
end P2MW
export P2MW.S_AlgebraicGeometry_isIntegrallyClosed_sections_of_smooth_of_forall_isIntegrallyClosed_sections (solution)
