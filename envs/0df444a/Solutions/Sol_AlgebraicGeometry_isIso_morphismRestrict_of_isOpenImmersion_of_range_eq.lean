-- Prove2me | solution 1 for AlgebraicGeometry.isIso_morphismRestrict_of_isOpenImmersion_of_range_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/8513bd63-705b-5c2d-a005-b349b0cce078

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isIso_morphismRestrict_of_isOpenImmersion_of_range_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

theorem solution
    {P P' : Scheme.{u}} (β : P' ⟶ P) (U : P.Opens) (s : (U : Scheme.{u}) ⟶ P') [IsOpenImmersion s]
    (hsβ : s ≫ β = U.ι) (hsr : Set.range s.base = β.base ⁻¹' (U : Set P)) :
    IsIso (β ∣_ U) := by
  have hr : Set.range s.base = Set.range (β ⁻¹ᵁ U).ι.base := by
    rw [hsr, Scheme.Opens.range_ι]; rfl
  let e := IsOpenImmersion.isoOfRangeEq s (β ⁻¹ᵁ U).ι hr
  have he : e.hom ≫ (β ⁻¹ᵁ U).ι = s := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have h1 : e.hom ≫ (β ∣_ U) = 𝟙 _ := by
    rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, he, hsβ,
      Category.id_comp]
  have h2 : β ∣_ U = e.inv := by
    rw [← Category.id_comp (β ∣_ U), ← e.inv_hom_id, Category.assoc, h1, Category.comp_id]
  rw [h2]
  infer_instance

end S_AlgebraicGeometry_isIso_morphismRestrict_of_isOpenImmersion_of_range_eq
end P2MW
export P2MW.S_AlgebraicGeometry_isIso_morphismRestrict_of_isOpenImmersion_of_range_eq (solution)
