-- Prove2me | solution 1 for AlgebraicGeometry.locallyOfFinitePresentation_of_comp_of_locallyOfFiniteType
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/65f23b80-4f77-59c0-b998-38686296387b

import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_locallyOfFinitePresentation_of_comp_of_locallyOfFiniteType

set_option autoImplicit false

universe u

open CategoryTheory

open AlgebraicGeometry

theorem solution
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} (h : LocallyOfFinitePresentation (f ≫ g))
    (hg : LocallyOfFiniteType g) : LocallyOfFinitePresentation f := by
  wlog hZ : IsAffine Z generalizing X Y Z
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) _
      (g.iSup_preimage_eq_top (iSup_affineOpens_eq_top Z))]
    intro U
    have H := IsZariskiLocalAtTarget.restrict (P := @LocallyOfFinitePresentation) h U.1
    rw [morphismRestrict_comp] at H
    exact this H (IsZariskiLocalAtTarget.restrict (P := @LocallyOfFiniteType) hg U.1) inferInstance
  wlog hY : IsAffine Y generalizing X Y
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) _
      (iSup_affineOpens_eq_top Y)]
    intro U
    have H := HasRingHomProperty.comp_of_isOpenImmersion @LocallyOfFinitePresentation
      (f ⁻¹ᵁ U.1).ι (f ≫ g) h
    rw [← morphismRestrict_ι_assoc] at H
    exact this H (HasRingHomProperty.comp_of_isOpenImmersion @LocallyOfFiniteType U.1.ι g hg)
      inferInstance
  wlog hX : IsAffine X generalizing X
  · rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) _
      (iSup_affineOpens_eq_top X)]
    intro U
    have H := HasRingHomProperty.comp_of_isOpenImmersion @LocallyOfFinitePresentation U.1.ι
      (f ≫ g) h
    rw [← Category.assoc] at H
    exact this H inferInstance
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)] at h ⊢
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)] at hg
  exact RingHom.FinitePresentation.of_comp_finiteType _ h hg

#print axioms solution
#check @solution

end S_AlgebraicGeometry_locallyOfFinitePresentation_of_comp_of_locallyOfFiniteType
end P2MW
export P2MW.S_AlgebraicGeometry_locallyOfFinitePresentation_of_comp_of_locallyOfFiniteType (solution)
