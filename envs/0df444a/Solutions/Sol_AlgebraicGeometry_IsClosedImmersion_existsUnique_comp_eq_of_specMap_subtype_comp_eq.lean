-- Prove2me | solution 1 for AlgebraicGeometry.IsClosedImmersion.existsUnique_comp_eq_of_specMap_subtype_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/caee2b88-2232-5524-920d-b0a75347c068

import Mathlib
import Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_existsUnique_comp_eq_of_denseRange_of_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_IsClosedImmersion_existsUnique_comp_eq_of_specMap_subtype_comp_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {Ω : Type u} [Field Ω] (O : Subring Ω)
    {Y Z : Scheme.{u}} (ι : Z ⟶ Y) [IsClosedImmersion ι] (z : Spec (CommRingCat.of ↥O) ⟶ Y)
    (ψ : Spec (CommRingCat.of Ω) ⟶ Z) (hψ : ψ ≫ ι = Spec.map (CommRingCat.ofHom O.subtype) ≫ z) :
    ∃! χ : Spec (CommRingCat.of ↥O) ⟶ Z, χ ≫ ι = z := by
  haveI : IsReduced (Spec (CommRingCat.of ↥O)) := inferInstance
  refine AlgebraicGeometry.IsClosedImmersion.existsUnique_comp_eq_of_denseRange_of_comp_eq
    (Spec.map (CommRingCat.ofHom O.subtype)) ?_ ι z ψ hψ

  have hker : RingHom.ker O.subtype ≤ nilradical ↥O := by
    intro a ha
    rw [RingHom.mem_ker] at ha
    have : a = 0 := Subtype.ext ha
    rw [this]; exact Ideal.zero_mem _
  have h := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (f := O.subtype)).mpr hker
  convert h using 1
  rfl
  rfl
  rfl
  rfl

end S_AlgebraicGeometry_IsClosedImmersion_existsUnique_comp_eq_of_specMap_subtype_comp_eq
end P2MW
export P2MW.S_AlgebraicGeometry_IsClosedImmersion_existsUnique_comp_eq_of_specMap_subtype_comp_eq (solution)
