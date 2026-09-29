-- Prove2me | solution 1 for AlgebraicCurve.germToFunctionField_mem_lSpaceOn_placesOf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/adb4deee-55df-5ca7-88e6-ac0bdbd3cfdc

import Mathlib
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicCurve_PlacesOf
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_adicValuation_le_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_germToFunctionField_mem_lSpaceOn_placesOf
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve

universe u

theorem solution
    {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C]
    (U : C.Opens) [Nonempty (U : C.Opens)] (s : Γ(C, U)) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    (C.germToFunctionField U).hom s ∈
      AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf c U) (0 : AlgebraicCurve.Divisor K C.functionField) := by
  letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  rintro v ⟨x, hxU, -, hvx⟩
  simp only [Finsupp.coe_zero, Pi.zero_apply, WithZero.exp_zero]
  rw [← Place.mem_iff_adicValuation_le_one]
  change (C.germToFunctionField U).hom s ∈ v.toValuationSubring.toSubring
  rw [← hvx]
  letI := C.presheaf.algebra_section_stalk (⟨x, hxU⟩ : U)
  haveI := AlgebraicGeometry.functionField_isScalarTower (X := C) U ⟨x, hxU⟩
  exact RingHom.mem_range.mpr ⟨algebraMap Γ(C, U) (C.presheaf.stalk x) s,
    (IsScalarTower.algebraMap_apply Γ(C, U) (C.presheaf.stalk x) C.functionField s).symm⟩

end S_AlgebraicCurve_germToFunctionField_mem_lSpaceOn_placesOf
end P2MW
export P2MW.S_AlgebraicCurve_germToFunctionField_mem_lSpaceOn_placesOf (solution)
