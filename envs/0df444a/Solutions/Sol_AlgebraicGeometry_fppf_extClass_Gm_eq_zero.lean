-- Prove2me | solution 1 for AlgebraicGeometry.fppf_extClass_Gm_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/4ee4ab56-d3f7-5b50-8ee6-30934de67aff

import Definitions.Def_AlgebraicGeometry_FppfKummerProp17
import Definitions.Def_AlgebraicGeometry_FppfAmitsurTrivial
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Theorems.Thm_CategoryTheory_ShortComplex_ShortExact_extClass_eq_zero_iff_exists_section_g
import Theorems.Thm_AlgebraicGeometry_exists_section_of_fppfAmitsurTrivial
import Theorems.Thm_AlgebraicGeometry_Scheme_fppfAmitsurTrivial_gmAbelianSheafLifted
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_fppf_extClass_Gm_eq_zero
set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry"

theorem solution
    (E : CategoryTheory.Sheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1})
    (f : FppfKummerSES.GmAbelianSheafLifted.{0} ⟶ E)
    (g : E ⟶ (CategoryTheory.constantSheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1}).obj (.of (ULift.{1} ℤ)))
    (w : f ≫ g = 0)
    (hS : (CategoryTheory.ShortComplex.mk f g w).ShortExact) :
    hS.extClass = 0 := by
  rw [hS.extClass_eq_zero_iff_exists_section_g]
  exact AlgebraicGeometry.exists_section_of_fppfAmitsurTrivial _ E f g w hS
    (fun A _ _ _ => AlgebraicGeometry.Scheme.fppfAmitsurTrivial_gmAbelianSheafLifted A)

end S_AlgebraicGeometry_fppf_extClass_Gm_eq_zero
end P2MW
export P2MW.S_AlgebraicGeometry_fppf_extClass_Gm_eq_zero (solution)
