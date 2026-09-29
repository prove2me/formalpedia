-- Prove2me | solution 1 for AlgebraicGeometry.fppf_exists_section_of_map_eq_unit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/94de2c73-94b4-57e2-b83b-c200c6d4a8c6

import Mathlib
import Definitions.Def_AlgebraicGeometry_FppfKummerProp17
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_fppf_exists_section_of_map_eq_unit

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry Opposite"

theorem solution
    {E : CategoryTheory.Sheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1}}
    (g : E ⟶ (CategoryTheory.constantSheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1}).obj (.of (ULift.{1} ℤ)))
    (e : ToType (E.obj.obj (op (Spec (.of ℤ)))))
    (he : g.hom.app (op (Spec (.of ℤ))) e =
      (CategoryTheory.constantSheafAdj Scheme.fppfTopology.{0} AddCommGrpCat.{1}
          AlgebraicGeometry.specZIsTerminal).unit.app (.of (ULift.{1} ℤ)) (ULift.up 1)) :
    ∃ s : (CategoryTheory.constantSheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1}).obj (.of (ULift.{1} ℤ)) ⟶ E,
      s ≫ g = 𝟙 _ := by

  let adj := CategoryTheory.constantSheafAdj Scheme.fppfTopology.{0} AddCommGrpCat.{1} AlgebraicGeometry.specZIsTerminal

  let φ : (AddCommGrpCat.of (ULift.{1} ℤ)) ⟶ E.obj.obj (op (Spec (.of ℤ))) :=
    AddCommGrpCat.ofHom (((zmultiplesHom (E.obj.obj (op (Spec (.of ℤ))))) e).comp AddEquiv.ulift.toAddMonoidHom)
  have hφ : φ (ULift.up 1) = e := by
    change (AddEquiv.ulift (ULift.up (1 : ℤ))) • e = e
    exact one_zsmul e
  refine ⟨(adj.homEquiv _ E).symm φ, ?_⟩
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_right, Equiv.apply_symm_apply, Adjunction.homEquiv_id]

  ext x
  obtain ⟨n⟩ := x
  have hx : (ULift.up n : ULift.{1} ℤ) = n • ULift.up 1 := by
    ext; simp
  rw [hx, map_zsmul, map_zsmul]
  congr 1
  change g.hom.app (op (Spec (.of ℤ))) (φ (ULift.up 1)) = adj.unit.app _ (ULift.up 1)
  rw [hφ]
  exact he

end S_AlgebraicGeometry_fppf_exists_section_of_map_eq_unit
end P2MW
export P2MW.S_AlgebraicGeometry_fppf_exists_section_of_map_eq_unit (solution)
