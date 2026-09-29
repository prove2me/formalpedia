-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_linearEquiv_H1StructureSheaf_symm_eq_H1baseChangeMap_self
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/64efdaba-39e0-5668-85a7-9bf269023909

import Mathlib
import Definitions.Def_AlgebraicGeometry_PicDualNumberDeformationClassSpec
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverH1BaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_H1StructureSheaf_symm_eq_H1baseChangeMap_self

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard

theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover) (c : C ⟶ Spec (.of R)) :
    ∃ j : H1StructureSheaf c R 𝒱 ≃ₗ[R] (𝒱.structureSheafSections c).H1,
      ∀ y, j.symm y = Scheme.TwoAffineOpenCover.H1baseChangeMap 𝒱 c R y := by

  have hι : Scheme.TwoAffineOpenCover.specMap R R = 𝟙 (Spec (.of R)) := by
    change Spec.map (CommRingCat.ofHom (RingHom.id R)) = _
    rw [CommRingCat.ofHom_id, Spec.map_id]
  haveI : IsIso (Scheme.TwoAffineOpenCover.specMap R R) := hι ▸ inferInstance
  haveI hfst : IsIso (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R R)) := inferInstance

  let f := Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c R
  let g : Scheme.TwoAffineOpenCover.HomOver (RingHom.id R) (𝒱.pullback c R)
      (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R R)) 𝒱 c :=
    { hom := inv (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R R))
      comm := by
        rw [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id, IsIso.inv_comp_eq, pullback.condition, hι,
          Category.comp_id]
      U0_le := by
        rw [Scheme.TwoAffineOpenCover.pullback_U0, ← Scheme.Hom.comp_preimage, IsIso.inv_hom_id,
          Scheme.Hom.id_preimage]
      U1_le := by
        rw [Scheme.TwoAffineOpenCover.pullback_U1, ← Scheme.Hom.comp_preimage, IsIso.inv_hom_id,
          Scheme.Hom.id_preimage] }
  have hgf : ∀ x, g.H1map (f.H1map x) = x := fun x => by
    rw [← Scheme.TwoAffineOpenCover.HomOver.comp_H1map]
    exact (Scheme.TwoAffineOpenCover.HomOver.H1map_congr (f := g.comp f)
      (g := Scheme.TwoAffineOpenCover.HomOver.id 𝒱 c)
      (show inv (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R R)) ≫
          pullback.fst c (Scheme.TwoAffineOpenCover.specMap R R) = 𝟙 C from IsIso.inv_hom_id _) x).trans
      (Scheme.TwoAffineOpenCover.HomOver.id_H1map x)
  have hfg : ∀ y, f.H1map (g.H1map y) = y := fun y => by
    rw [← Scheme.TwoAffineOpenCover.HomOver.comp_H1map]
    exact (Scheme.TwoAffineOpenCover.HomOver.H1map_congr (f := f.comp g)
      (g := Scheme.TwoAffineOpenCover.HomOver.id (𝒱.pullback c R)
        (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R R)))
      (show pullback.fst c (Scheme.TwoAffineOpenCover.specMap R R) ≫
          inv (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R R)) = 𝟙 _ from IsIso.hom_inv_id _) y).trans
      (Scheme.TwoAffineOpenCover.HomOver.id_H1map y)
  exact ⟨{ g.H1map with invFun := f.H1map, left_inv := hfg, right_inv := hgf }, fun y => rfl⟩

end S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_H1StructureSheaf_symm_eq_H1baseChangeMap_self
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_H1StructureSheaf_symm_eq_H1baseChangeMap_self (solution)
