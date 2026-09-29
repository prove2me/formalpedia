-- Prove2me | solution 1 for AlgebraicGeometry.isIso_pullbackMap_fromSpecResidueField_of_isIso_pullbackMap_opens
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/3442d006-b38d-5103-b414-d303f3b3d64c

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isIso_pullbackMap_fromSpecResidueField_of_isIso_pullbackMap_opens

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace K63H2

theorem isIso_pullbackMap_of_fac {X Y Z W W' : Scheme.{0}} (p : Z ⟶ Y) (q : X ⟶ Y) (h : Z ⟶ X)
    (w : h ≫ q = p) (i : W' ⟶ Y) (g : W ⟶ Y) (j : W ⟶ W') (hj : j ≫ i = g)
    (hi : IsIso (pullback.map p i q i h (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp]))) :
    IsIso (pullback.map p g q g h (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp])) := by
  set HI := pullback.map p i q i h (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp]) with hHI
  have F1 : inv HI ≫ pullback.fst p i ≫ h = pullback.fst q i := by
    rw [IsIso.inv_comp_eq, hHI, pullback.lift_fst]
  have F2 : inv HI ≫ pullback.snd p i = pullback.snd q i := by
    rw [IsIso.inv_comp_eq, hHI, pullback.lift_snd, Category.comp_id]
  let mapX : pullback q g ⟶ pullback q i :=
    pullback.map q g q i (𝟙 X) j (𝟙 Y) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hj])
  let mapZ : pullback p g ⟶ pullback p i :=
    pullback.map p g p i (𝟙 Z) j (𝟙 Y) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hj])
  let z : pullback q g ⟶ Z := mapX ≫ inv HI ≫ pullback.fst p i
  have hz : z ≫ p = pullback.snd q g ≫ g := by
    simp only [z, Category.assoc, pullback.condition]
    rw [← Category.assoc (inv HI), F2]
    simp only [mapX, pullback.lift_snd_assoc, Category.assoc, hj]
  refine ⟨⟨pullback.lift z (pullback.snd q g) hz, ?_, ?_⟩⟩
  ·
    have hsq : pullback.map p g q g h (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp]) ≫ mapX = mapZ ≫ HI := by
      apply pullback.hom_ext
      · simp only [mapX, mapZ, hHI, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
          Category.comp_id]
      · simp only [mapX, mapZ, hHI, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
          Category.comp_id]
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.id_comp (pullback.fst p g)]
      simp only [z]
      rw [← Category.assoc, hsq, Category.assoc, IsIso.hom_inv_id_assoc]
      simp only [mapZ, pullback.lift_fst, Category.comp_id]
    · rw [Category.assoc, pullback.lift_snd, Category.id_comp (pullback.snd p g), pullback.lift_snd,
        Category.comp_id]
  ·
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst,
        Category.id_comp (pullback.fst q g)]
      simp only [z, Category.assoc]
      rw [F1]
      simp only [mapX, pullback.lift_fst, Category.comp_id]
    · rw [Category.assoc, pullback.lift_snd, Category.comp_id, pullback.lift_snd,
        Category.id_comp (pullback.snd q g)]

end K63H2

theorem solution
    {X Y Z : Scheme.{0}} (p : Z ⟶ Y) (q : X ⟶ Y) (h : Z ⟶ X) (w : h ≫ q = p)
    (V : Y.Opens) (y : Y) (hy : y ∈ V)
    (hV : IsIso (pullback.map p V.ι q V.ι h (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp]))) :
    IsIso (pullback.map p (Y.fromSpecResidueField y) q (Y.fromSpecResidueField y) h (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp])) := by
  have hsub : Set.range (Y.fromSpecResidueField y).base ⊆ Set.range V.ι.base := by
    rw [Scheme.range_fromSpecResidueField, Scheme.Opens.range_ι, Set.singleton_subset_iff]
    exact hy
  exact K63H2.isIso_pullbackMap_of_fac p q h w V.ι (Y.fromSpecResidueField y)
    (IsOpenImmersion.lift V.ι (Y.fromSpecResidueField y) hsub) (IsOpenImmersion.lift_fac _ _ _) hV

end S_AlgebraicGeometry_isIso_pullbackMap_fromSpecResidueField_of_isIso_pullbackMap_opens
end P2MW
export P2MW.S_AlgebraicGeometry_isIso_pullbackMap_fromSpecResidueField_of_isIso_pullbackMap_opens (solution)
