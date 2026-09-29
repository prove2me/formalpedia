-- Prove2me | solution 1 for AlgebraicGeometry.specMap_comp_pullbackLift_eq_pullbackLift_comp_pullbackMap_of_comp_eq_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/c40ac352-47c5-5347-98ea-a7625397652e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_specMap_comp_pullbackLift_eq_pullbackLift_comp_pullbackMap_of_comp_eq_comp

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Ws23
namespace BCInt

theorem main
    {G S : Scheme.{u}} (g : G ⟶ S)
    {k L A : Type u} [CommRing k] [CommRing L] [CommRing A]
    (s : Spec (CommRingCat.of k) ⟶ S)
    (ι : Spec (CommRingCat.of L) ⟶ G)
    (E : G ⟶ G) (hE : E ≫ g = g)
    (e : L →+* L) (hι : Spec.map (CommRingCat.ofHom e) ≫ ι = ι ≫ E)
    (a : L →+* A) (c : k →+* A)
    (hsq : (Spec.map (CommRingCat.ofHom a) ≫ ι) ≫ g = Spec.map (CommRingCat.ofHom c) ≫ s)
    (eA : A →+* A) (hea : eA.comp a = a.comp e) (hec : eA.comp c = c) :
    Spec.map (CommRingCat.ofHom eA) ≫ pullback.lift (Spec.map (CommRingCat.ofHom a) ≫ ι) (Spec.map (CommRingCat.ofHom c)) hsq =
      pullback.lift (Spec.map (CommRingCat.ofHom a) ≫ ι) (Spec.map (CommRingCat.ofHom c)) hsq ≫
        pullback.map g s g s E (𝟙 _) (𝟙 _) (by rw [Category.comp_id]; exact hE.symm) (by rw [Category.comp_id, Category.id_comp]) := by

  have h1 : Spec.map (CommRingCat.ofHom eA) ≫ Spec.map (CommRingCat.ofHom a) =
      Spec.map (CommRingCat.ofHom a) ≫ Spec.map (CommRingCat.ofHom e) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hea]
  have h2 : Spec.map (CommRingCat.ofHom eA) ≫ Spec.map (CommRingCat.ofHom c) = Spec.map (CommRingCat.ofHom c) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hec]

  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    rw [← Category.assoc, h1, Category.assoc, hι]
  · simp only [Category.assoc, pullback.lift_snd, Category.comp_id]
    rw [h2]

end Ws23.BCInt

theorem solution
    {G S : Scheme.{u}} (g : G ⟶ S)
    {k L A : Type u} [CommRing k] [CommRing L] [CommRing A]
    (s : Spec (CommRingCat.of k) ⟶ S)
    (ι : Spec (CommRingCat.of L) ⟶ G)
    (E : G ⟶ G) (hE : E ≫ g = g)
    (e : L →+* L) (hι : Spec.map (CommRingCat.ofHom e) ≫ ι = ι ≫ E)
    (a : L →+* A) (c : k →+* A)
    (hsq : (Spec.map (CommRingCat.ofHom a) ≫ ι) ≫ g = Spec.map (CommRingCat.ofHom c) ≫ s)
    (eA : A →+* A) (hea : eA.comp a = a.comp e) (hec : eA.comp c = c) :
    Spec.map (CommRingCat.ofHom eA) ≫ pullback.lift (Spec.map (CommRingCat.ofHom a) ≫ ι) (Spec.map (CommRingCat.ofHom c)) hsq =
      pullback.lift (Spec.map (CommRingCat.ofHom a) ≫ ι) (Spec.map (CommRingCat.ofHom c)) hsq ≫
        pullback.map g s g s E (𝟙 _) (𝟙 _) (by rw [Category.comp_id]; exact hE.symm) (by rw [Category.comp_id, Category.id_comp]) :=
  Ws23.BCInt.main g s ι E hE e hι a c hsq eA hea hec

end S_AlgebraicGeometry_specMap_comp_pullbackLift_eq_pullbackLift_comp_pullbackMap_of_comp_eq_comp
end P2MW
export P2MW.S_AlgebraicGeometry_specMap_comp_pullbackLift_eq_pullbackLift_comp_pullbackMap_of_comp_eq_comp (solution)
