-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.map_germ_comap_ideal_eq_map_stalkMap_of_isOpenImmersion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/ca21b664-11b0-5976-b8fd-33bcedd93e36

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_map_germ_comap_ideal_eq_map_stalkMap_of_isOpenImmersion

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory

namespace G3bAux

open AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

noncomputable def G (I : X.IdealSheafData) (U : X.affineOpens) (y : X) (hy : y ∈ (U : X.Opens)) :
    Ideal (X.presheaf.stalk y) :=
  Ideal.map (X.presheaf.germ (U : X.Opens) y hy).hom (I.ideal U)

lemma G_eq_of_le (I : X.IdealSheafData) {U W : X.affineOpens} (h : W ≤ U) (y : X)
    (hyW : y ∈ (W : X.Opens)) (hyU : y ∈ (U : X.Opens)) : G I W y hyW = G I U y hyU := by
  unfold G
  rw [← I.map_ideal h, Ideal.map_map, ← CommRingCat.hom_comp]
  erw [TopCat.Presheaf.germ_res]

lemma G_eq (I : X.IdealSheafData) (U₁ U₂ : X.affineOpens) (y : X)
    (h₁ : y ∈ (U₁ : X.Opens)) (h₂ : y ∈ (U₂ : X.Opens)) : G I U₁ y h₁ = G I U₂ y h₂ := by
  obtain ⟨r, hle, hyr⟩ := U₁.2.exists_basicOpen_le ⟨y, h₂⟩ h₁
  have hW : IsAffineOpen (X.basicOpen r) := U₁.2.basicOpen r
  rw [← G_eq_of_le I (U := U₁) (W := ⟨X.basicOpen r, hW⟩) (X.basicOpen_le r) y hyr h₁,
    ← G_eq_of_le I (U := U₂) (W := ⟨X.basicOpen r, hW⟩) hle y hyr h₂]

lemma G_comap {Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (I : Y.IdealSheafData)
    (U : X.affineOpens) (y : X) (hy : y ∈ (U : X.Opens)) :
    G (I.comap f) U y hy =
      Ideal.map (f.stalkMap y).hom
        (G I ⟨f ''ᵁ U, U.2.image_of_isOpenImmersion f⟩ (f.base y) ⟨y, hy, rfl⟩) := by
  unfold G
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]

  have hci : Ideal.comap (f.appIso U).inv.hom
      (I.ideal ⟨f ''ᵁ U, U.2.image_of_isOpenImmersion f⟩) =
      Ideal.map (f.appIso U).hom.hom (I.ideal ⟨f ''ᵁ U, U.2.image_of_isOpenImmersion f⟩) := by
    have hhi : (f.appIso (U : X.Opens)).inv.hom.comp (f.appIso (U : X.Opens)).hom.hom = RingHom.id _ := by
      rw [← CommRingCat.hom_comp, Iso.hom_inv_id, CommRingCat.hom_id]
    have hih : ∀ a, (f.appIso (U : X.Opens)).hom.hom ((f.appIso (U : X.Opens)).inv.hom a) = a := by
      intro a
      rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Iso.inv_hom_id, CommRingCat.hom_id, RingHom.id_apply]
    apply le_antisymm
    · intro a ha
      rw [Ideal.mem_comap] at ha
      rw [← hih a]
      exact Ideal.mem_map_of_mem _ ha
    · rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap, hhi, Ideal.comap_id]
  rw [hci, Ideal.map_map, Ideal.map_map]
  congr 1

  rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Scheme.Hom.appIso_hom, Category.assoc]
  erw [TopCat.Presheaf.germ_res]
  rw [Scheme.Hom.germ_stalkMap]

lemma map_le_map_iff_of_isIso {R S : CommRingCat.{u}} (φ : R ⟶ S) [IsIso φ] (A B : Ideal R) :
    Ideal.map φ.hom A ≤ Ideal.map φ.hom B ↔ A ≤ B := by
  constructor
  · intro h
    have := Ideal.map_mono (f := (inv φ).hom) h
    rwa [Ideal.map_map, Ideal.map_map, ← CommRingCat.hom_comp, IsIso.hom_inv_id, CommRingCat.hom_id,
      Ideal.map_id, Ideal.map_id] at this
  · exact Ideal.map_mono

end G3bAux

open G3bAux in

theorem solution
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (I : Y.IdealSheafData) (x : X)
    (U : Y.affineOpens) (hU : f.base x ∈ (U : Y.Opens)) (V : X.affineOpens) (hV : x ∈ (V : X.Opens)) :
    Ideal.map (X.presheaf.germ (V : X.Opens) x hV).hom ((I.comap f).ideal V) =
      Ideal.map (f.stalkMap x).hom (Ideal.map (Y.presheaf.germ (U : Y.Opens) (f.base x) hU).hom (I.ideal U)) := by
  change G (I.comap f) V x hV = Ideal.map (f.stalkMap x).hom (G I U (f.base x) hU)
  rw [G_comap f I V x hV, G_eq I ⟨f ''ᵁ V, V.2.image_of_isOpenImmersion f⟩ U (f.base x) ⟨x, hV, rfl⟩ hU]

end S_AlgebraicGeometry_Scheme_IdealSheafData_map_germ_comap_ideal_eq_map_stalkMap_of_isOpenImmersion
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_map_germ_comap_ideal_eq_map_stalkMap_of_isOpenImmersion (solution)
