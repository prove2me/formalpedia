-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
-- name    : Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:31:59.227135+00:00
-- url     : https://prove2.me/theorems/7f8d33eb-1da2-43d1-9c34-6ac7e7a41030
-- title:
--   Exists Unique Torus Compat
-- statement:
--   Definitions and structural lemmas for Exists Unique Torus Compat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Uniformization/ExistsUniqueTorusCompat.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Theorems.Thm_GlobalTheory_SplitTorus_charUnit_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UU
def TorusCompat {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} {X : Type} [AddCommGroup X] (f : S' ⟶ S)
    (F : G'.left ⟶ G.left) (i' : splitTorus S' X ⟶ G') (i : splitTorus S X ⟶ G) : Prop :=
  ∃ τ : (splitTorus S' X).left ⟶ (splitTorus S X).left, τ ≫ (splitTorus S X).hom = (splitTorus S' X).hom ≫ f ∧
    (∀ χ, τ.appTop.hom (charUnit S X χ).val = (charUnit S' X χ).val) ∧ τ ≫ i.left = i'.left ≫ F
abbrev red {A : Type} [CommRing A] (J : Ideal A) : Spec (CommRingCat.of (A ⧸ J)) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
section API
open SplitTorus (bcMap bcMap_hom)
variable {S S' S'' : Scheme.{0}} {X : Type} [AddCommGroup X]
theorem bcMap_charUnit (f : S' ⟶ S) (χ : X) :
    (bcMap f X).appTop.hom (charUnit S X χ).val = (charUnit S' X χ).val := by
  rw [SplitTorus.charUnit_val, SplitTorus.charUnit_val, SplitTorus.bcMap_appTop_chi]
theorem splitTorus_left_hom_ext {Z : Scheme.{0}} (a b : Z ⟶ (splitTorus S X).left)
    (h : a ≫ (splitTorus S X).hom = b ≫ (splitTorus S X).hom)
    (hχ : ∀ χ, a.appTop.hom (charUnit S X χ).val = b.appTop.hom (charUnit S X χ).val) : a = b := by
  let a' : Over.mk (a ≫ (splitTorus S X).hom) ⟶ splitTorus S X := Over.homMk a
  let b' : Over.mk (a ≫ (splitTorus S X).hom) ⟶ splitTorus S X :=
    Over.homMk b (by simpa using h.symm)
  have hab : a' = b' := SplitTorus.hom_ext fun χ => by
    rw [SplitTorus.val_eq, SplitTorus.val_eq]
    have hc := hχ χ
    rw [SplitTorus.charUnit_val] at hc
    exact hc
  exact congrArg CommaMorphism.left hab
theorem eq_bcMap {f : S' ⟶ S} {τ : (splitTorus S' X).left ⟶ (splitTorus S X).left}
    (h : τ ≫ (splitTorus S X).hom = (splitTorus S' X).hom ≫ f)
    (hχ : ∀ χ, τ.appTop.hom (charUnit S X χ).val = (charUnit S' X χ).val) : τ = bcMap f X :=
  splitTorus_left_hom_ext _ _ (by rw [h, bcMap_hom]) fun χ => by rw [hχ, bcMap_charUnit]
theorem bcMap_id : bcMap (𝟙 S) X = 𝟙 _ :=
  (eq_bcMap (τ := 𝟙 _) (by simp) fun χ => by simp).symm
variable {G'' : Over S''} {G' : Over S'} {G : Over S}
theorem torusCompat_iff {f : S' ⟶ S} {F : G'.left ⟶ G.left} {i' : splitTorus S' X ⟶ G'}
    {i : splitTorus S X ⟶ G} : TorusCompat f F i' i ↔ bcMap f X ≫ i.left = i'.left ≫ F := by
  constructor
  · rintro ⟨τ, h₁, h₂, h₃⟩
    rw [← eq_bcMap h₁ h₂]
    exact h₃
  · intro h
    exact ⟨bcMap f X, bcMap_hom f X, fun χ => bcMap_charUnit f χ, h⟩
theorem TorusCompat.refl (i : splitTorus S X ⟶ G) : TorusCompat (𝟙 S) (𝟙 G.left) i i := by
  rw [torusCompat_iff, bcMap_id, Category.id_comp, Category.comp_id]
theorem torusCompat_id_iff {i' i : splitTorus S X ⟶ G} :
    TorusCompat (𝟙 S) (𝟙 G.left) i' i ↔ i' = i := by
  rw [torusCompat_iff, bcMap_id, Category.id_comp, Category.comp_id]
  constructor
  · intro h
    exact Over.OverMorphism.ext h.symm
  · rintro rfl
    rfl
theorem torusCompat_bcMap (f : S' ⟶ S) :
    TorusCompat f (bcMap f X) (𝟙 (splitTorus S' X)) (𝟙 (splitTorus S X)) := by
  rw [torusCompat_iff, Over.id_left, Over.id_left, Category.id_comp, Category.comp_id]
end API
instance isClosedImmersion_red {A : Type} [CommRing A] (J : Ideal A) : IsClosedImmersion (red J) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
example : TorusCompat (red (Ideal.span {(2 : ZMod 4)}))
    (SplitTorus.bcMap (red (Ideal.span {(2 : ZMod 4)})) ℤ) (𝟙 (splitTorus _ ℤ)) (𝟙 (splitTorus _ ℤ)) :=
  torusCompat_bcMap _
example (S : Scheme.{0}) (G : Over S) (i : splitTorus S ℤ ⟶ G) : TorusCompat (𝟙 S) (𝟙 _) i i :=
  TorusCompat.refl i
example : ¬ TorusCompat (𝟙 (Spec (CommRingCat.of ℚ))) (𝟙 _)
    (1 : splitTorus _ ℤ ⟶ splitTorus _ ℤ) (𝟙 (splitTorus _ ℤ)) := by
  rw [torusCompat_id_iff]
  intro h
  let S := Spec (CommRingCat.of ℚ)
  have hall : ∀ t : Over.mk (𝟙 S) ⟶ splitTorus S ℤ, t = 1 := fun t => by
    rw [← Category.comp_id t, ← h, MonObj.comp_one]
  let u : Γ(S, ⊤)ˣ := -1
  have h1 := SplitTorus.val_ofVal (T := Over.mk (𝟙 S)) (zmultiplesHom _ (Additive.ofMul u)) 1
  rw [hall (SplitTorus.ofVal _), SplitTorus.val_one] at h1
  have h2 : u = 1 := Units.ext (by simpa using h1.symm)
  have h3 := congrArg (fun v : Γ(S, ⊤)ˣ => (Scheme.ΓSpecIso (CommRingCat.of ℚ)).hom.hom v.val) h2
  simp only [u, Units.val_neg, Units.val_one, map_neg, map_one] at h3
  norm_num at h3
end GlobalTheory.UU
end


