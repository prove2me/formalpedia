-- Prove2me | solution 1 for AlgebraicGeometry.isOpenImmersion_of_isIso_stalkMap_genericPoint_of_injective_points_of_smoothOfRelativeDimension_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/06a5f5ba-d7ad-58a5-9f8c-35fd59f796de

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuliTower
import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Theorems.Thm_AlgebraicCurve_isClosed_singleton_of_ne_genericPoint
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_isDiscreteValuationRing_stalk_of_isClosed
import Theorems.Thm_IsDiscreteValuationRing_exists_algebraMap_eq_of_mem_subring_of_ne_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isOpenImmersion_of_isIso_stalkMap_genericPoint_of_injective_points_of_smoothOfRelativeDimension_one

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_isOpenImmersion_of_isIso_stalkMap_genericPoint_of_injective_points_of_smoothOfRelativeDimension_one.AlgebraicGeometry AlgebraicCurve NeronModelInfra Topology TopologicalSpace"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "IsLocallyNoetherian Surjective IsOpenImmersion.of_isIso_stalkMap Flat.of_stalkMap SmoothOfRelativeDimension LocallyOfFiniteType.isLocallyNoetherian Scheme.Hom Scheme.Hom.germ_stalkMap_apply Scheme.Hom.stalkSpecializes_stalkMap_apply LocallyOfFiniteType Spec IsIntegral Scheme.Hom.stalkMap_comp Scheme IsOpenImmersion genericPoint_eq_of_isOpenImmersion pointEquivClosedPoint Flat Scheme.Hom.stalkSpecializes_stalkMap_assoc locallyOfFiniteType_of_comp IsSeparated ext_of_apply_closedPoint_eq LocallyOfFinitePresentation SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed"
namespace C2b
p2m_open "AlgebraicGeometry"

namespace FunctionFieldPull

variable {X Y Z : Scheme.{u}}

def pull [IrreducibleSpace X] [IrreducibleSpace Y] (f : X ⟶ Y)
    (h : f.base (genericPoint X) ⤳ genericPoint Y) : Y.functionField ⟶ X.functionField :=
  Y.presheaf.stalkSpecializes h ≫ f.stalkMap (genericPoint X)

section

variable [IrreducibleSpace X] [IrreducibleSpace Y] [IrreducibleSpace Z]

theorem pull_germ (f : X ⟶ Y) (h : f.base (genericPoint X) ⤳ genericPoint Y)
    (U : Y.Opens) (hU : genericPoint Y ∈ U) (s : Γ(Y, U)) :
    pull f h (Y.presheaf.germ U (genericPoint Y) hU s) =
      X.presheaf.germ (f ⁻¹ᵁ U) (genericPoint X) (h.mem_open U.isOpen hU) (f.app U s) := by
  simp only [pull, CommRingCat.comp_apply]
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply, Scheme.Hom.germ_stalkMap_apply]

theorem pull_algebraMap (f : X ⟶ Y) (h : f.base (genericPoint X) ⤳ genericPoint Y) (x : X)
    (a : Y.presheaf.stalk (f.base x)) :
    pull f h (algebraMap (Y.presheaf.stalk (f.base x)) Y.functionField a) =
      algebraMap (X.presheaf.stalk x) X.functionField (f.stalkMap x a) := by
  simp only [pull, RingHom.algebraMap_toAlgebra, CommRingCat.comp_apply]
  rw [TopCat.Presheaf.stalkSpecializes_comp_apply (Y.presheaf)]
  have := Scheme.Hom.stalkSpecializes_stalkMap_apply f (genericPoint X) x
    ((genericPoint_spec X).specializes trivial) a
  convert this using 2

theorem pull_id : pull (𝟙 X) (specializes_refl _) = 𝟙 _ := by
  simp [pull]

theorem pull_comp (f : X ⟶ Y) (g : Y ⟶ Z) (hf : f.base (genericPoint X) ⤳ genericPoint Y)
    (hg : g.base (genericPoint Y) ⤳ genericPoint Z) :
    pull (f ≫ g) ((g.base.hom.map_specializes hf).trans hg) = pull g hg ≫ pull f hf := by
  simp only [pull, Scheme.Hom.stalkMap_comp, Category.assoc]
  rw [← Scheme.Hom.stalkSpecializes_stalkMap_assoc g (f.base (genericPoint X)) (genericPoint Y) hf]
  rw [← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp]
  rfl

end

variable [IsIntegral X] [IsIntegral Y]

theorem specializes_of_iso (e : X ≅ Y) : e.hom.base (genericPoint X) ⤳ genericPoint Y :=
  (genericPoint_eq_of_isOpenImmersion e.hom).symm ▸ specializes_refl _

theorem specializes_of_iso_inv (e : X ≅ Y) : e.inv.base (genericPoint Y) ⤳ genericPoint X :=
  specializes_of_iso e.symm

def equivOfIso (e : X ≅ Y) : Y.functionField ≃+* X.functionField :=
  (({ hom := pull e.hom (specializes_of_iso e)
      inv := pull e.inv (specializes_of_iso_inv e)
      hom_inv_id := by
        have h := (pull_comp e.inv e.hom (specializes_of_iso_inv e) (specializes_of_iso e)).symm
        rw [h]
        have : ∀ (k : (e.inv ≫ e.hom).base (genericPoint Y) ⤳ genericPoint Y),
            pull (e.inv ≫ e.hom) k = 𝟙 _ := by
          rw [e.inv_hom_id]; intro k; exact pull_id
        exact this _
      inv_hom_id := by
        have h := (pull_comp e.hom e.inv (specializes_of_iso e) (specializes_of_iso_inv e)).symm
        rw [h]
        have : ∀ (k : (e.hom ≫ e.inv).base (genericPoint X) ⤳ genericPoint X),
            pull (e.hom ≫ e.inv) k = 𝟙 _ := by
          rw [e.hom_inv_id]; intro k; exact pull_id
        exact this _ } : Y.functionField ≅ X.functionField)).commRingCatIsoToRingEquiv

theorem equivOfIso_apply (e : X ≅ Y) (a : Y.functionField) :
    equivOfIso e a = pull e.hom (specializes_of_iso e) a := rfl

theorem equivOfIso_symm_apply (e : X ≅ Y) (a : X.functionField) :
    (equivOfIso e).symm a = pull e.inv (specializes_of_iso_inv e) a := rfl

theorem map_equivOfIso_range_stalk (e : X ≅ Y) (x : X) :
    (algebraMap (Y.presheaf.stalk (e.hom.base x)) Y.functionField).range.map
        (equivOfIso e).toRingHom =
      (algebraMap (X.presheaf.stalk x) X.functionField).range := by
  haveI : IsIso (e.hom.stalkMap x) := inferInstance
  ext b
  simp only [Subring.mem_map, RingHom.mem_range, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨e.hom.stalkMap x a, (pull_algebraMap e.hom (specializes_of_iso e) x a).symm⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨a', rfl⟩ : ∃ a', e.hom.stalkMap x a' = a :=
      ⟨inv (e.hom.stalkMap x) a, by
        rw [← CommRingCat.comp_apply, IsIso.inv_hom_id]; rfl⟩
    exact ⟨_, ⟨a', rfl⟩, pull_algebraMap e.hom (specializes_of_iso e) x a'⟩

theorem image_equivOfIso_range_stalk (e : X ≅ Y) (x : X) :
    (equivOfIso e) ''
        ((algebraMap (Y.presheaf.stalk (e.hom.base x)) Y.functionField).range : Set _) =
      ((algebraMap (X.presheaf.stalk x) X.functionField).range : Set _) := by
  have h := congrArg (fun S : Subring X.functionField => (S : Set X.functionField))
    (map_equivOfIso_range_stalk e x)
  simpa [Subring.coe_map] using h

theorem image_equivOfIso_symm_range_stalk (e : X ≅ Y) (x : X) :
    (equivOfIso e).symm '' ((algebraMap (X.presheaf.stalk x) X.functionField).range : Set _) =
      ((algebraMap (Y.presheaf.stalk (e.hom.base x)) Y.functionField).range : Set _) := by
  rw [← image_equivOfIso_range_stalk e x, ← Set.image_comp]
  simp

theorem pull_baseToFunctionField {K : Type u} [Field K] (f : X ⟶ Y)
    (h : f.base (genericPoint X) ⤳ genericPoint Y)
    (cX : X ⟶ Spec (CommRingCat.of K)) (cY : Y ⟶ Spec (CommRingCat.of K)) (hf : f ≫ cY = cX)
    (a : K) :
    pull f h (baseToFunctionField cY a) = baseToFunctionField cX a := by
  subst hf
  simp only [baseToFunctionField, RingHom.coe_comp, Function.comp_apply]
  change pull f h (Y.presheaf.germ ⊤ (genericPoint Y) trivial _) =
    X.presheaf.germ ⊤ (genericPoint X) trivial _
  rw [pull_germ]
  rfl

theorem equivOfIso_baseToFunctionField {K : Type u} [Field K] (e : X ≅ Y)
    (cX : X ⟶ Spec (CommRingCat.of K)) (cY : Y ⟶ Spec (CommRingCat.of K))
    (hf : e.hom ≫ cY = cX) (a : K) :
    equivOfIso e (baseToFunctionField cY a) = baseToFunctionField cX a :=
  pull_baseToFunctionField e.hom _ cX cY hf a

end FunctionFieldPull

open FunctionFieldPull

theorem closed_or_generic {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsIntegral X] [SmoothOfRelativeDimension 1 f] (x : X) :
    IsClosed ({x} : Set X) ∨ x = genericPoint X := by
  by_cases hx : x = genericPoint X
  · exact Or.inr hx
  · exact Or.inl (AlgebraicCurve.isClosed_singleton_of_ne_genericPoint f x hx)

section Core

variable {K : Type} [Field K] [IsAlgClosed K]
  {Y X : Scheme.{0}} (gY : Y ⟶ Spec (CommRingCat.of K)) (gX : X ⟶ Spec (CommRingCat.of K))
  [IsIntegral Y] [IsIntegral X]
  [hY : SmoothOfRelativeDimension 1 gY] [hX : SmoothOfRelativeDimension 1 gX]
  (h : Y ⟶ X) (hh : h ≫ gX = gY)
  (hgen : h.base (genericPoint Y) = genericPoint X) (hbir : IsIso (h.stalkMap (genericPoint Y)))

include hgen in
theorem spec : h.base (genericPoint Y) ⤳ genericPoint X := by rw [hgen]

include hgen hbir in

theorem isIso_pull : IsIso (pull h (spec h hgen)) := by

  have : IsIso (X.presheaf.stalkSpecializes (spec h hgen)) := by
    have h2 : genericPoint X ⤳ h.base (genericPoint Y) := by rw [hgen]
    refine ⟨⟨X.presheaf.stalkSpecializes h2, ?_, ?_⟩⟩
    · rw [TopCat.Presheaf.stalkSpecializes_comp]; exact TopCat.Presheaf.stalkSpecializes_refl _ _
    · rw [TopCat.Presheaf.stalkSpecializes_comp]; exact TopCat.Presheaf.stalkSpecializes_refl _ _
  unfold pull
  infer_instance

include hh in

theorem isClosed_image {y : Y} (hy : IsClosed ({y} : Set Y)) : IsClosed ({h.base y} : Set X) := by
  haveI : LocallyOfFiniteType gY := inferInstance
  haveI : LocallyOfFiniteType gX := inferInstance
  set p := (pointEquivClosedPoint gY).symm ⟨y, hy⟩ with hp
  have hpy : p.1.base (IsLocalRing.closedPoint K) = y := by
    have := congrArg Subtype.val ((pointEquivClosedPoint gY).apply_symm_apply ⟨y, hy⟩)
    rw [← hp] at this
    exact this
  have hq : (p.1 ≫ h) ≫ gX = 𝟙 _ := by rw [Category.assoc, hh]; exact p.2
  have := ((pointEquivClosedPoint gX) ⟨p.1 ≫ h, hq⟩).2
  have hval : ((pointEquivClosedPoint gX) ⟨p.1 ≫ h, hq⟩).1 = h.base y := by
    show (p.1 ≫ h).base (IsLocalRing.closedPoint K) = h.base y
    rw [← hpy]; rfl
  rw [← hval]; exact this

include hh hgen hbir in

theorem stalkMap_bijective_of_isClosed {y : Y} (hy : IsClosed ({y} : Set Y)) :
    Function.Bijective (h.stalkMap y).hom := by
  haveI hDVRy : IsDiscreteValuationRing (Y.presheaf.stalk y) :=
    SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed gY y hy
  haveI hDVRx : IsDiscreteValuationRing (X.presheaf.stalk (h.base y)) :=
    SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed gX (h.base y) (isClosed_image gY gX h hh hy)
  haveI := isIso_pull h hgen hbir

  let ψ : X.functionField ≅ Y.functionField := asIso (pull h (spec h hgen))
  let W : Subring X.functionField :=
    (algebraMap (Y.presheaf.stalk y) Y.functionField).range.map ψ.inv.hom
  have hVW : ∀ v : X.presheaf.stalk (h.base y), algebraMap _ X.functionField v ∈ W := by
    intro v
    refine ⟨algebraMap _ Y.functionField (h.stalkMap y v), ⟨_, rfl⟩, ?_⟩
    rw [← pull_algebraMap h (spec h hgen) y v]
    show (ψ.hom ≫ ψ.inv) _ = _
    rw [ψ.hom_inv_id]; rfl
  have hW : W ≠ ⊤ := by
    intro hWtop
    apply IsDiscreteValuationRing.not_isField (Y.presheaf.stalk y)
    have hsurj : Function.Surjective (algebraMap (Y.presheaf.stalk y) Y.functionField) := by
      intro a
      have : ψ.inv a ∈ W := hWtop.symm ▸ Subring.mem_top _
      obtain ⟨b, ⟨w, rfl⟩, hb⟩ := this
      refine ⟨w, ?_⟩
      have hinj : Function.Injective ψ.inv.hom := (ConcreteCategory.bijective_of_isIso ψ.inv).1
      exact hinj hb
    have hinj := IsFractionRing.injective (Y.presheaf.stalk y) Y.functionField
    exact MulEquiv.isField (Field.toIsField Y.functionField)
      (RingEquiv.ofBijective (algebraMap (Y.presheaf.stalk y) Y.functionField) ⟨hinj, hsurj⟩).toMulEquiv
  constructor
  · intro v w hvw
    apply IsFractionRing.injective (X.presheaf.stalk (h.base y)) X.functionField
    apply (ConcreteCategory.bijective_of_isIso ψ.hom).1
    show pull h (spec h hgen) (algebraMap _ _ v) = pull h (spec h hgen) (algebraMap _ _ w)
    rw [pull_algebraMap, pull_algebraMap, hvw]
  · intro w
    obtain ⟨v, hv⟩ := IsDiscreteValuationRing.exists_algebraMap_eq_of_mem_subring_of_ne_top
      (X.presheaf.stalk (h.base y)) X.functionField W hVW hW (ψ.inv (algebraMap _ Y.functionField w))
      ⟨_, ⟨w, rfl⟩, rfl⟩
    refine ⟨v, ?_⟩
    apply IsFractionRing.injective (Y.presheaf.stalk y) Y.functionField
    rw [← pull_algebraMap h (spec h hgen) y v]
    have := congrArg ψ.hom hv
    show ψ.hom (algebraMap _ _ v) = _
    rw [this]
    show (ψ.inv ≫ ψ.hom) _ = _
    rw [ψ.inv_hom_id]; rfl

include hh hgen hbir in
theorem isIso_stalkMap (y : Y) : IsIso (h.stalkMap y) := by
  rcases closed_or_generic gY y with hy | rfl
  · have hb := stalkMap_bijective_of_isClosed gY gX h hh hgen hbir hy
    exact (RingEquiv.ofBijective (h.stalkMap y).hom hb).toCommRingCatIso.isIso_hom
  · exact hbir

end Core

end AlgebraicGeometry.C2b

open AlgebraicGeometry.C2b AlgebraicGeometry.C2b.FunctionFieldPull

theorem solution
    {K : Type} [Field K] [IsAlgClosed K]
    {Y X : Scheme.{0}} (gY : Y ⟶ Spec (CommRingCat.of K)) (gX : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral Y] [IsIntegral X] [IsSeparated gY] [IsSeparated gX]
    (hY : SmoothOfRelativeDimension 1 gY) (hX : SmoothOfRelativeDimension 1 gX)
    (h : Y ⟶ X) (hh : h ≫ gX = gY)
    (hgen : h.base (genericPoint Y) = genericPoint X) (hbir : IsIso (h.stalkMap (genericPoint Y)))
    (hinj : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of K))
      (P P' : SchemeHomOver s gY), P.1 ≫ h = P'.1 ≫ h → P = P') :
    IsOpenImmersion h := by
  haveI := hY; haveI := hX
  haveI hlftY : LocallyOfFiniteType gY := inferInstance
  haveI hlftX : LocallyOfFiniteType gX := inferInstance

  haveI hst : ∀ y : Y, IsIso (h.stalkMap y) := fun y => isIso_stalkMap gY gX h hh hgen hbir y

  haveI : Flat h := Flat.of_stalkMap h (fun y => RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso (h.stalkMap y)))
  haveI : LocallyOfFiniteType h := by
    haveI : LocallyOfFiniteType (h ≫ gX) := by rw [hh]; infer_instance
    exact locallyOfFiniteType_of_comp h gX
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian gX
  haveI : LocallyOfFinitePresentation h := inferInstance
  have hopen : IsOpenMap h.base := h.isOpenMap

  have hinjb : Function.Injective h.base := by
    intro y₁ y₂ he
    rcases closed_or_generic gY y₁ with h₁ | h₁ <;> rcases closed_or_generic gY y₂ with h₂ | h₂
    ·
      set p₁ := (pointEquivClosedPoint gY).symm ⟨y₁, h₁⟩
      set p₂ := (pointEquivClosedPoint gY).symm ⟨y₂, h₂⟩
      have hp₁ : p₁.1.base (IsLocalRing.closedPoint K) = y₁ :=
        congrArg Subtype.val ((pointEquivClosedPoint gY).apply_symm_apply ⟨y₁, h₁⟩)
      have hp₂ : p₂.1.base (IsLocalRing.closedPoint K) = y₂ :=
        congrArg Subtype.val ((pointEquivClosedPoint gY).apply_symm_apply ⟨y₂, h₂⟩)
      have hq₁ : (p₁.1 ≫ h) ≫ gX = 𝟙 _ := by rw [Category.assoc, hh]; exact p₁.2
      have hq₂ : (p₂.1 ≫ h) ≫ gX = 𝟙 _ := by rw [Category.assoc, hh]; exact p₂.2
      have heq : p₁.1 ≫ h = p₂.1 ≫ h := by
        apply ext_of_apply_closedPoint_eq gX hq₁ hq₂
        show h.base (p₁.1.base _) = h.base (p₂.1.base _)
        rw [hp₁, hp₂, he]
      have := hinj K (𝟙 _) ⟨p₁.1, p₁.2⟩ ⟨p₂.1, p₂.2⟩ heq
      have : p₁.1 = p₂.1 := congrArg Subtype.val this
      rw [← hp₁, ← hp₂, this]
    · exfalso

      subst h₂
      have hc : IsClosed ({genericPoint X} : Set X) := by rw [← hgen, ← he]; exact isClosed_image gY gX h hh h₁
      haveI := SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed gX _ hc
      exact IsDiscreteValuationRing.not_isField (X.presheaf.stalk (genericPoint X)) (Field.toIsField X.functionField)
    · exfalso
      subst h₁
      have hc : IsClosed ({genericPoint X} : Set X) := by rw [← hgen, he]; exact isClosed_image gY gX h hh h₂
      haveI := SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed gX _ hc
      exact IsDiscreteValuationRing.not_isField (X.presheaf.stalk (genericPoint X)) (Field.toIsField X.functionField)
    · rw [h₁, h₂]
  exact IsOpenImmersion.of_isIso_stalkMap h
    (IsOpenEmbedding.of_continuous_injective_isOpenMap h.continuous hinjb hopen)

end
end S_AlgebraicGeometry_isOpenImmersion_of_isIso_stalkMap_genericPoint_of_injective_points_of_smoothOfRelativeDimension_one
end P2MW
export P2MW.S_AlgebraicGeometry_isOpenImmersion_of_isIso_stalkMap_genericPoint_of_injective_points_of_smoothOfRelativeDimension_one (solution)
