-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.exists_isIso_comp_fst_comp_fst_eq_and_translate_comp_eq_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/9cb45ce4-5fcc-5111-9af9-f9e48cb893fe

import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_exists_isIso_comp_fst_comp_fst_eq_and_translate_comp_eq_of_isPullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

namespace TBCSol

theorem mul_val_congr {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)} (h : t₁ = t₂)
    (P₁ Q₁ : SchemeHomOver t₁ f) (P₂ Q₂ : SchemeHomOver t₂ f) (hP : P₁.1 = P₂.1) (hQ : Q₁.1 = Q₂.1) :
    (L.mul t₁ P₁ Q₁).1 = (L.mul t₂ P₂ Q₂).1 := by
  subst h
  obtain rfl : P₁ = P₂ := Subtype.ext hP
  obtain rfl : Q₁ = Q₂ := Subtype.ext hQ
  rfl

theorem translate_fst' {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    {R : Type} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver t f) :
    Polarisation.translate f L t x ≫ pullback.fst f t =
      (L.mul (pullback.snd f t ≫ t) ⟨pullback.fst f t, pullback.condition⟩ (schemeHomOverComp (pullback.snd f t) rfl x)).1 :=
  pullback.lift_fst _ _ _

end TBCSol

theorem solution
    {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T)
    {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of T)}
    (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw T f')
    (gA : A' ⟶ A) (hg : CategoryTheory.IsPullback gA f' f (Spec.map (CommRingCat.ofHom φ)))
    (hmul : ∀ {T'' : Scheme.{0}} (t'' : T'' ⟶ Spec (CommRingCat.of T)) (x y : SchemeHomOver t'' f'),
      (L'.mul t'' x y).1 ≫ gA =
        (L.mul (t'' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨x.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩).1)
    (x₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of T))) f')
    (hx : x.1 ≫ gA = Spec.map (CommRingCat.ofHom φ) ≫ x₀.1) :
    ∃ κ : pullback f' (𝟙 (Spec (CommRingCat.of T))) ⟶
        pullback (pullback.snd f (𝟙 (Spec (CommRingCat.of S)))) (Spec.map (CommRingCat.ofHom φ)),
      IsIso κ ∧
      κ ≫ pullback.fst (pullback.snd f (𝟙 (Spec (CommRingCat.of S)))) (Spec.map (CommRingCat.ofHom φ)) ≫
          pullback.fst f (𝟙 (Spec (CommRingCat.of S))) =
        pullback.fst f' (𝟙 (Spec (CommRingCat.of T))) ≫ gA ∧
      Polarisation.translate f' L' (𝟙 (Spec (CommRingCat.of T))) x ≫ κ ≫
          pullback.fst (pullback.snd f (𝟙 (Spec (CommRingCat.of S)))) (Spec.map (CommRingCat.ofHom φ)) =
        κ ≫ pullback.fst (pullback.snd f (𝟙 (Spec (CommRingCat.of S)))) (Spec.map (CommRingCat.ofHom φ)) ≫
          Polarisation.translate f L (𝟙 (Spec (CommRingCat.of S))) x₀ := by

  have hsq : (pullback.fst f' (𝟙 (Spec (CommRingCat.of T))) ≫ gA) ≫ f =
      (pullback.snd f' (𝟙 (Spec (CommRingCat.of T))) ≫ Spec.map (CommRingCat.ofHom φ)) ≫ 𝟙 _ := by
    rw [Category.comp_id, Category.assoc, hg.w, ← Category.assoc, pullback.condition, Category.assoc, Category.id_comp]

  let a : pullback f' (𝟙 (Spec (CommRingCat.of T))) ⟶ pullback f (𝟙 (Spec (CommRingCat.of S))) :=
    pullback.lift (pullback.fst f' (𝟙 _) ≫ gA) (pullback.snd f' (𝟙 _) ≫ Spec.map (CommRingCat.ofHom φ)) hsq
  have ha₁ : a ≫ pullback.fst f (𝟙 _) = pullback.fst f' (𝟙 _) ≫ gA := pullback.lift_fst _ _ _
  have ha₂ : a ≫ pullback.snd f (𝟙 _) = pullback.snd f' (𝟙 _) ≫ Spec.map (CommRingCat.ofHom φ) := pullback.lift_snd _ _ _

  let κ : pullback f' (𝟙 (Spec (CommRingCat.of T))) ⟶
      pullback (pullback.snd f (𝟙 (Spec (CommRingCat.of S)))) (Spec.map (CommRingCat.ofHom φ)) :=
    pullback.lift a (pullback.snd f' (𝟙 _)) ha₂
  have hκ₁ : κ ≫ pullback.fst _ _ = a := pullback.lift_fst _ _ _
  have hκ₂ : κ ≫ pullback.snd _ _ = pullback.snd f' (𝟙 _) := pullback.lift_snd _ _ _

  have hsq' : (pullback.fst (pullback.snd f (𝟙 (Spec (CommRingCat.of S)))) (Spec.map (CommRingCat.ofHom φ)) ≫
        pullback.fst f (𝟙 _)) ≫ f =
      pullback.snd (pullback.snd f (𝟙 (Spec (CommRingCat.of S)))) (Spec.map (CommRingCat.ofHom φ)) ≫
        Spec.map (CommRingCat.ofHom φ) := by
    rw [Category.assoc, pullback.condition, Category.comp_id, pullback.condition]
  let a' : pullback (pullback.snd f (𝟙 (Spec (CommRingCat.of S)))) (Spec.map (CommRingCat.ofHom φ)) ⟶ A' :=
    hg.lift (pullback.fst _ _ ≫ pullback.fst f (𝟙 _)) (pullback.snd _ _) hsq'
  have ha'₁ : a' ≫ gA = pullback.fst _ _ ≫ pullback.fst f (𝟙 _) := hg.lift_fst _ _ _
  have ha'₂ : a' ≫ f' = pullback.snd _ _ := hg.lift_snd _ _ _
  let κ' : pullback (pullback.snd f (𝟙 (Spec (CommRingCat.of S)))) (Spec.map (CommRingCat.ofHom φ)) ⟶
      pullback f' (𝟙 (Spec (CommRingCat.of T))) :=
    pullback.lift a' (pullback.snd _ _) (by rw [ha'₂, Category.comp_id])
  have hκ'₁ : κ' ≫ pullback.fst f' (𝟙 _) = a' := pullback.lift_fst _ _ _
  have hκ'₂ : κ' ≫ pullback.snd f' (𝟙 _) = pullback.snd _ _ := pullback.lift_snd _ _ _

  have h1 : κ ≫ κ' = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hκ'₁, Category.id_comp]
      apply hg.hom_ext
      · rw [Category.assoc, ha'₁, ← Category.assoc, hκ₁, ha₁]
      · rw [Category.assoc, ha'₂, hκ₂, pullback.condition, Category.comp_id]
    · rw [Category.assoc, hκ'₂, hκ₂, Category.id_comp]
  have h2 : κ' ≫ κ = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hκ₁, Category.id_comp]
      apply pullback.hom_ext
      · rw [Category.assoc, ha₁, ← Category.assoc, hκ'₁, ha'₁]
      · rw [Category.assoc, ha₂, ← Category.assoc, hκ'₂, pullback.condition]
    · rw [Category.assoc, hκ₂, hκ'₂, Category.id_comp]
  refine ⟨κ, ⟨⟨κ', h1, h2⟩⟩, ?_, ?_⟩
  · rw [← Category.assoc, hκ₁, ha₁]
  ·
    rw [← Category.assoc κ, hκ₁]
    apply pullback.hom_ext
    · rw [Category.assoc, ha₁, ← Category.assoc, TBCSol.translate_fst', Category.assoc, TBCSol.translate_fst']

      rw [hmul]
      have hnat := congrArg Subtype.val
        (L.mul_natural (pullback.snd f (𝟙 (Spec (CommRingCat.of S))) ≫ 𝟙 _)
          (a ≫ pullback.snd f (𝟙 (Spec (CommRingCat.of S))) ≫ 𝟙 _) a rfl
          ⟨pullback.fst f (𝟙 _), pullback.condition⟩
          (schemeHomOverComp (pullback.snd f (𝟙 (Spec (CommRingCat.of S)))) rfl x₀))
      rw [schemeHomOverComp_coe] at hnat
      rw [hnat]
      apply TBCSol.mul_val_congr L
      · rw [← Category.assoc, ha₂, Category.comp_id, Category.assoc, Category.comp_id]
      · rw [schemeHomOverComp_coe, ha₁]
      · show (pullback.snd f' (𝟙 _) ≫ x.1) ≫ gA = a ≫ pullback.snd f (𝟙 _) ≫ x₀.1
        rw [Category.assoc, hx, ← Category.assoc, ← ha₂, Category.assoc]
    · rw [Category.assoc, ha₂, ← Category.assoc, Polarisation.translate_snd, Category.assoc, Polarisation.translate_snd, ha₂]

end S_AlgebraicGeometry_Polarisation_exists_isIso_comp_fst_comp_fst_eq_and_translate_comp_eq_of_isPullback
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_exists_isIso_comp_fst_comp_fst_eq_and_translate_comp_eq_of_isPullback (solution)
