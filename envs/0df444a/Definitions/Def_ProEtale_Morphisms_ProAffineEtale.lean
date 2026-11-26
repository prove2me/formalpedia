-- Prove2me | Definitions.Def_ProEtale_Morphisms_ProAffineEtale
-- name    : ProEtale_Morphisms_ProAffineEtale
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T12:13:10.792799+00:00
-- url     : https://prove2.me/theorems/8441ae1b-5df6-4672-bf4f-bc89e2552f41
-- title:
--   Pro-(affine étale) morphisms of schemes
-- statement:
--   The class `proAffineEtale` of morphisms of schemes $U \to X$ for which $U$ is the limit of a small cofiltered diagram of affine schemes $U_j$ equipped with compatible étale morphisms $U_j \to X$ through which $U \to X$ factors. Such a morphism has affine source and is weakly étale; a morphism between affine schemes belongs to the class if and only if the induced ring map on global sections is ind-étale.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014), Definition 4.2.1. Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Morphisms/ProAffineEtale.lean (declarations kept unchanged, unused ones removed).

/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import Definitions.Def_ProEtale_Algebra_Etale
import Definitions.Def_ProEtale_Algebra_FaithfullyFlat
import Definitions.Def_ProEtale_Algebra_Ind
import Definitions.Def_ProEtale_Algebra_IndEtale
import Definitions.Def_ProEtale_Algebra_IndWeaklyEtale
import Definitions.Def_ProEtale_Algebra_WeaklyEtale
import Definitions.Def_ProEtale_Mathlib_Algebra_Category_AlgCat_FilteredColimits
import Definitions.Def_ProEtale_Mathlib_Algebra_Category_CommAlgCat_Limits
import Definitions.Def_ProEtale_Mathlib_Algebra_Homology_ShortComplex_Exact
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Limits_Preserves_Shapes_Zero
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Comma
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Ind
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_OfObjectProperty
import Definitions.Def_ProEtale_Mathlib_RingTheory_Henselian
import Definitions.Def_ProEtale_Mathlib_RingTheory_Ideal_Pure
import Definitions.Def_ProEtale_Morphisms_WeaklyEtale

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Pro-affine-étale morphisms

In this file we define the class of pro-affine-étale morphisms of schemes:
These are the morphisms of the form `lim Xᵢ ⟶ S` where each `Xᵢ` is absolutely affine
and étale over `X`.
-/

universe u

open CategoryTheory Limits MorphismProperty


namespace AlgebraicGeometry

/-- This is the property of morphisms of schemes that are of the form `lim Xᵢ ⟶ S`
where each `Xᵢ` is absolutely affine and étale over `X`. -/
def proAffineEtale : MorphismProperty Scheme.{u} :=
  MorphismProperty.pro.{u} (@Etale ⊓ .ofObjectProperty (IsAffine ·) ⊤)

lemma proAffineEtale.of_isAffine {X Y : Scheme.{u}} [IsAffine X] (f : X ⟶ Y) [Etale f] :
    proAffineEtale f :=
  MorphismProperty.le_pro _ _ ⟨‹_›, ⟨‹_›, trivial⟩⟩

/-- The domain of a pro-affine étale morphism is affine. -/
lemma proAffineEtale.isAffine {X S : Scheme.{u}} {f : X ⟶ S} (hf : proAffineEtale f) :
    IsAffine X := by
  obtain ⟨J, _, _, D, t, s, hs, hts⟩ := hf
  have hAff (j : J) : IsAffine (D.obj j) := ofObjectProperty_top_right_iff.mp (hts j).1.2
  exact Scheme.isAffine_of_isLimit (Cone.mk _ s) hs

/-- `IsAffine` is preserved under isomorphisms. -/
instance : ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme.{u}) (IsAffine ·) where
  of_iso e h := (IsAffine.iff_of_isIso e.hom).mp h

instance : proAffineEtale.RespectsIso := by
  rw [proAffineEtale, pro_eq_unop_ind_op]
  infer_instance


/-- For any `MorphismProperty Scheme` `P` coming from a ring-hom property `Q` via
`HasRingHomProperty`, a morphism `Spec.map f` between affine schemes lies in
`pro (P ⊓ isAffine)` if and only if `f` lies in `ind (RingHom.toMorphismProperty Q)`.

The forward direction reflects a pro-affine cone of `Spec.map f` along the `Γ ⊣ Spec`
adjunction (an equivalence on affine objects) to a colimit cocone of ring maps; the
backward direction applies `Scheme.Spec` to such a colimit and packages the result
as a pro-cone. -/
lemma pro_inf_isAffine_Spec_iff (P : MorphismProperty Scheme.{u})
    {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    [HasRingHomProperty P Q] {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (MorphismProperty.pro.{u} (P ⊓ ofObjectProperty (IsAffine ·) ⊤)) (Spec.map f) ↔
      MorphismProperty.ind.{u} (RingHom.toMorphismProperty @Q) f := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨J, _, _, D, t, s, hs, hts⟩ := h
    have hAff (j : J) : IsAffine (D.obj j) :=
      ofObjectProperty_top_right_iff.mp (hts j).1.2
    let Φ : Jᵒᵖ ⥤ CommRingCat.{u} := D.op ⋙ Scheme.Γ
    let σ (j' : Jᵒᵖ) : Φ.obj j' ⟶ S :=
      Spec.preimage (s.app j'.unop ≫ (D.obj j'.unop).isoSpec.hom)
    let τ (j' : Jᵒᵖ) : R ⟶ Φ.obj j' :=
      Spec.preimage ((D.obj j'.unop).isoSpec.inv ≫ t.app j'.unop)
    have hSpec_σ (j' : Jᵒᵖ) :
        Spec.map (σ j') = s.app j'.unop ≫ (D.obj j'.unop).isoSpec.hom :=
      Spec.map_preimage _
    have hSpec_τ (j' : Jᵒᵖ) :
        Spec.map (τ j') = (D.obj j'.unop).isoSpec.inv ≫ t.app j'.unop :=
      Spec.map_preimage _
    let τNat : (Functor.const Jᵒᵖ).obj R ⟶ Φ :=
      { app := τ
        naturality := fun j' k' α ↦ by
          have : IsAffine (D.obj j'.unop) := hAff j'.unop
          have : IsAffine (D.obj k'.unop) := hAff k'.unop
          dsimp
          rw [Category.id_comp]
          apply Spec.map_injective
          rw [Spec.map_comp, hSpec_τ k', hSpec_τ j']
          have htn : t.app k'.unop = D.map α.unop ≫ t.app j'.unop := by
            have := t.naturality α.unop
            simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at this
            exact this.symm
          have hΦmap : Φ.map α = (D.map α.unop).appTop := Scheme.Γ_map_op (D.map α.unop)
          rw [htn, hΦmap]
          exact (Scheme.isoSpec_inv_naturality_assoc (D.map α.unop) (t.app j'.unop)).symm }
    let σNat : Φ ⟶ (Functor.const Jᵒᵖ).obj S :=
      { app := σ
        naturality := fun j' k' α ↦ by
          have : IsAffine (D.obj j'.unop) := hAff j'.unop
          have : IsAffine (D.obj k'.unop) := hAff k'.unop
          dsimp
          rw [Category.comp_id]
          apply Spec.map_injective
          rw [Spec.map_comp, hSpec_σ k', hSpec_σ j']
          have hsn : s.app j'.unop = s.app k'.unop ≫ D.map α.unop := by
            have := s.naturality α.unop
            simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at this
            exact this
          have hΦmap : Φ.map α = (D.map α.unop).appTop := Scheme.Γ_map_op (D.map α.unop)
          rw [hsn, hΦmap, Category.assoc, Scheme.isoSpec_hom_naturality, ← Category.assoc] }
    let legSpec (c' : Cocone Φ) (i : J) : Spec c'.pt ⟶ D.obj i :=
      Spec.map (c'.ι.app (Opposite.op i)) ≫ (D.obj i).isoSpec.inv
    let mkScheme (c' : Cocone Φ) : Cone D :=
      { pt := Spec c'.pt
        π :=
          { app := legSpec c'
            naturality := fun i i' α ↦ by
              have : IsAffine (D.obj i) := hAff i
              have : IsAffine (D.obj i') := hAff i'
              dsimp only [legSpec, Functor.const_obj_obj, Functor.const_obj_map]
              rw [Category.id_comp]
              have hcnat : Φ.map α.op ≫ c'.ι.app (Opposite.op i) =
                  c'.ι.app (Opposite.op i') := by
                have := c'.ι.naturality α.op
                simp only [Functor.const_obj_obj, Functor.const_obj_map,
                  Category.comp_id] at this
                exact this
              have hΦmap : Φ.map α.op = (D.map α).appTop := Scheme.Γ_map_op (D.map α)
              rw [hΦmap] at hcnat
              rw [← hcnat, Spec.map_comp, Category.assoc,
                Scheme.isoSpec_inv_naturality, ← Category.assoc] } }
    refine ⟨Jᵒᵖ, inferInstance, inferInstance, Φ, τNat, σNat, ?_, fun j' ↦ ⟨?_, ?_⟩⟩
    · refine
        { desc := fun c' ↦ Spec.preimage (hs.lift (mkScheme c'))
          fac := fun c' j' ↦ ?_
          uniq := fun c' m hm ↦ ?_ }
      · apply Spec.map_injective
        have : IsAffine (D.obj j'.unop) := hAff j'.unop
        have hliftFac : hs.lift (mkScheme c') ≫ s.app j'.unop =
            Spec.map (c'.ι.app (Opposite.op j'.unop)) ≫
              (D.obj j'.unop).isoSpec.inv := hs.fac (mkScheme c') j'.unop
        rw [Spec.map_comp, Spec.map_preimage, hSpec_σ, ← Category.assoc, hliftFac,
          Category.assoc, Iso.inv_hom_id, Category.comp_id]
      · apply Spec.map_injective
        refine (hs.uniq (mkScheme c') (Spec.map m) ?_).trans
          (Spec.map_preimage (hs.lift (mkScheme c'))).symm
        intro i
        have : IsAffine (D.obj i) := hAff i
        have hmi : σNat.app (Opposite.op i) ≫ m = c'.ι.app (Opposite.op i) :=
          hm (Opposite.op i)
        have hcπ : Spec.map (c'.ι.app (Opposite.op i)) =
            Spec.map m ≫ s.app i ≫ (D.obj i).isoSpec.hom := by
          rw [← hSpec_σ (Opposite.op i), ← Spec.map_comp, hmi]
        have hmkπ : (mkScheme c').π.app i =
            Spec.map (c'.ι.app (Opposite.op i)) ≫ (D.obj i).isoSpec.inv := rfl
        rw [hmkπ, hcπ, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · exact (HasRingHomProperty.Spec_iff (P := P)).mp <| by
        rw [hSpec_τ]
        exact MorphismProperty.RespectsIso.precomp _ _ _ (hts j'.unop).1.1
    · apply Spec.map_injective
      rw [Spec.map_comp, hSpec_σ, hSpec_τ, Category.assoc, ← Category.assoc _ _ (t.app _),
        Iso.hom_inv_id, Category.id_comp]
      exact (hts j'.unop).2
  · obtain ⟨J, _, _, D, t, s, hs, hts⟩ := h
    refine ⟨Jᵒᵖ, inferInstance, inferInstance, D.op ⋙ Scheme.Spec,
      { app j' := Spec.map (t.app j'.unop)
        naturality := fun j' k' α ↦ by
          dsimp
          have := t.naturality α.unop
          simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at this
          rw [Category.comp_id, ← Spec.map_comp, ← this] },
      { app j' := Spec.map (s.app j'.unop)
        naturality := fun j' k' α ↦ by
          dsimp
          have := s.naturality α.unop
          simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at this
          rw [Category.id_comp, ← Spec.map_comp, this] },
      ?_, fun j' ↦ ⟨⟨?_, ?_⟩, ?_⟩⟩
    · let c : Cocone D := Cocone.mk _ s
      have hSpecLimit : IsLimit (Scheme.Spec.mapCone c.op) :=
        isLimitOfPreserves Scheme.Spec hs.op
      refine IsLimit.ofIsoLimit hSpecLimit (Cone.ext (Iso.refl _) ?_)
      intro j'
      dsimp [c]
      simp
    · exact (HasRingHomProperty.Spec_iff (P := P)).mpr (hts j'.unop).1
    · exact ofObjectProperty_top_right_iff.mpr (AlgebraicGeometry.isAffine_Spec _)
    · rw [← Spec.map_comp]
      exact congrArg Spec.map (hts j'.unop).2

/-- A morphism `Spec.map f` between affine schemes is pro-affine étale if and only
if `f` is ind-étale. -/
lemma proAffineEtale_Spec_iff {R S : CommRingCat.{u}} {f : R ⟶ S} :
    proAffineEtale (Spec.map f) ↔ f.hom.IndEtale := by
  rw [proAffineEtale, pro_inf_isAffine_Spec_iff (P := @Etale) f, RingHom.IndEtale.iff_ind_etale]
  rfl

/-- A morphism between affine schemes is pro-affine étale if and only if the induced map
on global sections is ind-étale. -/
lemma proAffineEtale_iff_appTop {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] {f : X ⟶ Y} :
    proAffineEtale f ↔ f.appTop.hom.IndEtale := by
  have h : Spec.map f.appTop = X.isoSpec.inv ≫ f ≫ Y.isoSpec.hom := by
    rw [← Scheme.isoSpec_hom_naturality, Iso.inv_hom_id_assoc]
  rw [← proAffineEtale_Spec_iff, h,
    MorphismProperty.cancel_left_of_respectsIso (P := proAffineEtale.{u}),
    MorphismProperty.cancel_right_of_respectsIso (P := proAffineEtale.{u})]

/-- The projection from a pro-affine-étale presentation to any of its stages is
pro-affine-étale. -/
lemma proAffineEtale.app_mem {J : Type u} [SmallCategory J] [IsCofiltered J]
    {D : J ⥤ Scheme.{u}} {S X : Scheme.{u}} {t : D ⟶ (Functor.const J).obj S}
    {s : (Functor.const J).obj X ⟶ D} (hs : IsLimit (Cone.mk X s))
    (ht : ∀ j, (@Etale ⊓ ofObjectProperty (IsAffine ·) ⊤ :
      MorphismProperty Scheme.{u}) (t.app j)) (j₀ : J) :
    proAffineEtale (s.app j₀) := by
  refine MorphismProperty.pro_coneπ hs j₀ fun {i} u ↦ ⟨?_, ?_⟩
  · have h1 : D.map u ≫ t.app j₀ = t.app i := by simp
    exact MorphismProperty.of_postcomp (W := @Etale) (W' := @Etale) _ (t.app j₀)
      (ht j₀).1 (by rw [h1]; exact (ht i).1)
  · exact ofObjectProperty_top_right_iff.mpr (ofObjectProperty_top_right_iff.mp (ht i).2)


/-- Every pro-affine étale morphism is weakly-étale: it factors as the projection to a stage
of its presentation, which is ind-étale between affine schemes, followed by an étale map. -/
lemma proAffineEtale_le_weaklyEtale : proAffineEtale ≤ @WeaklyEtale := by
  intro X S f hf
  have : IsAffine X := hf.isAffine
  obtain ⟨J, _, _, D, t, s, hs, hts⟩ := hf
  obtain ⟨j₀⟩ : Nonempty J := IsCofiltered.nonempty
  have : IsAffine (D.obj j₀) := ofObjectProperty_top_right_iff.mp (hts j₀).1.2
  have : Etale (t.app j₀) := (hts j₀).1.1
  have : IsAffine (((Functor.const J).obj X).obj j₀) := ‹IsAffine X›
  have hπ := proAffineEtale.app_mem hs (fun j ↦ (hts j).1) j₀
  rw [proAffineEtale_iff_appTop] at hπ
  have : WeaklyEtale (s.app j₀) :=
    (HasRingHomProperty.iff_of_isAffine (P := @WeaklyEtale)).mpr hπ.weaklyEtale
  rw [← (hts j₀).2]
  infer_instance


/- TODO: this previously followed from a (sorried, mathematically unjustified) global
instance `IsStableUnderComposition (pro P)`. The corrected statement
`MorphismProperty.IsStableUnderComposition.pro_of_le_isFinitelyPresentable` additionally
requires `P.IsStableUnderBaseChange` and `P.op ≤ isFinitelyPresentable Schemeᵒᵖ`,
which are not available for `Etale ⊓ ofObjectProperty (IsAffine ·) ⊤`. -/


/-- Name used by chrisflav/proetale#204 for `proAffineEtale_iff_appTop` (from #201). -/
alias proAffineEtale_iff_indEtale_appTop := proAffineEtale_iff_appTop

end AlgebraicGeometry


