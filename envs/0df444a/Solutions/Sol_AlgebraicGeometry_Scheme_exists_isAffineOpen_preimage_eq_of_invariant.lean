-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_isAffineOpen_preimage_eq_of_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/07a390fb-d476-5587-ba60-299a1e6848f6

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_quotient_baseChange_of_finiteLocallyFree_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_affine_quotient_of_finiteLocallyFree_equivalenceRelation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_isAffineOpen_preimage_eq_of_invariant

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.isoOfEq_hom_ι IsOpenImmersion.lift Surjective morphismRestrict_ι Scheme.Opens.range_ι Scheme.Hom IsAffine.of_isIso UniversallyClosed IsFinite IsAffine isPullback_morphismRestrict Scheme IsOpenImmersion Flat IsAffineOpen Scheme.Opens LocallyOfFinitePresentation Scheme.Pullback.exists_preimage_pullback IsOpenImmersion.lift_fac Scheme.Hom.comp_apply Scheme.quotient_baseChange_of_finiteLocallyFree_of_isPullback Scheme.exists_affine_quotient_of_finiteLocallyFree_equivalenceRelation"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "isoOfEq_hom_ι Opens.range_ι Hom Opens Pullback.exists_preimage_pullback isoOfEq restrict Hom.comp_apply quotient_baseChange_of_finiteLocallyFree_of_isPullback exists_affine_quotient_of_finiteLocallyFree_equivalenceRelation"
p2m_open "AlgebraicGeometry.Scheme AlgebraicGeometry"

namespace InvariantAffineImage

variable {X R Y : Scheme.{u}} (s t : R ⟶ X) (p : X ⟶ Y)

theorem mem_of_apply_eq (hR : IsPullback s t p p) (W : X.Opens) (hinv : s ⁻¹ᵁ W = t ⁻¹ᵁ W)
    {x w : X} (hw : w ∈ W) (h : p x = p w) : x ∈ W := by
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback x w h
  set r : R := hR.isoPullback.inv z with hr
  have hs : s r = x := by
    rw [hr, ← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst]; exact hz1
  have ht : t r = w := by
    rw [hr, ← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_snd]; exact hz2
  have hrt : r ∈ t ⁻¹ᵁ W := by show t r ∈ W; rw [ht]; exact hw
  rw [← hinv] at hrt
  have : s r ∈ W := hrt
  rwa [hs] at this

def imageOpen [UniversallyClosed p] (W : X.Opens) : Y.Opens :=
  ⟨(p.base '' ((W : Set X)ᶜ))ᶜ, by
    rw [isOpen_compl_iff]
    exact p.isClosedMap _ (isClosed_compl_iff.mpr W.isOpen)⟩

theorem mem_imageOpen_iff [UniversallyClosed p] (W : X.Opens) (y : Y) :
    y ∈ imageOpen p W ↔ ∀ x : X, p x = y → x ∈ W := by
  change y ∈ (p.base '' _)ᶜ ↔ _
  simp only [Set.mem_compl_iff, Set.mem_image, not_exists, not_and, SetLike.mem_coe]
  constructor
  · intro h x hx
    by_contra hc
    exact h x hc hx
  · intro h x hx hpx
    exact hx (h x hpx)

theorem preimage_imageOpen_eq [UniversallyClosed p] (hR : IsPullback s t p p) (W : X.Opens)
    (hinv : s ⁻¹ᵁ W = t ⁻¹ᵁ W) : p ⁻¹ᵁ imageOpen p W = W := by
  ext x
  change p x ∈ imageOpen p W ↔ x ∈ (W : Set X)
  rw [mem_imageOpen_iff]
  constructor
  · intro h; exact h x rfl
  · intro hx x' hx'
    exact mem_of_apply_eq s t p hR W hinv hx hx'

end InvariantAffineImage

open InvariantAffineImage

theorem equivalenceRelation_restrict {X R : Scheme.{u}} (s t : R ⟶ X) (U : X.Opens) (hinv : s ⁻¹ᵁ U = t ⁻¹ᵁ U)
    (hmono : ∀ {T : Scheme.{u}} (a b : T ⟶ R), a ≫ s = b ≫ s → a ≫ t = b ≫ t → a = b)
    (hequiv : ∀ T : Scheme.{u},
      _root_.Equivalence fun x y : T ⟶ X => ∃ φ : T ⟶ R, φ ≫ s = x ∧ φ ≫ t = y) :
    (∀ {T : Scheme.{u}} (a b : T ⟶ (s ⁻¹ᵁ U).toScheme),
        a ≫ (s ∣_ U) = b ≫ (s ∣_ U) →
        a ≫ ((R.isoOfEq hinv).hom ≫ (t ∣_ U)) = b ≫ ((R.isoOfEq hinv).hom ≫ (t ∣_ U)) → a = b) ∧
    (∀ T : Scheme.{u}, _root_.Equivalence fun x y : T ⟶ U.toScheme =>
        ∃ φ : T ⟶ (s ⁻¹ᵁ U).toScheme, φ ≫ (s ∣_ U) = x ∧ φ ≫ ((R.isoOfEq hinv).hom ≫ (t ∣_ U)) = y) := by

  have hs' : (s ∣_ U) ≫ U.ι = (s ⁻¹ᵁ U).ι ≫ s := morphismRestrict_ι s U
  have ht' : ((R.isoOfEq hinv).hom ≫ (t ∣_ U)) ≫ U.ι = (s ⁻¹ᵁ U).ι ≫ t := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.isoOfEq_hom_ι]

  have key : ∀ {T : Scheme.{u}} (x y : T ⟶ U.toScheme),
      (∃ φ : T ⟶ (s ⁻¹ᵁ U).toScheme, φ ≫ (s ∣_ U) = x ∧ φ ≫ ((R.isoOfEq hinv).hom ≫ (t ∣_ U)) = y) ↔
      (∃ φ : T ⟶ R, φ ≫ s = x ≫ U.ι ∧ φ ≫ t = y ≫ U.ι) := by
    intro T x y
    constructor
    · rintro ⟨φ, h1, h2⟩
      refine ⟨φ ≫ (s ⁻¹ᵁ U).ι, ?_, ?_⟩
      · rw [Category.assoc, ← hs', ← Category.assoc, h1]
      · rw [Category.assoc, ← ht', ← Category.assoc, h2]
    · rintro ⟨φ, h1, h2⟩
      have hrange : Set.range φ.base ⊆ Set.range (s ⁻¹ᵁ U).ι.base := by
        rintro _ ⟨z, rfl⟩
        rw [Scheme.Opens.range_ι]
        show s (φ z) ∈ U
        rw [← Scheme.Hom.comp_apply, h1, Scheme.Hom.comp_apply]
        exact (x z).2
      refine ⟨IsOpenImmersion.lift (s ⁻¹ᵁ U).ι φ hrange, ?_, ?_⟩
      · apply (cancel_mono U.ι).mp
        rw [Category.assoc, hs', ← Category.assoc, IsOpenImmersion.lift_fac, h1]
      · apply (cancel_mono U.ι).mp
        rw [Category.assoc, ht', ← Category.assoc, IsOpenImmersion.lift_fac, h2]
  refine ⟨?_, ?_⟩
  · intro T a b ha hb
    apply (cancel_mono (s ⁻¹ᵁ U).ι).mp
    apply hmono
    · have ha' := congrArg (· ≫ U.ι) ha
      simp only [Category.assoc, hs'] at ha'
      simpa only [Category.assoc] using ha'
    · have hb' := congrArg (· ≫ U.ι) hb
      simp only [Category.assoc] at hb'
      rw [← Category.assoc (R.isoOfEq hinv).hom, ht'] at hb'
      simpa only [Category.assoc] using hb'
  · intro T
    refine ⟨fun x => ?_, fun {x y} hxy => ?_, fun {x y z} hxy hyz => ?_⟩
    · exact (key x x).mpr ((hequiv T).refl (x ≫ U.ι))
    · exact (key y x).mpr ((hequiv T).symm ((key x y).mp hxy))
    · exact (key x z).mpr ((hequiv T).trans ((key x y).mp hxy) ((key y z).mp hyz))

end AlgebraicGeometry.Scheme

p2m_open "AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_exists_isAffineOpen_preimage_eq_of_invariant.AlgebraicGeometry AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_exists_isAffineOpen_preimage_eq_of_invariant.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_exists_isAffineOpen_preimage_eq_of_invariant.AlgebraicGeometry.Scheme.InvariantAffineImage"

theorem solution {X R Y : Scheme.{u}} (s t : R ⟶ X)
    [IsFinite s] [Flat s] [LocallyOfFinitePresentation s]
    [IsFinite t] [Flat t] [LocallyOfFinitePresentation t]
    (hmono : ∀ {T : Scheme.{u}} (a b : T ⟶ R), a ≫ s = b ≫ s → a ≫ t = b ≫ t → a = b)
    (hequiv : ∀ T : Scheme.{u},
      _root_.Equivalence fun x y : T ⟶ X => ∃ φ : T ⟶ R, φ ≫ s = x ∧ φ ≫ t = y)
    (p : X ⟶ Y) (w : s ≫ p = t ≫ p)
    [IsFinite p] [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
    (hR : IsPullback s t p p) (W : X.Opens) (hW : IsAffineOpen W) (hinv : s ⁻¹ᵁ W = t ⁻¹ᵁ W) :
    ∃ V : Y.Opens, IsAffineOpen V ∧ p ⁻¹ᵁ V = W := by
  let V : Y.Opens := imageOpen p W
  have hVW : p ⁻¹ᵁ V = W := preimage_imageOpen_eq s t p hR W hinv
  refine ⟨V, ?_, hVW⟩

  have hinv' : s ⁻¹ᵁ (p ⁻¹ᵁ V) = t ⁻¹ᵁ (p ⁻¹ᵁ V) := by
    change (s ≫ p) ⁻¹ᵁ V = (t ≫ p) ⁻¹ᵁ V
    rw [w]

  let s' : (s ⁻¹ᵁ (p ⁻¹ᵁ V)).toScheme ⟶ (p ⁻¹ᵁ V).toScheme := s ∣_ (p ⁻¹ᵁ V)
  let t' : (s ⁻¹ᵁ (p ⁻¹ᵁ V)).toScheme ⟶ (p ⁻¹ᵁ V).toScheme := (R.isoOfEq hinv').hom ≫ (t ∣_ (p ⁻¹ᵁ V))
  let p' : (p ⁻¹ᵁ V).toScheme ⟶ V.toScheme := p ∣_ V
  have hX : IsPullback (p ⁻¹ᵁ V).ι p' p V.ι := (isPullback_morphismRestrict p V).flip
  have hsq : IsPullback (s ⁻¹ᵁ (p ⁻¹ᵁ V)).ι s' s (p ⁻¹ᵁ V).ι := (isPullback_morphismRestrict s (p ⁻¹ᵁ V)).flip
  have htq : (s ⁻¹ᵁ (p ⁻¹ᵁ V)).ι ≫ t = t' ≫ (p ⁻¹ᵁ V).ι := by
    simp only [t', Category.assoc, morphismRestrict_ι]
    rw [← Category.assoc, Scheme.isoOfEq_hom_ι]
  have hsι : s' ≫ (p ⁻¹ᵁ V).ι = (s ⁻¹ᵁ (p ⁻¹ᵁ V)).ι ≫ s := morphismRestrict_ι s (p ⁻¹ᵁ V)
  have hpι : p' ≫ V.ι = (p ⁻¹ᵁ V).ι ≫ p := morphismRestrict_ι p V
  have w' : s' ≫ p' = t' ≫ p' := by
    apply (cancel_mono V.ι).mp
    rw [Category.assoc, Category.assoc, hpι, ← Category.assoc s', ← Category.assoc t', hsι, ← htq,
      Category.assoc, Category.assoc, w]

  obtain ⟨-, -, -, -, -, ⟨hcolim'⟩⟩ :=
    AlgebraicGeometry.Scheme.quotient_baseChange_of_finiteLocallyFree_of_isPullback hR hX hsq htq w'

  haveI : IsAffine (p ⁻¹ᵁ V).toScheme := by rw [hVW]; exact hW
  haveI : IsFinite s' := MorphismProperty.of_isPullback (P := @IsFinite) hsq ‹IsFinite s›
  haveI : Flat s' := MorphismProperty.of_isPullback (P := @Flat) hsq ‹Flat s›
  haveI : LocallyOfFinitePresentation s' :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hsq ‹LocallyOfFinitePresentation s›
  have htsq : IsPullback (t ⁻¹ᵁ (p ⁻¹ᵁ V)).ι (t ∣_ (p ⁻¹ᵁ V)) t (p ⁻¹ᵁ V).ι :=
    (isPullback_morphismRestrict t (p ⁻¹ᵁ V)).flip
  haveI : IsFinite (t ∣_ (p ⁻¹ᵁ V)) := MorphismProperty.of_isPullback (P := @IsFinite) htsq ‹IsFinite t›
  haveI : Flat (t ∣_ (p ⁻¹ᵁ V)) := MorphismProperty.of_isPullback (P := @Flat) htsq ‹Flat t›
  haveI : LocallyOfFinitePresentation (t ∣_ (p ⁻¹ᵁ V)) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) htsq ‹LocallyOfFinitePresentation t›
  haveI : IsFinite t' := inferInstance
  haveI : Flat t' := inferInstance
  haveI : LocallyOfFinitePresentation t' := inferInstance
  obtain ⟨hmono', hequiv'⟩ := equivalenceRelation_restrict s t (p ⁻¹ᵁ V) hinv' hmono hequiv
  obtain ⟨Y'', hY'', p'', w'', -, -, -, -, -, ⟨hcolim''⟩⟩ :=
    AlgebraicGeometry.Scheme.exists_affine_quotient_of_finiteLocallyFree_equivalenceRelation s' t' hmono' hequiv'

  let e : V.toScheme ≅ Y'' := IsColimit.coconePointUniqueUpToIso hcolim' hcolim''
  haveI : IsAffine Y'' := hY''
  exact IsAffine.of_isIso e.hom

end S_AlgebraicGeometry_Scheme_exists_isAffineOpen_preimage_eq_of_invariant
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_exists_isAffineOpen_preimage_eq_of_invariant (solution)
