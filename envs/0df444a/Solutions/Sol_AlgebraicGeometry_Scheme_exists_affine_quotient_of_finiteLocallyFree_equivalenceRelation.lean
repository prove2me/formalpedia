-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_affine_quotient_of_finiteLocallyFree_equivalenceRelation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/47b66eb7-2bcb-5750-9339-09a0a52057a3

import Mathlib
import Theorems.Thm_RingHom_isPushout_eqLocus_of_finiteLocallyFree_equivalenceRelation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_affine_quotient_of_finiteLocallyFree_equivalenceRelation

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Q1AFF

theorem finite_projective_appTop {X R : Scheme.{u}} [IsAffine X] [IsAffine R] (s : R ⟶ X)
    [IsFinite s] [Flat s] [LocallyOfFinitePresentation s] :
    (letI := s.appTop.hom.toAlgebra; Module.Finite Γ(X, ⊤) Γ(R, ⊤)) ∧
    (letI := s.appTop.hom.toAlgebra; Module.Projective Γ(X, ⊤) Γ(R, ⊤)) := by
  have h₁ : RingHom.Finite s.appTop.hom :=
    ((HasAffineProperty.iff_of_isAffine (P := @IsFinite)).mp inferInstance).2
  have h₂ : RingHom.Flat s.appTop.hom := HasRingHomProperty.appTop (P := @Flat) s inferInstance
  have h₃ : RingHom.FinitePresentation s.appTop.hom :=
    HasRingHomProperty.appTop (P := @LocallyOfFinitePresentation) s inferInstance
  algebraize [s.appTop.hom]
  refine ⟨h₁, ?_⟩
  have : Module.FinitePresentation Γ(X, ⊤) Γ(R, ⊤) :=
    Module.FinitePresentation.of_finite_of_finitePresentation _ _
  exact Module.Flat.projective_of_finitePresentation

theorem range_sup_range_eq_top {X R : Scheme.{u}} [IsAffine X] [IsAffine R] (s t : R ⟶ X)
    [IsFinite s]
    (hmono : ∀ {T : Scheme.{u}} (a b : T ⟶ R), a ≫ s = b ≫ s → a ≫ t = b ≫ t → a = b) :
    s.appTop.hom.range ⊔ t.appTop.hom.range = ⊤ := by
  classical
  set B₀ : Subring Γ(R, ⊤) := s.appTop.hom.range ⊔ t.appTop.hom.range with hB₀

  let s₀ : Γ(X, ⊤) →+* B₀ := s.appTop.hom.codRestrict B₀ (fun a => by
    rw [hB₀]; exact (le_sup_left : s.appTop.hom.range ≤ _) ⟨a, rfl⟩)
  let t₀ : Γ(X, ⊤) →+* B₀ := t.appTop.hom.codRestrict B₀ (fun a => by
    rw [hB₀]; exact (le_sup_right : t.appTop.hom.range ≤ _) ⟨a, rfl⟩)

  let incl : CommRingCat.of B₀ ⟶ Γ(R, ⊤) := CommRingCat.ofHom B₀.subtype
  have hfacs : s.appTop = CommRingCat.ofHom s₀ ≫ incl := by ext; rfl
  have hfact : t.appTop = CommRingCat.ofHom t₀ ≫ incl := by ext; rfl
  have hnat : ∀ f : R ⟶ X, R.isoSpec.inv ≫ f = Spec.map f.appTop ≫ X.isoSpec.inv := fun f => by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact (Scheme.isoSpec_hom_naturality f).symm
  haveI : Epi incl := by
    constructor
    intro T φ ψ h
    have key : Spec.map φ ≫ R.isoSpec.inv = Spec.map ψ ≫ R.isoSpec.inv := by
      apply hmono
      · simp only [Category.assoc, hnat, ← Spec.map_comp_assoc]
        rw [hfacs, Category.assoc, Category.assoc, h]
      · simp only [Category.assoc, hnat, ← Spec.map_comp_assoc]
        rw [hfact, Category.assoc, Category.assoc, h]
    have : Spec.map φ = Spec.map ψ := by
      simpa using congrArg (· ≫ R.isoSpec.hom) key
    exact Spec.map_injective this

  have hfin : RingHom.Finite incl.hom := by
    have h₁ : RingHom.Finite s.appTop.hom :=
      ((HasAffineProperty.iff_of_isAffine (P := @IsFinite)).mp inferInstance).2
    have hfac : incl.hom.comp s₀ = s.appTop.hom := RingHom.ext fun _ => rfl
    rw [← hfac] at h₁
    exact RingHom.Finite.of_comp_finite h₁
  have hsurj : Function.Surjective incl.hom := RingHom.surjective_of_epi_of_finite incl hfin
  rw [eq_top_iff]
  rintro b -
  obtain ⟨⟨b₀, hb₀⟩, rfl⟩ := hsurj b
  exact hb₀

theorem equivalence_ringPoints {X R : Scheme.{u}} [IsAffine X] [IsAffine R] (s t : R ⟶ X)
    (hequiv : ∀ T : Scheme.{u},
      _root_.Equivalence fun x y : T ⟶ X => ∃ φ : T ⟶ R, φ ≫ s = x ∧ φ ≫ t = y)
    (T : Type u) [CommRing T] :
    _root_.Equivalence fun x y : Γ(X, ⊤) →+* T =>
      ∃ φ : Γ(R, ⊤) →+* T, φ.comp s.appTop.hom = x ∧ φ.comp t.appTop.hom = y := by

  let Φ : (Γ(X, ⊤) →+* T) → (Spec (.of T) ⟶ X) := fun x =>
    Spec.map (CommRingCat.ofHom x) ≫ X.isoSpec.inv
  let ΦR : (Γ(R, ⊤) →+* T) → (Spec (.of T) ⟶ R) := fun φ =>
    Spec.map (CommRingCat.ofHom φ) ≫ R.isoSpec.inv
  have hnat : ∀ f : R ⟶ X, R.isoSpec.inv ≫ f = Spec.map f.appTop ≫ X.isoSpec.inv := fun f => by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact (Scheme.isoSpec_hom_naturality f).symm
  have hΦ : ∀ (f : R ⟶ X) (φ : Γ(R, ⊤) →+* T), ΦR φ ≫ f = Φ (φ.comp f.appTop.hom) := fun f φ => by
    simp only [ΦR, Φ, Category.assoc, hnat, ← Spec.map_comp_assoc, CommRingCat.ofHom_comp,
      CommRingCat.ofHom_hom]
  have hsurjR : ∀ ψ : Spec (.of T) ⟶ R, ∃ φ, ΦR φ = ψ := fun ψ => by
    obtain ⟨g, hg⟩ := Spec.map_surjective (ψ ≫ R.isoSpec.hom)
    refine ⟨g.hom, ?_⟩
    simp only [ΦR, CommRingCat.ofHom_hom, hg, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hΦinj : Function.Injective Φ := fun x y hxy => by
    have h1 : Spec.map (CommRingCat.ofHom x) = Spec.map (CommRingCat.ofHom y) := by
      simpa [Φ] using congrArg (· ≫ X.isoSpec.hom) hxy
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  have key : ∀ x y : Γ(X, ⊤) →+* T,
      (∃ φ : Γ(R, ⊤) →+* T, φ.comp s.appTop.hom = x ∧ φ.comp t.appTop.hom = y) ↔
        (∃ ψ : Spec (.of T) ⟶ R, ψ ≫ s = Φ x ∧ ψ ≫ t = Φ y) := fun x y => by
    constructor
    · rintro ⟨φ, rfl, rfl⟩
      exact ⟨ΦR φ, hΦ s φ, hΦ t φ⟩
    · rintro ⟨ψ, h1, h2⟩
      obtain ⟨φ, rfl⟩ := hsurjR ψ
      exact ⟨φ, hΦinj (by rw [← hΦ, h1]), hΦinj (by rw [← hΦ, h2])⟩
  have E := hequiv (Spec (.of T))
  exact
    { refl := fun x => (key x x).2 (E.refl _)
      symm := fun h => (key _ _).2 (E.symm ((key _ _).1 h))
      trans := fun h h' => (key _ _).2 (E.trans ((key _ _).1 h) ((key _ _).1 h')) }

theorem main {X R : Scheme.{u}} [IsAffine X] (s t : R ⟶ X)
    [IsFinite s] [Flat s] [LocallyOfFinitePresentation s]
    [IsFinite t] [Flat t] [LocallyOfFinitePresentation t]
    (hmono : ∀ {T : Scheme.{u}} (a b : T ⟶ R), a ≫ s = b ≫ s → a ≫ t = b ≫ t → a = b)
    (hequiv : ∀ T : Scheme.{u},
      _root_.Equivalence fun x y : T ⟶ X => ∃ φ : T ⟶ R, φ ≫ s = x ∧ φ ≫ t = y) :
    ∃ (Y : Scheme.{u}) (_ : IsAffine Y) (p : X ⟶ Y) (w : s ≫ p = t ≫ p),
      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      IsPullback s t p p ∧ Nonempty (IsColimit (Cofork.ofπ p w)) := by
  haveI : IsAffine R := isAffine_of_isAffineHom s

  set A : Type u := Γ(X, ⊤) with hA
  set B : Type u := Γ(R, ⊤) with hB
  let sr : A →+* B := s.appTop.hom
  let tr : A →+* B := t.appTop.hom
  let C : Subring A := sr.eqLocus tr

  obtain ⟨hs, hs'⟩ := finite_projective_appTop s
  obtain ⟨ht, ht'⟩ := finite_projective_appTop t
  have hgen := range_sup_range_eq_top s t hmono
  have heq := equivalence_ringPoints s t hequiv
  have hinj : Function.Injective (algebraMap C A) := Subtype.val_injective
  have hinv : ∀ a : A, sr a = tr a ↔ a ∈ Set.range (algebraMap C A) := fun a => by
    constructor
    · intro h; exact ⟨⟨a, h⟩, rfl⟩
    · rintro ⟨c, rfl⟩; exact c.2
  obtain ⟨hfin, hproj, hff, hpo⟩ :=
    RingHom.isPushout_eqLocus_of_finiteLocallyFree_equivalenceRelation sr tr hs hs' ht ht' hgen heq
      hinj hinv

  let ι : CommRingCat.of C ⟶ Γ(X, ⊤) := CommRingCat.ofHom (algebraMap C A)
  have hιs : ι ≫ s.appTop = ι ≫ t.appTop := by
    ext c
    exact c.2
  let p : X ⟶ Spec (.of C) := X.isoSpec.hom ≫ Spec.map ι
  have w : s ≫ p = t ≫ p := by
    simp only [p, ← Category.assoc, ← Scheme.isoSpec_hom_naturality]
    simp only [Category.assoc, ← Spec.map_comp, hιs]

  have hι_fin : RingHom.Finite ι.hom := RingHom.finite_algebraMap.mpr hfin
  have hι_ff : ι.hom.FaithfullyFlat := RingHom.faithfullyFlat_algebraMap_iff.mpr hff
  haveI : Module.FinitePresentation C A := Module.finitePresentation_of_projective C A
  have hι_fp : RingHom.FinitePresentation ι.hom :=
    RingHom.finitePresentation_algebraMap.mpr inferInstance
  haveI : IsFinite (Spec.map ι) := (IsFinite.SpecMap_iff ι).mpr hι_fin
  haveI : Flat (Spec.map ι) := ((flat_and_surjective_SpecMap_iff ι).mpr hι_ff).1
  haveI : Surjective (Spec.map ι) := ((flat_and_surjective_SpecMap_iff ι).mpr hι_ff).2
  haveI : LocallyOfFinitePresentation (Spec.map ι) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mpr hι_fp
  haveI : IsFinite p := inferInstance
  haveI : Flat p := inferInstance
  haveI : Surjective p := inferInstance
  haveI : LocallyOfFinitePresentation p := inferInstance

  have hpb : IsPullback (Spec.map s.appTop) (Spec.map t.appTop) (Spec.map ι) (Spec.map ι) :=
    isPullback_SpecMap_of_isPushout ι ι s.appTop t.appTop hpo
  have hker : IsPullback s t p p := by
    refine hpb.of_iso R.isoSpec.symm X.isoSpec.symm X.isoSpec.symm (Iso.refl _) ?_ ?_ ?_ ?_
    · simpa [Iso.symm_hom] using (Scheme.isoSpec_inv_naturality s)
    · simpa [Iso.symm_hom] using (Scheme.isoSpec_inv_naturality t)
    · simp [p]
    · simp [p]
  have hk : IsKernelPair p s t := hker
  exact ⟨Spec (.of C), inferInstance, p, w, inferInstance, inferInstance, inferInstance,
    inferInstance, hker, ⟨hk.toCoequalizer (regularEpiOfEffectiveEpi p)⟩⟩

end Q1AFF

theorem solution
    {X R : Scheme.{u}} [IsAffine X] (s t : R ⟶ X)
    [IsFinite s] [Flat s] [LocallyOfFinitePresentation s]
    [IsFinite t] [Flat t] [LocallyOfFinitePresentation t]
    (hmono : ∀ {T : Scheme.{u}} (a b : T ⟶ R), a ≫ s = b ≫ s → a ≫ t = b ≫ t → a = b)
    (hequiv : ∀ T : Scheme.{u},
      _root_.Equivalence fun x y : T ⟶ X => ∃ φ : T ⟶ R, φ ≫ s = x ∧ φ ≫ t = y) :
    ∃ (Y : Scheme.{u}) (_ : IsAffine Y) (p : X ⟶ Y) (w : s ≫ p = t ≫ p),
      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      IsPullback s t p p ∧ Nonempty (IsColimit (Cofork.ofπ p w)) :=
  Q1AFF.main s t hmono hequiv

end S_AlgebraicGeometry_Scheme_exists_affine_quotient_of_finiteLocallyFree_equivalenceRelation
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_exists_affine_quotient_of_finiteLocallyFree_equivalenceRelation (solution)
