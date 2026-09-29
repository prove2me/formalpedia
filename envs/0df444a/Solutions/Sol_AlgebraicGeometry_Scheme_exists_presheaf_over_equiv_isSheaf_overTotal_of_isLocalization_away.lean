-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_presheaf_over_equiv_isSheaf_overTotal_of_isLocalization_away
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/2361192b-2b67-562a-a09e-255811ad98af

import Mathlib
import Definitions.Def_CategoryTheory_OverTotalPresheaf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_presheaf_over_equiv_isSheaf_overTotal_of_isLocalization_away

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry Opposite CategoryTheory.Limits"

namespace GrassBridgeH1

structure Datum (R : Type) [CommRing R] where
  F : ∀ (A : Type) [CommRing A] [Algebra R A], Type
  Fmap : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B],
    (A →ₐ[R] B) → F A → F B
  Fmap_id : ∀ (A : Type) [CommRing A] [Algebra R A] (s : F A), Fmap A A (AlgHom.id R A) s = s
  Fmap_comp : ∀ (A B C : Type) [CommRing A] [CommRing B] [CommRing C] [Algebra R A] [Algebra R B]
    [Algebra R C] (φ : A →ₐ[R] B) (ψ : B →ₐ[R] C) (s : F A),
    Fmap A C (ψ.comp φ) s = Fmap B C ψ (Fmap A B φ s)

namespace Datum

variable {R : Type} [CommRing R] (D : Datum R)

def IsSheaf : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra R A] (n : ℕ) (f : Fin n → A),
    Ideal.span (Set.range f) = ⊤ →
    ∀ (B : Fin n → Type) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)] [∀ i, Algebra R (B i)]
      [∀ i, IsScalarTower R A (B i)] [∀ i, IsLocalization.Away (f i) (B i)] (s : ∀ i, D.F (B i)),
    (∀ (i j : Fin n) (C : Type) [CommRing C] [Algebra A C] [Algebra R C] [IsScalarTower R A C]
        [IsLocalization.Away (f i * f j) C] (ρ₁ : B i →ₐ[A] C) (ρ₂ : B j →ₐ[A] C),
        D.Fmap _ _ (ρ₁.restrictScalars R) (s i) = D.Fmap _ _ (ρ₂.restrictScalars R) (s j)) →
    ∃! s₀ : D.F A, ∀ i, D.Fmap _ _ (IsScalarTower.toAlgHom R A (B i)) s₀ = s i

abbrev F' (A : Type) [CommRing A] (i : Algebra R A) : Type := @Datum.F R _ D A _ i

abbrev am {A : Type} [CommRing A] (i : Algebra R A) (r : R) : A := @algebraMap R A _ _ i r

def mkₐ {A B : Type} [CommRing A] [CommRing B] (iA : Algebra R A) (iB : Algebra R B) (g : A →+* B)
    (hg : ∀ r, g (am iA r) = am iB r) : @AlgHom R A B _ _ _ iA iB :=
  @AlgHom.mk R A B _ _ _ iA iB g hg

@[scoped simp] lemma mkₐ_apply {A B : Type} [CommRing A] [CommRing B] (iA : Algebra R A) (iB : Algebra R B)
    (g : A →+* B) (hg : ∀ r, g (am iA r) = am iB r) (a : A) : mkₐ iA iB g hg a = g a := rfl

def T {A B : Type} [CommRing A] [CommRing B] (iA : Algebra R A) (iB : Algebra R B) (g : A →+* B)
    (hg : ∀ r, g (am iA r) = am iB r) : D.F' A iA → D.F' B iB :=
  @Datum.Fmap R _ D A B _ _ iA iB (mkₐ iA iB g hg)

lemma Fmap_eq_T {A B : Type} [CommRing A] [CommRing B] {iA : Algebra R A} {iB : Algebra R B}
    (f : @AlgHom R A B _ _ _ iA iB) (x : D.F' A iA) :
    @Datum.Fmap R _ D A B _ _ iA iB f x = D.T iA iB f.toRingHom (@AlgHom.commutes R A B _ _ _ iA iB f) x :=
  rfl

lemma T_id {A : Type} [CommRing A] (iA : Algebra R A) (hg : ∀ r, RingHom.id A (am iA r) = am iA r)
    (x : D.F' A iA) : D.T iA iA (RingHom.id A) hg x = x :=
  @Datum.Fmap_id R _ D A _ iA x

lemma T_T {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (iA : Algebra R A) (iB : Algebra R B)
    (iC : Algebra R C) (g : A →+* B) (hg : ∀ r, g (am iA r) = am iB r) (g' : B →+* C)
    (hg' : ∀ r, g' (am iB r) = am iC r) (x : D.F' A iA) :
    D.T iB iC g' hg' (D.T iA iB g hg x) =
      D.T iA iC (g'.comp g) (fun r => by rw [RingHom.comp_apply, hg, hg']) x :=
  (@Datum.Fmap_comp R _ D A B C _ _ _ iA iB iC (mkₐ iA iB g hg) (mkₐ iB iC g' hg') x).symm

lemma T_congr {A B : Type} [CommRing A] [CommRing B] (iA : Algebra R A) (iB : Algebra R B)
    {g g' : A →+* B} (h : g = g') (hg : ∀ r, g (am iA r) = am iB r)
    (hg' : ∀ r, g' (am iA r) = am iB r) (x : D.F' A iA) : D.T iA iB g hg x = D.T iA iB g' hg' x := by
  subst h; rfl

lemma T_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {iA : Algebra R A}
    {iB : Algebra R B} {iC : Algebra R C} {g : A →+* B} {hg : ∀ r, g (am iA r) = am iB r} {g' : B →+* C}
    {hg' : ∀ r, g' (am iB r) = am iC r} {g'' : A →+* C} (h : g'.comp g = g'') (x : D.F' A iA) :
    D.T iB iC g' hg' (D.T iA iB g hg x) =
      D.T iA iC g'' (fun r => by subst h; rw [RingHom.comp_apply, hg, hg']) x := by
  rw [T_T]; exact D.T_congr _ _ h _ _ x

lemma T_eq_self {A : Type} [CommRing A] {iA : Algebra R A} {g : A →+* A} (h : g = RingHom.id A)
    (hg : ∀ r, g (am iA r) = am iA r) (x : D.F' A iA) : D.T iA iA g hg x = x := by
  subst h; exact D.T_id iA hg x

@[scoped ext (flat := false)]
structure Tot (A : CommRingCat.{0}) : Type where
  φ : CommRingCat.of R ⟶ A
  val : D.F' A φ.hom.toAlgebra

namespace Tot

variable {D}

def out {A : CommRingCat.{0}} (t : D.Tot A) (i : Algebra R A) (h : ∀ r, t.φ.hom r = am i r) : D.F' A i :=
  D.T t.φ.hom.toAlgebra i (RingHom.id A) (fun r => h r) t.val

lemma out_self {A : CommRingCat.{0}} (t : D.Tot A) (h : ∀ r, t.φ.hom r = am t.φ.hom.toAlgebra r) :
    t.out _ h = t.val :=
  D.T_id _ _ _

lemma out_congr {A : CommRingCat.{0}} {t t' : D.Tot A} (e : t = t') (i : Algebra R A)
    (h : ∀ r, t.φ.hom r = am i r) (h' : ∀ r, t'.φ.hom r = am i r) : t.out i h = t'.out i h' := by
  subst e; rfl

lemma ext_of_out {A : CommRingCat.{0}} {t t' : D.Tot A} (h : t.φ = t'.φ)
    (hv : t.out t'.φ.hom.toAlgebra (fun r => by rw [h]; rfl) = t'.val) : t = t' := by
  obtain ⟨φ, v⟩ := t
  obtain ⟨φ', v'⟩ := t'
  cases h
  rw [out_self] at hv
  cases hv
  rfl

end Tot

def P₀ : (CommRingCat.{0}ᵒᵖ)ᵒᵖ ⥤ Type where
  obj X := D.Tot X.unop.unop
  map {X Y} g := ↾fun t => ⟨t.φ ≫ g.unop.unop, D.T _ _ g.unop.unop.hom (fun _ => rfl) t.val⟩
  map_id X := by
    refine ConcreteCategory.hom_ext _ _ fun t => ?_
    simp only [TypeCat.ofHom_apply, types_id_apply]
    refine Tot.ext_of_out (Category.comp_id _) ?_
    simp only [Tot.out]
    exact (D.T_comp_eq rfl _).trans (D.T_eq_self (by ext; simp) _ _)
  map_comp {X Y Z} g g' := by
    refine ConcreteCategory.hom_ext _ _ fun t => ?_
    simp only [TypeCat.ofHom_apply, types_comp_apply]
    symm
    refine Tot.ext_of_out (Category.assoc _ _ _) ?_
    simp only [Tot.out]
    rw [D.T_comp_eq rfl, D.T_comp_eq rfl]
    rfl

@[scoped simp] lemma P₀_map_φ {X Y : (CommRingCat.{0}ᵒᵖ)ᵒᵖ} (g : X ⟶ Y) (t : D.P₀.obj X) :
    (D.P₀.map g t).φ = t.φ ≫ g.unop.unop := rfl

lemma P₀_map_val {X Y : (CommRingCat.{0}ᵒᵖ)ᵒᵖ} (g : X ⟶ Y) (t : D.P₀.obj X) :
    (D.P₀.map g t).val = D.T _ _ g.unop.unop.hom (fun _ => rfl) t.val := rfl

lemma out_P₀_map {X Y : (CommRingCat.{0}ᵒᵖ)ᵒᵖ} (g : X ⟶ Y) (t : D.P₀.obj X)
    (i : Algebra R Y.unop.unop) (h : ∀ r, (t.φ ≫ g.unop.unop).hom r = am i r) :
    (D.P₀.map g t).out i h = D.T _ i g.unop.unop.hom h t.val := by
  simp only [Tot.out, P₀_map_val]
  exact D.T_comp_eq (RingHom.id_comp _) _

end Datum
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_exists_presheaf_over_equiv_isSheaf_overTotal_of_isLocalization_away.GrassBridgeH1.Datum"

scoped instance isCoverDense_Spec : Scheme.Spec.IsCoverDense Scheme.zariskiTopology.{0} where
  is_cover X := by
    rw [Scheme.mem_grothendieckTopology_iff]
    refine ⟨X.affineCover, ?_⟩
    rintro Y f ⟨i⟩
    exact ⟨{obj := op _, lift := 𝟙 _, map := X.affineCover.f i, fac := Category.id_comp _}⟩

noncomputable abbrev J₀ : GrothendieckTopology CommRingCat.{0}ᵒᵖ :=
  Scheme.Spec.inducedTopology Scheme.zariskiTopology.{0}

scoped instance isOneHypercoverDense_Spec :
    Functor.IsOneHypercoverDense.{0} Scheme.Spec J₀ Scheme.zariskiTopology.{0} :=
  Functor.IsOneHypercoverDense.of_hasPullbacks fun X =>
    ⟨X.affineCover.I₀, fun i => op (X.local_affine i).choose_spec.choose, X.affineCover.f,
      X.affineCover.mem_grothendieckTopology⟩

lemma isSheaf_J₀_yoneda (S : Scheme.{0}) :
    Presheaf.IsSheaf J₀ (Scheme.Spec.op ⋙ yoneda.obj S) :=
  Scheme.Spec.op_comp_isSheaf J₀ Scheme.zariskiTopology (Scheme.zariskiTopology.yoneda.obj S)

noncomputable def stdObj (A : CommRingCat.{0}) {n : ℕ} (f : Fin n → A) (i : Fin n) : CommRingCat.{0}ᵒᵖ :=
  op (CommRingCat.of (Localization.Away (f i)))

noncomputable def stdHom (A : CommRingCat.{0}) {n : ℕ} (f : Fin n → A) (i : Fin n) : stdObj A f i ⟶ op A :=
  (CommRingCat.ofHom (algebraMap A (Localization.Away (f i)))).op

lemma range_Spec_map_algebraMap_away (A : CommRingCat.{0}) (r : A) :
    Set.range (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away r)))) =
      (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum A)) :=
  PrimeSpectrum.localization_away_comap_range (Localization.Away r) r

lemma generate_std_mem (A : CommRingCat.{0}) {n : ℕ} (f : Fin n → A)
    (hf : Ideal.span (Set.range f) = ⊤) :
    Sieve.ofArrows (stdObj A f) (stdHom A f) ∈ J₀ (op A) := by
  rw [Functor.mem_inducedTopology_iff_of_isCoverDense, Scheme.mem_grothendieckTopology_iff]
  refine ⟨(Scheme.affineOpenCoverOfSpanRangeEqTop f hf).openCover, ?_⟩
  rintro _ _ ⟨i⟩
  exact ⟨stdObj A f i, stdHom A f i, 𝟙 _, Sieve.ofArrows_mk _ _ i, (Category.id_comp _).symm⟩

lemma mem_of_functorPushforward_Spec_map {A : CommRingCat.{0}} (S : Sieve (op A)) {B : CommRingCat.{0}}
    (g : A ⟶ B) (h : S.functorPushforward Scheme.Spec (Spec.map g)) : S g.op := by
  have e := (Sieve.fullyFaithfulFunctorGaloisCoinsertion Scheme.Spec (op A)).u_l_eq S
  rw [← e]
  exact h

lemma exists_std_of_mem {A : CommRingCat.{0}} {S : Sieve (op A)} (hS : S ∈ J₀ (op A)) :
    ∃ (n : ℕ) (f : Fin n → A), Ideal.span (Set.range f) = ⊤ ∧ ∀ i, S (stdHom A f i) := by
  rw [Functor.mem_inducedTopology_iff_of_isCoverDense, Scheme.mem_grothendieckTopology_iff] at hS
  obtain ⟨𝒰, h𝒰⟩ := hS
  have key : ∀ p : PrimeSpectrum A, ∃ r : A, p ∈ PrimeSpectrum.basicOpen r ∧
      S ((CommRingCat.ofHom (algebraMap A (Localization.Away r))).op) := by
    intro p
    obtain ⟨y, hy⟩ := 𝒰.covers p
    obtain ⟨_, ⟨r, rfl⟩, hpr, hrU⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
        (Set.mem_range.mpr ⟨y, hy⟩) (𝒰.f (𝒰.idx p)).opensRange.2
    refine ⟨r, hpr, ?_⟩
    have hrange : Set.range (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away r)))) ⊆
        Set.range (𝒰.f (𝒰.idx p)) := by
      rw [range_Spec_map_algebraMap_away]; exact hrU
    apply mem_of_functorPushforward_Spec_map
    rw [← IsOpenImmersion.lift_fac _ _ hrange]
    exact Sieve.downward_closed _ (h𝒰 _ _ (Presieve.ofArrows.mk (𝒰.idx p))) _
  choose r hr hrS using key
  have hspan : Ideal.span (Set.range r) = ⊤ := by
    rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff]
    exact top_le_iff.mp fun p _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨p, hr p⟩
  obtain ⟨T, hT, h1⟩ :=
    Submodule.mem_span_finite_of_mem_span ((Ideal.eq_top_iff_one _).mp hspan)
  have hall : ∀ a ∈ Set.range r, S ((CommRingCat.ofHom (algebraMap A (Localization.Away a))).op) := by
    rintro _ ⟨p, rfl⟩; exact hrS p
  refine ⟨T.card, fun i => (T.equivFin.symm i : A), ?_, fun i => hall _ (hT (T.equivFin.symm i).2)⟩
  rw [Ideal.eq_top_iff_one]
  refine Ideal.span_mono ?_ h1
  intro a ha
  exact ⟨T.equivFin ⟨a, ha⟩, by simp⟩

lemma isSeparatedFor_of_le {C : Type*} [Category C] {P : Cᵒᵖ ⥤ Type*} {X : C} {R₁ R₂ : Presieve X}
    (h : R₁ ≤ R₂) (h₁ : Presieve.IsSeparatedFor P R₁) : Presieve.IsSeparatedFor P R₂ :=
  fun x t₁ t₂ ht₁ ht₂ => h₁ (x.restrict h) t₁ t₂ (Presieve.isAmalgamation_restrict h x t₁ ht₁)
    (Presieve.isAmalgamation_restrict h x t₂ ht₂)

namespace Datum

variable {R : Type} [CommRing R] (D : Datum R)

theorem isSheafFor_std (hD : D.IsSheaf) (A : CommRingCat.{0}) {n : ℕ} (f : Fin n → A)
    (hf : Ideal.span (Set.range f) = ⊤) :
    Presieve.IsSheafFor D.P₀ (Presieve.ofArrows (stdObj A f) (stdHom A f)) := by
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  change ∀ i, D.Tot (CommRingCat.of (Localization.Away (f i))) at x

  have hY : Presieve.IsSheafFor (Scheme.Spec.op ⋙ yoneda.obj (Spec (.of R)))
      (Presieve.ofArrows (stdObj A f) (stdHom A f)) := by
    rw [Presieve.isSheafFor_iff_generate]
    exact (isSheaf_iff_isSheaf_of_type _ _).1 (isSheaf_J₀_yoneda (Spec (.of R))) _
      (generate_std_mem A f hf)
  rw [Presieve.isSheafFor_arrows_iff] at hY
  have hφx : ∀ (i j : Fin n) (Z : CommRingCat.{0}ᵒᵖ) (gi : Z ⟶ stdObj A f i) (gj : Z ⟶ stdObj A f j),
      gi ≫ stdHom A f i = gj ≫ stdHom A f j → (x i).φ ≫ gi.unop = (x j).φ ≫ gj.unop := by
    intro i j Z gi gj hg
    exact congrArg Tot.φ (hx i j Z gi gj hg)
  obtain ⟨t, ht, ht'⟩ := hY (fun i => Spec.map (x i).φ) (by
    intro i j Z gi gj hg
    change Spec.map gi.unop ≫ Spec.map (x i).φ = Spec.map gj.unop ≫ Spec.map (x j).φ
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (hφx i j Z gi gj hg))
  replace ht : ∀ i, Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (f i)))) ≫ t =
      Spec.map (x i).φ := ht
  replace ht' : ∀ t₁ : Spec A ⟶ Spec (.of R), (∀ i, Spec.map (CommRingCat.ofHom
      (algebraMap A (Localization.Away (f i)))) ≫ t₁ = Spec.map (x i).φ) → t₁ = t := ht'
  set φ : CommRingCat.of R ⟶ A := Spec.preimage t with hφdef
  have hφ : ∀ i, φ ≫ CommRingCat.ofHom (algebraMap A (Localization.Away (f i))) = (x i).φ := by
    intro i
    apply Spec.map_injective
    rw [Spec.map_comp, hφdef, Spec.map_preimage]
    exact ht i
  have hφr : ∀ i (r : R), algebraMap A (Localization.Away (f i)) (φ.hom r) = (x i).φ.hom r :=
    fun i r => congrArg (fun k : CommRingCat.of R ⟶ _ => k.hom r) (hφ i)

  letI iA : Algebra R A := φ.hom.toAlgebra
  have hRi : ∀ i (r : R), (x i).φ.hom r = algebraMap R (Localization.Away (f i)) r := fun i r => by
    rw [IsScalarTower.algebraMap_apply R A (Localization.Away (f i)) r]
    exact (hφr i r).symm

  obtain ⟨s₀, hs₀, hs₀'⟩ := hD A n f hf (fun i => Localization.Away (f i))
      (fun i => (x i).out _ (hRi i)) (by
    intro i j C _ _ instRC _ _ ρ₁ ρ₂
    have hcomm : (CommRingCat.ofHom ρ₁.toRingHom).op ≫ stdHom A f i =
        (CommRingCat.ofHom ρ₂.toRingHom).op ≫ stdHom A f j := by
      apply Quiver.Hom.unop_inj
      ext a
      change ρ₁ (algebraMap A _ a) = ρ₂ (algebraMap A _ a)
      simp
    have h := hx i j (op (CommRingCat.of C)) _ _ hcomm
    have hρ₁ : ∀ r, ((x i).φ ≫ CommRingCat.ofHom ρ₁.toRingHom).hom r = am instRC r := fun r => by
      change ρ₁ ((x i).φ.hom r) = _
      rw [hRi]; exact (ρ₁.restrictScalars R).commutes r
    have hρ₂ : ∀ r, ((x j).φ ≫ CommRingCat.ofHom ρ₂.toRingHom).hom r = am instRC r := fun r => by
      change ρ₂ ((x j).φ.hom r) = _
      rw [hRi]; exact (ρ₂.restrictScalars R).commutes r
    have h' := Tot.out_congr h instRC hρ₁ hρ₂
    erw [out_P₀_map, out_P₀_map] at h'
    exact (D.T_comp_eq (RingHom.comp_id ρ₁.toRingHom) (x i).val).trans
      (h'.trans (D.T_comp_eq (RingHom.comp_id ρ₂.toRingHom) (x j).val).symm))

  have hs₀T : ∀ i, D.T iA (x i).φ.hom.toAlgebra (algebraMap A (Localization.Away (f i))) (hφr i) s₀ =
      (x i).val := by
    intro i
    have h := congrArg (D.T _ (x i).φ.hom.toAlgebra (RingHom.id _) (fun r => (hRi i r).symm)) (hs₀ i)
    exact ((D.T_comp_eq (RingHom.id_comp (algebraMap A (Localization.Away (f i)))) s₀).symm.trans
      h).trans ((D.T_comp_eq (RingHom.id_comp (RingHom.id (Localization.Away (f i))))
        (x i).val).trans (D.T_eq_self rfl _ _))

  refine ⟨⟨φ, s₀⟩, fun i => ?_, fun t₁ ht₁ => ?_⟩
  · refine Tot.ext_of_out (hφ i) ?_
    erw [out_P₀_map]
    exact hs₀T i
  · have h₁ : t₁.φ = φ := by
      apply Spec.map_injective
      rw [hφdef, Spec.map_preimage]
      refine ht' _ fun i => ?_
      rw [← Spec.map_comp]
      exact congrArg (fun k => Spec.map (Tot.φ k)) (ht₁ i)
    refine Tot.ext_of_out h₁ ?_
    refine hs₀' _ fun i => ?_
    have hg₁ : ∀ r, (t₁.φ ≫ CommRingCat.ofHom (algebraMap A (Localization.Away (f i)))).hom r =
        algebraMap R (Localization.Away (f i)) r := fun r => by
      change algebraMap A _ (t₁.φ.hom r) = _
      rw [h₁]; exact (hφr i r).trans (hRi i r)
    have h₂ := Tot.out_congr (ht₁ i) _ hg₁ (hRi i)
    erw [out_P₀_map] at h₂
    exact (D.T_comp_eq (RingHom.comp_id (algebraMap A (Localization.Away (f i)))) _).trans h₂

theorem isSheaf_P₀ (hD : D.IsSheaf) : Presheaf.IsSheaf J₀ D.P₀ := by
  rw [isSheaf_iff_isSheaf_of_type]
  intro X S hS
  obtain ⟨A⟩ := X
  obtain ⟨n, f, hf, hfS⟩ := exists_std_of_mem hS
  refine Presieve.isSheafFor_subsieve_aux D.P₀ (S := Sieve.ofArrows (stdObj A f) (stdHom A f))
    ?_ ?_ ?_
  · rintro _ _ ⟨Y', h, g, ⟨i⟩, rfl⟩
    exact S.downward_closed (hfS i) h
  · rw [← Presieve.isSheafFor_iff_generate]
    exact D.isSheafFor_std hD A f hf
  · intro Y g _
    obtain ⟨B⟩ := Y
    set f' : Fin n → B := fun i => g.unop.hom (f i)
    have hf' : Ideal.span (Set.range f') = ⊤ := by
      have e : f' = g.unop.hom ∘ f := rfl
      rw [e, Set.range_comp, ← Ideal.map_span, hf, Ideal.map_top]
    have hle : Presieve.ofArrows (stdObj B f') (stdHom B f') ≤
        (Sieve.pullback g (Sieve.ofArrows (stdObj A f) (stdHom A f))).arrows := by
      rintro _ _ ⟨i⟩
      refine ⟨stdObj A f i, (CommRingCat.ofHom (Localization.awayMap g.unop.hom (f i))).op,
        stdHom A f i, Presieve.ofArrows.mk i, ?_⟩
      apply Quiver.Hom.unop_inj
      ext a
      change Localization.awayMap g.unop.hom (f i) (algebraMap A _ a) = algebraMap B _ (g.unop.hom a)
      exact IsLocalization.map_eq _ _
    exact isSeparatedFor_of_le hle (D.isSheafFor_std hD B f' hf').isSeparatedFor

end Datum
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_exists_presheaf_over_equiv_isSheaf_overTotal_of_isLocalization_away.GrassBridgeH1.Datum"

noncomputable abbrev affRing (T : Scheme.{0}) (i : T.affineCover.I₀) : CommRingCat.{0} :=
  (T.local_affine i).choose_spec.choose

noncomputable abbrev acov (T : Scheme.{0}) : T.OpenCover where
  I₀ := T.affineCover.I₀
  X i := Spec (affRing T i)
  f i := T.affineCover.f i
  mem₀ := T.affineCover.mem₀

namespace Datum

variable {R : Type} [CommRing R] (D : Datum R) (hD : D.IsSheaf)

noncomputable def G₀ : Sheaf J₀ (Type 0) := ⟨D.P₀, D.isSheaf_P₀ hD⟩

noncomputable def H : Scheme.{0}ᵒᵖ ⥤ Type :=
  Functor.OneHypercoverDenseData.essSurj.presheaf
    (Functor.oneHypercoverDenseData Scheme.Spec J₀ Scheme.zariskiTopology) (D.G₀ hD)

lemma H_isSheaf : Presheaf.IsSheaf Scheme.zariskiTopology (D.H hD) :=
  Functor.OneHypercoverDenseData.essSurj.isSheaf _ _

noncomputable def Hiso : Scheme.Spec.op ⋙ D.H hD ≅ D.P₀ :=
  Functor.OneHypercoverDenseData.essSurj.compPresheafIso _ _

noncomputable def toH {A : CommRingCat.{0}} (t : D.Tot A) : (D.H hD).obj (op (Spec A)) :=
  (D.Hiso hD).inv.app (op (op A)) t

noncomputable def ofH {A : CommRingCat.{0}} (y : (D.H hD).obj (op (Spec A))) : D.Tot A :=
  (D.Hiso hD).hom.app (op (op A)) y

lemma ofH_toH {A : CommRingCat.{0}} (t : D.Tot A) : D.ofH hD (D.toH hD t) = t := by
  have h := ConcreteCategory.congr_hom ((D.Hiso hD).inv_hom_id_app (op (op A))) t
  exact h

lemma toH_ofH {A : CommRingCat.{0}} (y : (D.H hD).obj (op (Spec A))) : D.toH hD (D.ofH hD y) = y := by
  have h := ConcreteCategory.congr_hom ((D.Hiso hD).hom_inv_id_app (op (op A))) y
  exact h

lemma ofH_map {A B : CommRingCat.{0}} (g : A ⟶ B) (y : (D.H hD).obj (op (Spec A))) :
    D.ofH hD ((D.H hD).map (Spec.map g).op y) = D.P₀.map g.op.op (D.ofH hD y) :=
  NatTrans.naturality_apply (D.Hiso hD).hom (g.op.op : op (op A) ⟶ op (op B)) y

lemma map_toH {A B : CommRingCat.{0}} (g : A ⟶ B) (t : D.Tot A) :
    (D.H hD).map (Spec.map g).op (D.toH hD t) = D.toH hD (D.P₀.map g.op.op t) :=
  (NatTrans.naturality_apply (D.Hiso hD).inv (g.op.op : op (op A) ⟶ op (op B)) t).symm

noncomputable def aff {T : Scheme.{0}} (y : (D.H hD).obj (op T)) {A : CommRingCat.{0}} (u : Spec A ⟶ T) :
    D.Tot A :=
  D.ofH hD ((D.H hD).map u.op y)

lemma aff_map {T T' : Scheme.{0}} (y : (D.H hD).obj (op T)) (k : T' ⟶ T) {A : CommRingCat.{0}}
    (u : Spec A ⟶ T') : D.aff hD ((D.H hD).map k.op y) u = D.aff hD y (u ≫ k) := by
  simp only [aff, ← Functor.map_comp_apply, ← op_comp]

lemma aff_id {A : CommRingCat.{0}} (y : (D.H hD).obj (op (Spec A))) :
    D.aff hD y (𝟙 _) = D.ofH hD y := by
  simp only [aff, op_id, Functor.map_id_apply]

lemma aff_Spec_map {T : Scheme.{0}} (y : (D.H hD).obj (op T)) {A B : CommRingCat.{0}} (g : A ⟶ B)
    (u : Spec A ⟶ T) : D.aff hD y (Spec.map g ≫ u) = D.P₀.map g.op.op (D.aff hD y u) := by
  simp only [aff, op_comp, Functor.map_comp_apply]
  exact D.ofH_map hD g _

lemma Spec_map_aff_φ_comp {T : Scheme.{0}} (y : (D.H hD).obj (op T)) {A B : CommRingCat.{0}}
    (v : Spec B ⟶ Spec A) (u : Spec A ⟶ T) :
    Spec.map (D.aff hD y (v ≫ u)).φ = v ≫ Spec.map (D.aff hD y u).φ := by
  obtain ⟨g, rfl⟩ := Spec.map_surjective v
  rw [aff_Spec_map, P₀_map_φ, Spec.map_comp]
  rfl

noncomputable def base {T : Scheme.{0}} (y : (D.H hD).obj (op T)) : T ⟶ Spec (.of R) :=
  (acov T).glueMorphisms (fun i => Spec.map (D.aff hD y ((acov T).f i)).φ) (by
    intro i j
    apply (acov (pullback ((acov T).f i) ((acov T).f j))).hom_ext
    intro k
    dsimp only
    rw [← Category.assoc, ← Category.assoc, ← Spec_map_aff_φ_comp, ← Spec_map_aff_φ_comp,
      Category.assoc, Category.assoc, pullback.condition])

lemma ι_base {T : Scheme.{0}} (y : (D.H hD).obj (op T)) (i : (acov T).I₀) :
    (acov T).f i ≫ D.base hD y = Spec.map (D.aff hD y ((acov T).f i)).φ :=
  (acov T).ι_glueMorphisms _ _ i

lemma base_spec {T : Scheme.{0}} (y : (D.H hD).obj (op T)) {A : CommRingCat.{0}} (u : Spec A ⟶ T) :
    Spec.map (D.aff hD y u).φ = u ≫ D.base hD y := by
  apply ((acov T).pullback₁ u).hom_ext
  intro i
  apply (acov (pullback u ((acov T).f i))).hom_ext
  intro k
  change (acov _).f k ≫ pullback.fst u ((acov T).f i) ≫ Spec.map _ =
    (acov _).f k ≫ pullback.fst u ((acov T).f i) ≫ u ≫ D.base hD y
  rw [← Category.assoc, ← Spec_map_aff_φ_comp, Category.assoc, pullback.condition, ← Category.assoc,
    Spec_map_aff_φ_comp, pullback.condition_assoc, ι_base, Category.assoc]

lemma base_unique {T : Scheme.{0}} (y : (D.H hD).obj (op T)) (t : T ⟶ Spec (.of R))
    (ht : ∀ (A : CommRingCat.{0}) (u : Spec A ⟶ T), Spec.map (D.aff hD y u).φ = u ≫ t) :
    t = D.base hD y := by
  apply (acov T).hom_ext
  intro i
  rw [← ht, base_spec]

noncomputable def G : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ Type where
  obj X := { y : (D.H hD).obj (op X.unop.left) //
    ∀ (A : CommRingCat.{0}) (u : Spec A ⟶ X.unop.left), Spec.map (D.aff hD y u).φ = u ≫ X.unop.hom }
  map {X Y} k := ↾fun y => ⟨(D.H hD).map k.unop.left.op y.1, fun A u => by
    rw [aff_map, y.2, Category.assoc, Over.w k.unop]⟩
  map_id X := by
    refine ConcreteCategory.hom_ext _ _ fun y => Subtype.ext ?_
    simp
  map_comp {X Y Z} k k' := by
    refine ConcreteCategory.hom_ext _ _ fun y => Subtype.ext ?_
    simp

noncomputable def totEquiv (T : Scheme.{0}) : (D.G hD).OverTotal T ≃ (D.H hD).obj (op T) where
  toFun a := a.2.1
  invFun y := ⟨D.base hD y, ⟨y, fun A u => D.base_spec hD y u⟩⟩
  left_inv a := by
    obtain ⟨t, y, hy⟩ := a
    refine Functor.OverTotal.ext' (D.base_unique hD y t hy).symm (Subtype.ext ?_)
    change (D.H hD).map (𝟙 T).op y = y
    simp
  right_inv y := rfl

noncomputable def totIso : (D.G hD).overTotal ≅ D.H hD :=
  NatIso.ofComponents (fun T => (D.totEquiv hD T.unop).toIso) (by
    intro X Y f
    refine ConcreteCategory.hom_ext _ _ fun a => ?_
    rfl)

theorem isSheaf_overTotal : Presheaf.IsSheaf Scheme.zariskiTopology (D.G hD).overTotal :=
  (Presheaf.isSheaf_of_iso_iff (D.totIso hD)).2 (D.H_isSheaf hD)

lemma Spec_map_aff_φ {A B : CommRingCat.{0}} (y : (D.H hD).obj (op (Spec A))) (u : Spec B ⟶ Spec A) :
    Spec.map (D.aff hD y u).φ = u ≫ Spec.map (D.aff hD y (𝟙 _)).φ := by
  rw [← Spec_map_aff_φ_comp, Category.comp_id]

lemma aff_toH_id {A : CommRingCat.{0}} (t : D.Tot A) : D.aff hD (D.toH hD t) (𝟙 (Spec A)) = t := by
  rw [aff_id, ofH_toH]

section ev

variable (A : Type) [CommRing A] [instA : Algebra R A]

noncomputable abbrev ovr : Over (Spec (CommRingCat.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))

def tot (s : D.F A) : D.Tot (CommRingCat.of A) :=
  ⟨CommRingCat.ofHom (algebraMap R A), D.T instA _ (RingHom.id A) (fun _ => rfl) s⟩

noncomputable def evFun (s : D.F A) : (D.G hD).obj (op (ovr A)) :=
  ⟨(D.toH hD (D.tot A s) : (D.H hD).obj (op (Spec (.of A)))),
    fun B (u : Spec B ⟶ Spec (.of A)) => by
      change Spec.map (D.aff hD (D.toH hD (D.tot A s)) u).φ =
        u ≫ Spec.map (CommRingCat.ofHom (algebraMap R A))
      rw [Spec_map_aff_φ, aff_toH_id]
      rfl⟩

noncomputable def germ (z : (D.G hD).obj (op (ovr A))) : D.Tot (CommRingCat.of A) :=
  D.aff hD (z.1 : (D.H hD).obj (op (Spec (.of A)))) (𝟙 (Spec (.of A)))

lemma germ_φ (z : (D.G hD).obj (op (ovr A))) : (D.germ hD A z).φ = CommRingCat.ofHom (algebraMap R A) := by
  apply Spec.map_injective
  exact (z.2 (CommRingCat.of A) (𝟙 (Spec (.of A)))).trans (Category.id_comp _)

lemma germ_φ_apply (z : (D.G hD).obj (op (ovr A))) (r : R) :
    (D.germ hD A z).φ.hom r = algebraMap R A r := by
  rw [germ_φ]; rfl

noncomputable def evInv (z : (D.G hD).obj (op (ovr A))) : D.F A :=
  (D.germ hD A z).out instA (D.germ_φ_apply hD A z)

lemma germ_evFun (s : D.F A) : D.germ hD A (D.evFun hD A s) = D.tot A s :=
  D.aff_toH_id hD (D.tot A s)

lemma tot_evInv (z : (D.G hD).obj (op (ovr A))) : D.tot A (D.evInv hD A z) = D.germ hD A z := by
  symm
  refine Tot.ext_of_out (D.germ_φ hD A z) ?_
  change D.T _ _ _ _ _ = D.T _ _ _ _ (D.T _ _ _ _ _)
  exact (D.T_comp_eq (RingHom.comp_id (RingHom.id A)) _).symm

noncomputable def ev : D.F A ≃ (D.G hD).obj (op (ovr A)) where
  toFun := D.evFun hD A
  invFun := D.evInv hD A
  left_inv s := by
    unfold evInv
    rw [Tot.out_congr (D.germ_evFun hD A s) instA _ (fun _ => rfl)]
    exact (D.T_comp_eq (RingHom.comp_id (RingHom.id A)) s).trans (D.T_eq_self rfl _ _)
  right_inv z := by
    apply Subtype.ext
    change D.toH hD (D.tot A (D.evInv hD A z)) = (z.1 : (D.H hD).obj (op (Spec (.of A))))
    rw [tot_evInv]
    exact (congrArg (D.toH hD) (D.aff_id hD _)).trans (D.toH_ofH hD _)

lemma ev_apply_val (s : D.F A) :
    ((D.ev hD A s).1 : (D.H hD).obj (op (Spec (.of A)))) = D.toH hD (D.tot A s) := rfl

end ev
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_exists_presheaf_over_equiv_isSheaf_overTotal_of_isLocalization_away.GrassBridgeH1.Datum"

theorem ev_natural (A B : Type) [CommRing A] [CommRing B] [instA : Algebra R A] [instB : Algebra R B]
    (φ : A →ₐ[R] B) (s : D.F A)
    (h : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R B))) :
    D.ev hD B (D.Fmap A B φ s) =
      (D.G hD).map (Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) h :
        ovr B ⟶ ovr A).op (D.ev hD A s) := by
  apply Subtype.ext
  change D.toH hD (D.tot B (D.Fmap A B φ s)) =
    (D.H hD).map (Spec.map (CommRingCat.ofHom φ.toRingHom)).op (D.toH hD (D.tot A s))
  rw [map_toH]
  congr 1
  symm
  refine Tot.ext_of_out ?_ ?_
  · apply CommRingCat.hom_ext
    ext r
    exact φ.commutes r
  · erw [out_P₀_map]
    change D.T _ _ _ _ (D.T _ _ _ _ s) = D.T _ _ _ _ (D.T _ _ _ _ s)
    exact (D.T_comp_eq (RingHom.comp_id φ.toRingHom) s).trans
      (D.T_comp_eq (RingHom.id_comp φ.toRingHom) s).symm

end Datum
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_exists_presheaf_over_equiv_isSheaf_overTotal_of_isLocalization_away.GrassBridgeH1.Datum"

end GrassBridgeH1
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_exists_presheaf_over_equiv_isSheaf_overTotal_of_isLocalization_away.GrassBridgeH1.Datum P2MW.S_AlgebraicGeometry_Scheme_exists_presheaf_over_equiv_isSheaf_overTotal_of_isLocalization_away.GrassBridgeH1"

open GrassBridgeH1 in
theorem solution
    (R : Type) [CommRing R]
    (F : ∀ (A : Type) [CommRing A] [Algebra R A], Type)
    (Fmap : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B],
      (A →ₐ[R] B) → F A → F B)
    (Fmap_id : ∀ (A : Type) [CommRing A] [Algebra R A] (s : F A), Fmap A A (AlgHom.id R A) s = s)
    (Fmap_comp : ∀ (A B C : Type) [CommRing A] [CommRing B] [CommRing C] [Algebra R A] [Algebra R B]
      [Algebra R C] (φ : A →ₐ[R] B) (ψ : B →ₐ[R] C) (s : F A),
      Fmap A C (ψ.comp φ) s = Fmap B C ψ (Fmap A B φ s))
    (sheaf : ∀ (A : Type) [CommRing A] [Algebra R A] (n : ℕ) (f : Fin n → A),
      Ideal.span (Set.range f) = ⊤ →
      ∀ (B : Fin n → Type) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)] [∀ i, Algebra R (B i)]
        [∀ i, IsScalarTower R A (B i)] [∀ i, IsLocalization.Away (f i) (B i)] (s : ∀ i, F (B i)),
      (∀ (i j : Fin n) (C : Type) [CommRing C] [Algebra A C] [Algebra R C] [IsScalarTower R A C]
          [IsLocalization.Away (f i * f j) C] (ρ₁ : B i →ₐ[A] C) (ρ₂ : B j →ₐ[A] C),
          Fmap _ _ (ρ₁.restrictScalars R) (s i) = Fmap _ _ (ρ₂.restrictScalars R) (s j)) →
      ∃! s₀ : F A, ∀ i, Fmap _ _ (IsScalarTower.toAlgHom R A (B i)) s₀ = s i) :
    ∃ (G : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ Type)
      (ev : ∀ (A : Type) [CommRing A] [Algebra R A],
        F A ≃ G.obj (op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))))),
      Presheaf.IsSheaf Scheme.zariskiTopology G.overTotal ∧
      ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B) (s : F A)
        (h : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
          Spec.map (CommRingCat.ofHom (algebraMap R B))),
        ev B (Fmap A B φ s) =
          G.map (Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) h :
            Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B))) ⟶
              Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))).op (ev A s) := by
  let D : Datum R := ⟨F, Fmap, Fmap_id, Fmap_comp⟩
  have hD : D.IsSheaf := sheaf
  exact ⟨D.G hD, fun A _ _ => D.ev hD A, D.isSheaf_overTotal hD,
    fun A B _ _ _ _ φ s h => D.ev_natural hD A B φ s h⟩

end S_AlgebraicGeometry_Scheme_exists_presheaf_over_equiv_isSheaf_overTotal_of_isLocalization_away
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_exists_presheaf_over_equiv_isSheaf_overTotal_of_isLocalization_away (solution)
