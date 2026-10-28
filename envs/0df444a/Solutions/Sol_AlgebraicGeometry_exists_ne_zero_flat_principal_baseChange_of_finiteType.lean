-- Prove2me | solution 1 for AlgebraicGeometry.exists_ne_zero_flat_principal_baseChange_of_finiteType
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-25T16:59:07.065395+00:00
-- url     : https://prove2.me/submissions/2f68151c-6525-440f-abca-83ac6ca042bc

import Mathlib
import Theorems.Thm_Module_Flat_exists_ne_zero_flat_localization_tensorProduct

universe u
set_option linter.style.haveILetI false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PhilipponGenericFlatness

lemma flat_of_comp_openImmersion
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (j : Y ⟶ Z)
    [IsOpenImmersion j] [Flat (f ≫ j)] : Flat f := by
  apply Flat.of_stalkMap
  intro x
  apply (RingHom.Flat.respectsIso.cancel_left_isIso
    (j.stalkMap (f x)) (f.stalkMap x)).mp
  rw [← CommRingCat.hom_comp, ← Scheme.Hom.stalkMap_comp]
  exact Flat.stalkMap (f ≫ j) x

lemma flat_restrict_of_flat_localization
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (a : A) [Module.Flat A (Localization.Away (algebraMap A B a))] :
    Flat ((Spec.map (CommRingCat.ofHom (algebraMap A B))) ∣_ (PrimeSpectrum.basicOpen a)) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let U : (Spec (.of A)).Opens := PrimeSpectrum.basicOpen a
  let V := f ⁻¹ᵁ U
  have hV : V = PrimeSpectrum.basicOpen (algebraMap A B a) := by
    ext x
    rfl
  let e : (V : Scheme) ≅ Spec (.of (Localization.Away (algebraMap A B a))) :=
    ((Spec (.of B)).isoOfEq hV) ≪≫ basicOpenIsoSpecAway (R := .of B) (algebraMap A B a)
  have he : e.hom ≫ Spec.map (CommRingCat.ofHom
      (algebraMap B (Localization.Away (algebraMap A B a)))) = V.ι := by
    dsimp only [e, Iso.trans_hom]
    rw [Category.assoc, basicOpenIsoSpecAway_hom_SpecMap]
    exact Scheme.isoOfEq_hom_ι _ hV
  have hcomp : Flat (V.ι ≫ f) := by
    have hφ : Flat (Spec.map (CommRingCat.ofHom
        (algebraMap A (Localization.Away (algebraMap A B a))))) :=
      Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
    have h : Flat (e.hom ≫ Spec.map (CommRingCat.ofHom
        (algebraMap A (Localization.Away (algebraMap A B a))))) := inferInstance
    have hm : CommRingCat.ofHom (algebraMap A B) ≫ CommRingCat.ofHom
        (algebraMap B (Localization.Away (algebraMap A B a))) =
        CommRingCat.ofHom (algebraMap A (Localization.Away (algebraMap A B a))) := by
      apply CommRingCat.hom_ext
      exact (IsScalarTower.algebraMap_eq A B _).symm
    rw [← hm, Spec.map_comp, ← Category.assoc, he] at h
    exact h
  haveI : Flat ((f ∣_ U) ≫ U.ι) := by
    rw [(isPullback_morphismRestrict f U).w]
    exact hcomp
  exact flat_of_comp_openImmersion (f ∣_ U) U.ι

lemma flat_stalk_of_flat_open
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (j : Z ⟶ X)
    [IsOpenImmersion j] [Flat (j ≫ f)] (x : Z) :
    (f.stalkMap (j x)).hom.Flat := by
  apply (RingHom.Flat.respectsIso.cancel_right_isIso
    (f.stalkMap (j x)) (j.stalkMap x)).mp
  rw [← CommRingCat.hom_comp, ← Scheme.Hom.stalkMap_comp]
  exact Flat.stalkMap (j ≫ f) x

lemma flat_restrict_of_cover_by_flat_opens
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens)
    {I : Type u} (W : I → X.Opens) (hW : ∀ i, Flat ((W i).ι ≫ f))
    (hcover : ∀ x : X, f x ∈ V → ∃ i, x ∈ W i) : Flat (f ∣_ V) := by
  have H : Flat ((f ⁻¹ᵁ V).ι ≫ f) := by
    apply Flat.of_stalkMap
    intro x
    obtain ⟨i, hi⟩ := hcover x.val x.property
    haveI : Flat ((W i).ι ≫ f) := hW i
    have hx := flat_stalk_of_flat_open f (W i).ι ⟨x.val, hi⟩
    change (f.stalkMap ((f ⁻¹ᵁ V).ι x)).hom.Flat at hx
    have h := (RingHom.Flat.respectsIso.cancel_right_isIso
      (f.stalkMap ((f ⁻¹ᵁ V).ι x)) ((f ⁻¹ᵁ V).ι.stalkMap x)).mpr hx
    rw [← CommRingCat.hom_comp, ← Scheme.Hom.stalkMap_comp] at h
    exact h
  haveI : Flat ((f ∣_ V) ≫ V.ι) := by
    rw [(isPullback_morphismRestrict f V).w]
    exact H
  exact flat_of_comp_openImmersion (f ∣_ V) V.ι

/-- A base map landing in a flat restriction has flat scheme base change. -/
lemma flat_pullback_of_flat_restrict
    {X Y T : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) [Flat (f ∣_ U)]
    (b : T ⟶ Y) (hb : Set.range b ⊆ U) : Flat (pullback.snd f b) := by
  let bU := IsOpenImmersion.lift U.ι b (by simpa only [Scheme.Opens.range_ι] using hb)
  have hbU : bU ≫ U.ι = b := IsOpenImmersion.lift_fac _ _ _
  let hp := (isPullback_morphismRestrict f U).flip
  have hw : pullback.fst f b ≫ f = (pullback.snd f b ≫ bU) ≫ U.ι := by
    rw [Category.assoc, hbU]
    exact pullback.condition
  let r := hp.lift (pullback.fst f b) (pullback.snd f b ≫ bU) hw
  have hpr : IsPullback r (pullback.snd f b) (f ∣_ U) bU := by
    refine IsPullback.of_right ?_ (hp.lift_snd _ _ _) hp
    rw [hp.lift_fst, hbU]
    exact IsPullback.of_hasPullback f b
  exact MorphismProperty.of_isPullback hpr inferInstance

end PhilipponGenericFlatness



set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace PhilipponGenericFlatness

/-- Algebraic generic flatness on one affine chart, with the actual
principal localization of the coordinate ring retained. -/
lemma exists_ne_zero_flat_away
    (A B : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [CommRing B] [Algebra A B] [Algebra.FiniteType A B] :
    ∃ a : A, a ≠ 0 ∧ Module.Flat A (Localization.Away (algebraMap A B a)) := by
  obtain ⟨a, ha, hflat⟩ :=
    Module.Flat.exists_ne_zero_flat_localization_tensorProduct (A := A) (B := B) (M := B)
  let C := Localization.Away (algebraMap A B a)
  haveI : Module.Flat A (C ⊗[B] B) := hflat
  have he : (C ⊗[B] B) ≃ₗ[A] C := (TensorProduct.rid B C).restrictScalars A
  exact ⟨a, ha, Module.Flat.of_linearEquiv he.symm⟩

/-- One affine chart of a finite-type scheme becomes flat over one
nonempty base basic open. Its image open is retained in the whole scheme. -/
lemma exists_flat_open_of_affine_chart
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {X Z : Scheme.{u}} [IsAffine Z]
    (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f]
    (j : Z ⟶ X) [IsOpenImmersion j] :
    ∃ a : A, a ≠ 0 ∧ ∃ W : X.Opens,
      Flat (W.ι ≫ f) ∧
      ∀ x : X, x ∈ Set.range j → f x ∈ PrimeSpectrum.basicOpen a → x ∈ W := by
  classical
  let R := Γ(Z, ⊤)
  let j' := Z.isoSpec.inv ≫ j
  let φ : CommRingCat.of A ⟶ R := Spec.preimage (j' ≫ f)
  have hφ : Spec.map φ = j' ≫ f := Spec.map_preimage _
  letI : Algebra A R := φ.hom.toAlgebra
  haveI : Algebra.FiniteType A R := by
    haveI : LocallyOfFiniteType (Spec.map φ) := by rw [hφ]; infer_instance
    change φ.hom.FiniteType
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φ)).mp inferInstance
  obtain ⟨a, ha, hflat⟩ := exists_ne_zero_flat_away A R
  haveI : Module.Flat A (Localization.Away (algebraMap A R a)) := hflat
  let U : (Spec (.of A)).Opens := PrimeSpectrum.basicOpen a
  let V := (j' ≫ f) ⁻¹ᵁ U
  haveI : Flat ((j' ≫ f) ∣_ U) := by
    rw [← hφ]
    exact flat_restrict_of_flat_localization A R a
  haveI : Flat (V.ι ≫ j' ≫ f) := by
    have H : Flat (((j' ≫ f) ∣_ U) ≫ U.ι) := inferInstance
    rw [morphismRestrict_ι] at H
    simpa only [Category.assoc] using H
  let W := j' ''ᵁ V
  have hW : Flat (W.ι ≫ f) := by
    rw [← j'.isoImage_inv_ι V, Category.assoc, Category.assoc]
    infer_instance
  refine ⟨a, ha, W, hW, ?_⟩
  intro x hx hfx
  obtain ⟨z, hz⟩ := hx
  let z' := Z.isoSpec.hom z
  have hz' : j' z' = x := by
    dsimp only [j', z']
    rw [Scheme.Hom.comp_apply, Scheme.hom_inv_apply]
    exact hz
  change x ∈ (j' ''ᵁ V)
  change ∃ y, y ∈ V ∧ j' y = x
  refine ⟨z', ?_, hz'⟩
  change f (j' z') ∈ U
  rw [hz']
  exact hfx

/-- Generic flatness for a quasi-compact scheme of finite type over a
noetherian domain, retaining a common dense open of the actual base. -/
theorem exists_dense_open_flat
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {X : Scheme.{u}} [CompactSpace X]
    (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] :
    ∃ U : (Spec (.of A)).Opens,
      (⊥ : PrimeSpectrum A) ∈ U ∧ Dense (U : Set (Spec (.of A))) ∧ Flat (f ∣_ U) := by
  classical
  let 𝒰 := X.affineCover.finiteSubcover
  have h : ∀ i : 𝒰.I₀, ∃ a : A, a ≠ 0 ∧ ∃ W : X.Opens,
      Flat (W.ι ≫ f) ∧
      ∀ x : X, x ∈ Set.range (𝒰.f i) → f x ∈ PrimeSpectrum.basicOpen a → x ∈ W := by
    intro i
    exact exists_flat_open_of_affine_chart A f (𝒰.f i)
  choose a ha W hW hcover using h
  let U : (Spec (.of A)).Opens := ⨅ i, PrimeSpectrum.basicOpen (a i)
  have hU : (⊥ : PrimeSpectrum A) ∈ U := by
    change (⊥ : PrimeSpectrum A) ∈ ((⨅ i, PrimeSpectrum.basicOpen (a i) :
      TopologicalSpace.Opens (PrimeSpectrum A)) : Set (PrimeSpectrum A))
    rw [TopologicalSpace.Opens.coe_iInf]
    apply Set.mem_iInter.mpr
    intro i
    change a i ∉ (⊥ : Ideal A)
    simpa only [Ideal.mem_bot] using ha i
  have hd : Dense (U : Set (Spec (.of A))) := U.isOpen.dense ⟨(⊥ : PrimeSpectrum A), hU⟩
  refine ⟨U, hU, hd, flat_restrict_of_cover_by_flat_opens f U W hW ?_⟩
  intro x hx
  let i := 𝒰.idx x
  have hxrange : x ∈ Set.range (𝒰.f i) := 𝒰.covers x
  refine ⟨i, hcover i x hxrange ?_⟩
  exact (iInf_le (fun i => PrimeSpectrum.basicOpen (a i)) i) hx

/-- Generic flatness on the actual base change to one principal
localization of the prescribed noetherian affine base. -/
theorem exists_ne_zero_flat_baseChange
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {X : Scheme.{u}} [CompactSpace X]
    (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] :
    ∃ a : A, a ≠ 0 ∧
      Flat (pullback.snd f (Spec.map (CommRingCat.ofHom
        (algebraMap A (Localization.Away a))))) := by
  obtain ⟨U, hU, _hd, hflat⟩ := exists_dense_open_flat A f
  obtain ⟨D, ⟨a, rfl⟩, ha, hDU⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp PrimeSpectrum.isBasis_basic_opens hU
  have ha0 : a ≠ 0 := by
    change a ∉ (⊥ : Ideal A) at ha
    simpa only [Ideal.mem_bot] using ha
  haveI : Flat (f ∣_ U) := hflat
  refine ⟨a, ha0, flat_pullback_of_flat_restrict f U _ ?_⟩
  rintro x ⟨z, rfl⟩
  apply hDU
  exact (PrimeSpectrum.localization_away_comap_range (Localization.Away a) a).le ⟨z, rfl⟩

end PhilipponGenericFlatness

theorem solution
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {X : Scheme.{u}} [CompactSpace X]
    (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] :
    ∃ a : A, a ≠ 0 ∧
      Flat (pullback.snd f (Spec.map (CommRingCat.ofHom
        (algebraMap A (Localization.Away a))))) := by
  exact PhilipponGenericFlatness.exists_ne_zero_flat_baseChange A f
