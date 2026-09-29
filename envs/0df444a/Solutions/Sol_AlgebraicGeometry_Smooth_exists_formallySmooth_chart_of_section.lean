-- Prove2me | solution 1 for AlgebraicGeometry.Smooth.exists_formallySmooth_chart_of_section
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/365934e5-a4d7-5d17-bcd4-b1c02653a128

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Smooth_exists_formallySmooth_chart_of_section

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry NeronModelInfra

namespace SmoothChartOfSectionP3

section ConormalOfSection

open TensorProduct KaehlerDifferential

variable {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]

theorem kerCotangentToTensor_bijective_of_section (ε : B →ₐ[R] R) :
    letI : Algebra B R := ε.toRingHom.toAlgebra
    haveI : IsScalarTower R B R := IsScalarTower.of_algebraMap_eq fun r => (ε.commutes r).symm
    Function.Bijective (kerCotangentToTensor R B R) := by
  letI : Algebra B R := ε.toRingHom.toAlgebra
  haveI : IsScalarTower R B R := IsScalarTower.of_algebraMap_eq fun r => (ε.commutes r).symm
  have hsurj : Function.Surjective (algebraMap B R) := fun r => ⟨algebraMap R B r, ε.commutes r⟩
  constructor
  ·
    obtain ⟨⟨l, hl⟩⟩ : Nonempty { l // l ∘ₗ (kerCotangentToTensor R B R) = LinearMap.id } :=
      ⟨(retractionKerCotangentToTensorEquivSection (R := R) (P := B) (S := R) hsurj).symm
        ⟨Algebra.ofId R _, Subsingleton.elim _ _⟩⟩
    intro a b hab
    have ha := LinearMap.congr_fun hl a
    have hb := LinearMap.congr_fun hl b
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at ha hb
    rw [← ha, ← hb, hab]
  ·
    intro t
    have hex := KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R B R hsurj
    have ht : KaehlerDifferential.mapBaseChange R B R t = 0 := Subsingleton.elim _ _
    exact (hex t).mp ht

theorem exists_conormal_basis [Module.Free B Ω[B⁄R]] [Module.Finite B Ω[B⁄R]] (ε : B →ₐ[R] R) :
    ∃ (g : ℕ) (x : Fin g → B), (∀ j, ε (x j) = 0) ∧
      (RingHom.ker ε ≤ Ideal.span (Set.range x) ⊔ RingHom.ker ε ^ 2) ∧
      (∀ c : Fin g → R, (∑ j, c j • x j) ∈ RingHom.ker ε ^ 2 → c = 0) := by
  classical
  letI : Algebra B R := ε.toRingHom.toAlgebra
  haveI : IsScalarTower R B R := IsScalarTower.of_algebraMap_eq fun r => (ε.commutes r).symm
  set I : Ideal B := RingHom.ker (algebraMap B R) with hI
  have hIε : RingHom.ker ε = I := rfl

  let κ : I.Cotangent ≃ₗ[B] R ⊗[B] Ω[B⁄R] :=
    LinearEquiv.ofBijective _ (kerCotangentToTensor_bijective_of_section ε)
  let κR : I.Cotangent ≃ₗ[R] R ⊗[B] Ω[B⁄R] := κ.restrictScalars R

  let β := Module.Free.chooseBasis B Ω[B⁄R]
  let ιT := Module.Free.ChooseBasisIndex B Ω[B⁄R]
  let βR : Module.Basis ιT R (R ⊗[B] Ω[B⁄R]) := β.baseChange R
  let g : ℕ := Fintype.card ιT
  let eFin : ιT ≃ Fin g := Fintype.equivFin ιT
  let bI : Module.Basis (Fin g) R I.Cotangent := (βR.map κR.symm).reindex eFin

  have hlift : ∀ j : Fin g, ∃ y : I, I.toCotangent y = bI j := fun j =>
    I.toCotangent_surjective (bI j)
  choose y hy using hlift
  refine ⟨g, fun j => (y j : B), fun j => (y j).2, ?_, ?_⟩
  ·
    rw [hIε]
    intro b hb
    have hrepr := bI.sum_repr (I.toCotangent ⟨b, hb⟩)
    have hdiff : (⟨b, hb⟩ : I) - ∑ j, (bI.repr (I.toCotangent ⟨b, hb⟩) j) • y j ∈
        LinearMap.ker I.toCotangent := by
      rw [LinearMap.mem_ker, map_sub, map_sum]
      simp_rw [LinearMap.map_smul_of_tower, hy]
      rw [hrepr, sub_self]
    rw [Ideal.mem_toCotangent_ker] at hdiff
    have hb' : b = (∑ j, (bI.repr (I.toCotangent ⟨b, hb⟩) j) • (y j : B)) +
        (((⟨b, hb⟩ : I) - ∑ j, (bI.repr (I.toCotangent ⟨b, hb⟩) j) • y j : I) : B) := by
      simp
    rw [hb']
    refine Submodule.add_mem_sup (Ideal.sum_mem _ fun j _ => ?_) hdiff
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
  ·
    intro c hc
    rw [hIε] at hc
    have hmem : (∑ j, c j • (y j : B)) ∈ I :=
      I.sum_mem fun j _ => by rw [Algebra.smul_def]; exact I.mul_mem_left _ (y j).2
    have h0 : I.toCotangent ⟨_, hmem⟩ = 0 := (I.toCotangent_eq_zero _).mpr hc
    have hsum : (⟨_, hmem⟩ : I) = ∑ j, c j • y j := by
      apply Subtype.ext; simp
    rw [hsum, map_sum] at h0
    simp_rw [LinearMap.map_smul_of_tower, hy] at h0
    exact funext fun j => by
      simpa using (Fintype.linearIndependent_iff.mp bI.linearIndependent c h0 j)

end ConormalOfSection

section Geometry

variable {R : Type u} [CommRing R] {A : Scheme.{u}}

local notation "SR" => Spec (CommRingCat.of R)

theorem exists_chart (f : A ⟶ SR) [Smooth f] (s : SR ⟶ A) (hs : s ≫ f = 𝟙 _) (p : SR) :
    ∃ (r : Γ(SR, ⊤)) (W : A.Opens) (_ : IsAffineOpen W) (eW : W ≤ f ⁻¹ᵁ (SR).basicOpen r),
      p ∈ (SR).basicOpen r ∧ (SR).basicOpen r ≤ s ⁻¹ᵁ W ∧
        (f.appLE ((SR).basicOpen r) W eW).hom.IsStandardSmooth := by
  obtain ⟨U, hU, V, hV, hxV, e, hstd⟩ := Smooth.exists_isStandardSmooth f (s p)
  have hfs : f (s p) = p := by
    rw [← Scheme.Hom.comp_apply, hs]; rfl
  have hpU : p ∈ U := by
    have : f (s p) ∈ U := e hxV
    rwa [hfs] at this

  obtain ⟨r, hrle, hpr⟩ :=
    (isAffineOpen_top SR).exists_basicOpen_le ⟨p, (show p ∈ U ⊓ s ⁻¹ᵁ V from ⟨hpU, hxV⟩)⟩ trivial

  let rU : Γ(SR, U) := (SR).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op r
  have hDU : (SR).basicOpen rU = (SR).basicOpen r := by
    rw [Scheme.basicOpen_res]
    exact inf_eq_right.mpr (hrle.trans inf_le_left)

  let W : A.Opens := A.basicOpen (f.appLE U V e rU)
  have hW : IsAffineOpen W := hV.basicOpen _
  have hWeq : W = V ⊓ f ⁻¹ᵁ (SR).basicOpen rU := by
    simp only [W, Scheme.Hom.appLE, CommRingCat.comp_apply]
    rw [Scheme.basicOpen_res, Scheme.preimage_basicOpen]
  have eW' : W ≤ f ⁻¹ᵁ (SR).basicOpen rU := hWeq ▸ inf_le_right
  have key := AlgebraicGeometry.IsAffineOpen.appLE_eq_away_map f hU hV e rU
  have hstdW : (f.appLE ((SR).basicOpen rU) W eW').hom.IsStandardSmooth := by
    have := hU.isLocalization_basicOpen rU
    have := hV.isLocalization_basicOpen (f.appLE U V e rU)
    rw [key]
    exact RingHom.isStandardSmooth_localizationPreserves.away _ _ _ _ hstd
  have eW : W ≤ f ⁻¹ᵁ (SR).basicOpen r := hDU ▸ eW'
  refine ⟨r, W, hW, eW, hpr, ?_, ?_⟩
  ·
    rw [hWeq, hDU]
    intro q hq
    refine ⟨hrle hq |>.2, ?_⟩
    show f (s q) ∈ (SR).basicOpen r
    rw [← Scheme.Hom.comp_apply, hs]
    exact hq
  · exact (f.appLE_congr eW' hDU rfl (fun g => g.hom.IsStandardSmooth)).mp hstdW

noncomputable def rho (r : Γ(SR, ⊤)) : CommRingCat.of R ⟶ Γ(SR, (SR).basicOpen r) :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (SR).presheaf.map (homOfLE ((SR).basicOpen_le r)).op

theorem fromSpec_basicOpen_eq (r : Γ(SR, ⊤)) :
    ((isAffineOpen_top SR).basicOpen r).fromSpec = Spec.map (rho r) := by
  rw [← IsAffineOpen.map_fromSpec (isAffineOpen_top SR) ((isAffineOpen_top SR).basicOpen r)
    (homOfLE ((SR).basicOpen_le r)).op, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv,
    ← Spec.map_comp]
  rfl

theorem isLocalization_rho (r : Γ(SR, ⊤)) :
    @IsLocalization.Away R _ ((Scheme.ΓSpecIso (CommRingCat.of R)).hom r)
      Γ(SR, (SR).basicOpen r) _ (rho r).hom.toAlgebra := by
  have h := IsLocalization.isLocalization_of_base_ringEquiv (.powers r) Γ(SR, (SR).basicOpen r)
    (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
  rw [Submonoid.map_powers] at h
  exact h

theorem appLE_section_comp (f : A ⟶ SR) (s : SR ⟶ A) (hs : s ≫ f = 𝟙 _)
    (D : (SR).Opens) (W : A.Opens) (eW : W ≤ f ⁻¹ᵁ D) (hsW : D ≤ s ⁻¹ᵁ W) :
    (s.appLE W D hsW).hom.comp (f.appLE D W eW).hom = RingHom.id _ := by
  rw [← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]
  have : ∀ (g : SR ⟶ SR) (_ : g = 𝟙 _) (e'), (g.appLE D D e').hom = RingHom.id _ := by
    rintro g rfl e'
    simp [Scheme.Hom.appLE]
    rfl
  exact this _ hs _

theorem fromSpec_comp (f : A ⟶ SR) (r : Γ(SR, ⊤)) (W : A.Opens) (hW : IsAffineOpen W)
    (eW : W ≤ f ⁻¹ᵁ (SR).basicOpen r) :
    hW.fromSpec ≫ f =
      Spec.map (f.appLE ((SR).basicOpen r) W eW) ≫ Spec.map (rho r) := by
  rw [← fromSpec_basicOpen_eq, IsAffineOpen.SpecMap_appLE_fromSpec]

theorem section_fromSpec (s : SR ⟶ A) (r : Γ(SR, ⊤)) (W : A.Opens) (hW : IsAffineOpen W)
    (hsW : (SR).basicOpen r ≤ s ⁻¹ᵁ W) :
    Spec.map (s.appLE W ((SR).basicOpen r) hsW) ≫ hW.fromSpec = Spec.map (rho r) ≫ s := by
  rw [← fromSpec_basicOpen_eq, IsAffineOpen.SpecMap_appLE_fromSpec]

end Geometry

section Points

variable {A : Scheme.{u}}

noncomputable def toHom (W : A.Opens) {C : Type u} [CommRing C] (φ : Γ(A, W) →+* C) :
    Γ(A, W) ⟶ CommRingCat.of C :=
  CommRingCat.ofHom φ

@[scoped simp] theorem toHom_hom (W : A.Opens) {C : Type u} [CommRing C] (φ : Γ(A, W) →+* C) :
    (toHom W φ).hom = φ := rfl

theorem toHom_comp (W : A.Opens) {C C' : Type u} [CommRing C] [CommRing C']
    (φ : Γ(A, W) →+* C) (ψ : C →+* C') :
    toHom W (ψ.comp φ) = toHom W φ ≫ CommRingCat.ofHom ψ := rfl

noncomputable def iotaHom {W : A.Opens} (hW : IsAffineOpen W) {C : Type u} [CommRing C]
    (φ : Γ(A, W) →+* C) : Spec (CommRingCat.of C) ⟶ A :=
  Spec.map (toHom W φ) ≫ hW.fromSpec

theorem iotaHom_comp {W : A.Opens} (hW : IsAffineOpen W) {C C' : Type u} [CommRing C]
    [CommRing C'] (φ : Γ(A, W) →+* C) (ψ : C →+* C') :
    iotaHom hW (ψ.comp φ) = Spec.map (CommRingCat.ofHom ψ) ≫ iotaHom hW φ := by
  simp only [iotaHom, toHom_comp, Spec.map_comp, Category.assoc]

theorem iotaHom_injective {W : A.Opens} (hW : IsAffineOpen W) {C : Type u} [CommRing C] :
    Function.Injective (iotaHom (C := C) hW) := by
  intro φ₁ φ₂ h
  have h1 : Spec.map (toHom W φ₁) = Spec.map (toHom W φ₂) :=
    (cancel_mono hW.fromSpec).mp h
  have h2 := Spec.map_injective h1
  exact congrArg CommRingCat.Hom.hom h2

theorem range_comp_quotient_eq {C : Type u} [CommRing C] (J : Ideal C) (hJ : IsNilpotent J)
    (P : Spec (CommRingCat.of C) ⟶ A) :
    Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ P) = Set.range P := by
  have hle : J ≤ nilradical C := by
    obtain ⟨n, hn⟩ := hJ
    intro x hx
    exact mem_nilradical.mpr ⟨n, by
      have := Ideal.pow_mem_pow hx n
      rw [hn] at this
      simpa using this⟩
  have hsurj : Function.Surjective (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    (PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical hle).2
  ext y
  simp only [Set.mem_range, Scheme.Hom.comp_apply]
  constructor
  · rintro ⟨q, rfl⟩; exact ⟨_, rfl⟩
  · rintro ⟨q, rfl⟩
    obtain ⟨q', rfl⟩ := hsurj q
    exact ⟨q', rfl⟩

theorem exists_iotaHom_eq {W : A.Opens} (hW : IsAffineOpen W) {C : Type u} [CommRing C]
    (P : Spec (CommRingCat.of C) ⟶ A) (hP : Set.range P ⊆ Set.range hW.fromSpec) :
    ∃ φ : Γ(A, W) →+* C, iotaHom hW φ = P := by
  let l := IsOpenImmersion.lift hW.fromSpec P hP
  refine ⟨(Spec.preimage l).hom, ?_⟩
  simp only [iotaHom]
  have : toHom W (Spec.preimage l).hom = Spec.preimage l := rfl
  rw [this, Spec.map_preimage, IsOpenImmersion.lift_fac]

theorem range_iotaHom_subset {W : A.Opens} (hW : IsAffineOpen W) {C : Type u} [CommRing C]
    (φ : Γ(A, W) →+* C) : Set.range (iotaHom hW φ) ⊆ Set.range hW.fromSpec := by
  rintro _ ⟨q, rfl⟩
  exact ⟨_, (Scheme.Hom.comp_apply _ _ q).symm⟩

end Points

section Package

variable {R : Type u} [CommRing R] {A : Scheme.{u}}

local notation "SR" => Spec (CommRingCat.of R)

theorem iotaHom_comp_structure (f : A ⟶ SR) (r : Γ(SR, ⊤)) (W : A.Opens) (hW : IsAffineOpen W)
    (eW : W ≤ f ⁻¹ᵁ (SR).basicOpen r) {C : Type u} [CommRing C] (φ : Γ(A, W) →+* C) :
    iotaHom hW φ ≫ f = Spec.map (rho r ≫ f.appLE ((SR).basicOpen r) W eW ≫ toHom W φ) := by
  simp only [iotaHom, Category.assoc, fromSpec_comp f r W hW eW, Spec.map_comp]

theorem chart_package (f : A ⟶ SR) (s : SR ⟶ A) (hs : s ≫ f = 𝟙 _) (r : Γ(SR, ⊤))
    (W : A.Opens) (hW : IsAffineOpen W) (eW : W ≤ f ⁻¹ᵁ (SR).basicOpen r)
    (hsW : (SR).basicOpen r ≤ s ⁻¹ᵁ W)
    (hstd : (f.appLE ((SR).basicOpen r) W eW).hom.IsStandardSmooth)
    (Rᵢ : Type u) [CommRing Rᵢ] [Algebra R Rᵢ]
    [IsLocalization.Away ((Scheme.ΓSpecIso (CommRingCat.of R)).hom r) Rᵢ] :
    ∃ (g : ℕ) (B : Type u) (_ : CommRing B) (_ : Algebra Rᵢ B) (_ : Algebra.FormallySmooth Rᵢ B)
      (ε : B →ₐ[Rᵢ] Rᵢ) (x : Fin g → B)
      (ι : ∀ (C : Type u) [CommRing C] [Algebra Rᵢ C],
        (B →ₐ[Rᵢ] C) →
          SchemeHomOver (Spec.map (CommRingCat.ofHom ((algebraMap Rᵢ C).comp (algebraMap R Rᵢ)))) f),
      (∀ j, ε (x j) = 0) ∧
      (RingHom.ker ε ≤ Ideal.span (Set.range x) ⊔ RingHom.ker ε ^ 2) ∧
      (∀ c : Fin g → Rᵢ, (∑ j, c j • x j) ∈ RingHom.ker ε ^ 2 → c = 0) ∧
      (∀ (C C' : Type u) [CommRing C] [Algebra Rᵢ C] [CommRing C'] [Algebra Rᵢ C']
        (ψ : C →ₐ[Rᵢ] C') (φ : B →ₐ[Rᵢ] C),
          (ι C' (ψ.comp φ)).1 = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ (ι C φ).1) ∧
      (∀ (C : Type u) [CommRing C] [Algebra Rᵢ C], Function.Injective (ι C)) ∧
      ((ι Rᵢ ε).1 = Spec.map (CommRingCat.ofHom (algebraMap R Rᵢ)) ≫ s) ∧
      (∀ (C : Type u) [CommRing C] [Algebra Rᵢ C] (J : Ideal C), IsNilpotent J →
        ∀ (P : SchemeHomOver (Spec.map (CommRingCat.ofHom ((algebraMap Rᵢ C).comp (algebraMap R Rᵢ)))) f)
          (φ₀ : B →ₐ[Rᵢ] C ⧸ J),
          (ι (C ⧸ J) φ₀).1 = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ P.1 →
            ∃ φ : B →ₐ[Rᵢ] C, ι C φ = P) := by
  classical

  let R₀ : Type u := Γ(SR, (SR).basicOpen r)
  let B₀ : Type u := Γ(A, W)
  let φ₀ : R₀ →+* B₀ := (f.appLE ((SR).basicOpen r) W eW).hom
  let ε₀ : B₀ →+* R₀ := (s.appLE W ((SR).basicOpen r) hsW).hom
  have hεφ : ε₀.comp φ₀ = RingHom.id R₀ := appLE_section_comp f s hs _ W eW hsW

  letI algR : Algebra R R₀ := (rho r).hom.toAlgebra
  haveI : IsLocalization.Away ((Scheme.ΓSpecIso (CommRingCat.of R)).hom r) R₀ :=
    isLocalization_rho r
  let e : Rᵢ ≃ₐ[R] R₀ :=
    IsLocalization.algEquiv (.powers ((Scheme.ΓSpecIso (CommRingCat.of R)).hom r)) Rᵢ R₀
  have he : ∀ y : R, e (algebraMap R Rᵢ y) = (rho r).hom y := fun y => e.commutes y
  have hloc : ∀ (C : Type u) [CommRing C] (g₁ g₂ : Rᵢ →+* C),
      g₁.comp (algebraMap R Rᵢ) = g₂.comp (algebraMap R Rᵢ) → g₁ = g₂ :=
    fun C _ g₁ g₂ h =>
      IsLocalization.ringHom_ext (.powers ((Scheme.ΓSpecIso (CommRingCat.of R)).hom r)) h

  let φᵢ : Rᵢ →+* B₀ := φ₀.comp (e : Rᵢ →+* R₀)
  letI algB : Algebra Rᵢ B₀ := φᵢ.toAlgebra
  have hstdᵢ : φᵢ.IsStandardSmooth :=
    RingHom.isStandardSmooth_respectsIso.2 φ₀ e.toRingEquiv hstd
  haveI : Algebra.IsStandardSmooth Rᵢ B₀ := hstdᵢ.toAlgebra
  have hFS : Algebra.FormallySmooth Rᵢ B₀ := inferInstance
  haveI : Module.Free B₀ Ω[B₀⁄Rᵢ] := inferInstance
  haveI : Module.Finite B₀ Ω[B₀⁄Rᵢ] := inferInstance

  let εᵢ : B₀ →ₐ[Rᵢ] Rᵢ :=
    { toRingHom := (e.symm : R₀ →+* Rᵢ).comp ε₀
      commutes' := fun y => by
        change e.symm (ε₀ (φ₀ (e y))) = y
        have := congrArg (fun h : R₀ →+* R₀ => h (e y)) hεφ
        simp only [RingHom.comp_apply, RingHom.id_apply] at this
        rw [this]
        exact e.symm_apply_apply y }
  have hεᵢ : (εᵢ : B₀ →+* Rᵢ) = (e.symm : R₀ →+* Rᵢ).comp ε₀ := rfl
  obtain ⟨g, x, hx, hgen, hind⟩ := exists_conormal_basis εᵢ

  have hover : ∀ (C : Type u) [CommRing C] [Algebra Rᵢ C] (φ : B₀ →ₐ[Rᵢ] C),
      iotaHom hW (φ : B₀ →+* C) ≫ f =
        Spec.map (CommRingCat.ofHom ((algebraMap Rᵢ C).comp (algebraMap R Rᵢ))) := by
    intro C _ _ φ
    rw [iotaHom_comp_structure f r W hW eW]
    congr 1
    ext y
    change φ (φ₀ ((rho r).hom y)) = algebraMap Rᵢ C (algebraMap R Rᵢ y)
    rw [← he, ← φ.commutes]
    rfl
  let ι : ∀ (C : Type u) [CommRing C] [Algebra Rᵢ C], (B₀ →ₐ[Rᵢ] C) →
      SchemeHomOver (Spec.map (CommRingCat.ofHom ((algebraMap Rᵢ C).comp (algebraMap R Rᵢ)))) f :=
    fun C _ _ φ => ⟨iotaHom hW (φ : B₀ →+* C), hover C φ⟩
  have hι : ∀ (C : Type u) [CommRing C] [Algebra Rᵢ C] (φ : B₀ →ₐ[Rᵢ] C),
      (ι C φ).1 = iotaHom hW (φ : B₀ →+* C) := fun C _ _ φ => rfl
  refine ⟨g, B₀, inferInstance, algB, hFS, εᵢ, x, ι, hx, hgen, hind, ?_, ?_, ?_, ?_⟩
  ·
    intro C C' _ _ _ _ ψ φ
    rw [hι, hι]
    exact iotaHom_comp hW (φ : B₀ →+* C) (ψ : C →+* C')
  ·
    intro C _ _ φ₁ φ₂ h
    have h1 : iotaHom hW (φ₁ : B₀ →+* C) = iotaHom hW (φ₂ : B₀ →+* C) := by
      rw [← hι, ← hι, h]
    exact AlgHom.coe_ringHom_injective (iotaHom_injective hW h1)
  ·
    rw [hι, hεᵢ, iotaHom_comp]
    have h1 : iotaHom hW ε₀ = Spec.map (rho r) ≫ s := section_fromSpec s r W hW hsW
    rw [h1, ← Category.assoc, ← Spec.map_comp]
    congr 2
    ext y
    change e.symm ((rho r).hom y) = algebraMap R Rᵢ y
    rw [← he]
    exact e.symm_apply_apply _
  ·
    intro C _ _ J hJ P ψ₀ hψ₀
    have hrange : Set.range P.1 ⊆ Set.range hW.fromSpec := by
      rw [← range_comp_quotient_eq J hJ P.1, ← hψ₀, hι]
      exact range_iotaHom_subset hW _
    obtain ⟨φr, hφr⟩ := exists_iotaHom_eq hW P.1 hrange

    have hcomm : φr.comp (algebraMap Rᵢ B₀) = algebraMap Rᵢ C := by
      apply hloc
      have h1 := iotaHom_comp_structure f r W hW eW φr
      rw [hφr, P.2] at h1
      have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)

      ext y
      have h3 := congrArg (fun h : R →+* C => h y) h2
      simp only [CommRingCat.hom_ofHom, CommRingCat.hom_comp, RingHom.comp_apply, toHom_hom] at h3
      show φr (φ₀ (e (algebraMap R Rᵢ y))) = algebraMap Rᵢ C (algebraMap R Rᵢ y)
      rw [he, h3]
    let φ : B₀ →ₐ[Rᵢ] C :=
      { toRingHom := φr
        commutes' := fun y => congrArg (fun h : Rᵢ →+* C => h y) hcomm }
    refine ⟨φ, Subtype.ext ?_⟩
    rw [hι]
    exact hφr

end Package

section Main

variable {R : Type u} [CommRing R] {A : Scheme.{u}}

local notation "SR" => Spec (CommRingCat.of R)

theorem main {f : A ⟶ SR} (hf : Smooth f) (s : SR ⟶ A) (hs : s ≫ f = 𝟙 _) :
    ∃ (n : ℕ) (a : Fin n → R), Ideal.span (Set.range a) = ⊤ ∧
      ∀ (i : Fin n) (Rᵢ : Type u) [CommRing Rᵢ] [Algebra R Rᵢ] [IsLocalization.Away (a i) Rᵢ],
        ∃ (g : ℕ) (B : Type u) (_ : CommRing B) (_ : Algebra Rᵢ B) (_ : Algebra.FormallySmooth Rᵢ B)
          (ε : B →ₐ[Rᵢ] Rᵢ) (x : Fin g → B)
          (ι : ∀ (C : Type u) [CommRing C] [Algebra Rᵢ C],
            (B →ₐ[Rᵢ] C) →
              SchemeHomOver (Spec.map (CommRingCat.ofHom ((algebraMap Rᵢ C).comp (algebraMap R Rᵢ)))) f),
          (∀ j, ε (x j) = 0) ∧
          (RingHom.ker ε ≤ Ideal.span (Set.range x) ⊔ RingHom.ker ε ^ 2) ∧
          (∀ c : Fin g → Rᵢ, (∑ j, c j • x j) ∈ RingHom.ker ε ^ 2 → c = 0) ∧
          (∀ (C C' : Type u) [CommRing C] [Algebra Rᵢ C] [CommRing C'] [Algebra Rᵢ C']
            (ψ : C →ₐ[Rᵢ] C') (φ : B →ₐ[Rᵢ] C),
              (ι C' (ψ.comp φ)).1 = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ (ι C φ).1) ∧
          (∀ (C : Type u) [CommRing C] [Algebra Rᵢ C], Function.Injective (ι C)) ∧
          ((ι Rᵢ ε).1 = Spec.map (CommRingCat.ofHom (algebraMap R Rᵢ)) ≫ s) ∧
          (∀ (C : Type u) [CommRing C] [Algebra Rᵢ C] (J : Ideal C), IsNilpotent J →
            ∀ (P : SchemeHomOver (Spec.map (CommRingCat.ofHom ((algebraMap Rᵢ C).comp (algebraMap R Rᵢ)))) f)
              (φ₀ : B →ₐ[Rᵢ] C ⧸ J),
              (ι (C ⧸ J) φ₀).1 = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ P.1 →
                ∃ φ : B →ₐ[Rᵢ] C, ι C φ = P) := by
  classical
  haveI := hf

  have H := fun p : SR => exists_chart f s hs p
  choose r W hW eW hpr hsW hstd using H

  let aR : SR → R := fun p => (Scheme.ΓSpecIso (CommRingCat.of R)).hom (r p)
  have hspan : Ideal.span (Set.range aR) = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    let p : SR := (⟨m, hm.isPrime⟩ : PrimeSpectrum R)
    have h1 : aR p ∈ m := hle (Ideal.subset_span ⟨p, rfl⟩)
    have h2 := hpr p
    rw [basicOpen_eq_of_affine'] at h2
    exact h2 h1

  obtain ⟨T, hT, h1T⟩ :=
    Submodule.mem_span_finite_of_mem_span ((Ideal.eq_top_iff_one _).mp hspan)
  have hTmem : ∀ i : Fin T.card, ∃ p, aR p = (T.equivFin.symm i : R) := fun i =>
    hT (T.equivFin.symm i).2
  choose π hπ using hTmem
  refine ⟨T.card, fun i => aR (π i), ?_, ?_⟩
  · rw [Ideal.eq_top_iff_one]
    refine Ideal.span_mono ?_ h1T
    intro t ht
    exact ⟨T.equivFin ⟨t, ht⟩, by simp [hπ]⟩
  · intro i Rᵢ _ _ _
    exact chart_package f s hs (r (π i)) (W (π i)) (hW _) (eW _) (hsW _) (hstd _) Rᵢ

end Main

end SmoothChartOfSectionP3
p2m_reactivate "P2MW.S_AlgebraicGeometry_Smooth_exists_formallySmooth_chart_of_section.SmoothChartOfSectionP3"

open SmoothChartOfSectionP3 in
theorem solution
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (hf : Smooth f)
    (s : Spec (CommRingCat.of R) ⟶ A) (hs : s ≫ f = 𝟙 _) :
    ∃ (n : ℕ) (a : Fin n → R), Ideal.span (Set.range a) = ⊤ ∧
      ∀ (i : Fin n) (Rᵢ : Type u) [CommRing Rᵢ] [Algebra R Rᵢ] [IsLocalization.Away (a i) Rᵢ],
        ∃ (g : ℕ) (B : Type u) (_ : CommRing B) (_ : Algebra Rᵢ B) (_ : Algebra.FormallySmooth Rᵢ B)
          (ε : B →ₐ[Rᵢ] Rᵢ) (x : Fin g → B)
          (ι : ∀ (C : Type u) [CommRing C] [Algebra Rᵢ C],
            (B →ₐ[Rᵢ] C) →
              SchemeHomOver (Spec.map (CommRingCat.ofHom ((algebraMap Rᵢ C).comp (algebraMap R Rᵢ)))) f),

          (∀ j, ε (x j) = 0) ∧
          (RingHom.ker ε ≤ Ideal.span (Set.range x) ⊔ RingHom.ker ε ^ 2) ∧
          (∀ c : Fin g → Rᵢ, (∑ j, c j • x j) ∈ RingHom.ker ε ^ 2 → c = 0) ∧

          (∀ (C C' : Type u) [CommRing C] [Algebra Rᵢ C] [CommRing C'] [Algebra Rᵢ C']
            (ψ : C →ₐ[Rᵢ] C') (φ : B →ₐ[Rᵢ] C),
              (ι C' (ψ.comp φ)).1 = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ (ι C φ).1) ∧

          (∀ (C : Type u) [CommRing C] [Algebra Rᵢ C], Function.Injective (ι C)) ∧

          ((ι Rᵢ ε).1 = Spec.map (CommRingCat.ofHom (algebraMap R Rᵢ)) ≫ s) ∧

          (∀ (C : Type u) [CommRing C] [Algebra Rᵢ C] (J : Ideal C), IsNilpotent J →
            ∀ (P : SchemeHomOver (Spec.map (CommRingCat.ofHom ((algebraMap Rᵢ C).comp (algebraMap R Rᵢ)))) f)
              (φ₀ : B →ₐ[Rᵢ] C ⧸ J),
              (ι (C ⧸ J) φ₀).1 = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ P.1 →
                ∃ φ : B →ₐ[Rᵢ] C, ι C φ = P) :=
  main hf s hs

end S_AlgebraicGeometry_Smooth_exists_formallySmooth_chart_of_section
end P2MW
export P2MW.S_AlgebraicGeometry_Smooth_exists_formallySmooth_chart_of_section (solution)
