-- Prove2me | solution 1 for AlgebraicGeometry.exists_not_mem_forall_factorsThrough_iff_of_forall_atPrime_of_isProper
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/c45a68e4-3dbc-509d-a140-09a83e774c0c

import Mathlib
import Theorems.Thm_Ideal_exists_not_mem_forall_map_eq_map_of_isLocalization_of_map_eq_map_of_fg
import Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_map_ideal_ker_eq_of_forall_factorsThrough_iff_atPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_not_mem_forall_factorsThrough_iff_of_forall_atPrime_of_isProper

set_option autoImplicit false
set_option maxHeartbeats 3200000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace L4CS

noncomputable abbrev φ {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (V : A.affineOpens) :
    S →+* Γ(A, V.1) :=
  ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appLE ⊤ V.1 le_top).hom

theorem isNoetherianRing_chart {S : Type} [CommRing S] [IsNoetherianRing S] {A : Scheme.{0}}
    (f : A ⟶ Spec (CommRingCat.of S)) [LocallyOfFiniteType f] (V : A.affineOpens) : IsNoetherianRing Γ(A, V.1) := by
  have hft : RingHom.FiniteType (f.appLE ⊤ V.1 le_top).hom :=
    HasRingHomProperty.appLE @LocallyOfFiniteType f inferInstance ⟨⊤, isAffineOpen_top _⟩ V le_top
  haveI : IsNoetherianRing Γ(Spec (CommRingCat.of S), ⊤) :=
    isNoetherianRing_of_ringEquiv S (Scheme.ΓSpecIso (CommRingCat.of S)).symm.commRingCatIsoToRingEquiv
  letI := (f.appLE ⊤ V.1 le_top).hom.toAlgebra
  haveI : Algebra.FiniteType Γ(Spec (CommRingCat.of S), ⊤) Γ(A, V.1) := hft
  exact Algebra.FiniteType.isNoetherianRing Γ(Spec (CommRingCat.of S), ⊤) Γ(A, V.1)

theorem factorsThrough_iff {A Z : Scheme.{0}} (ι : Z ⟶ A) [IsClosedImmersion ι] (U : A.Opens)
    {T : Scheme.{0}} (ψ' : T ⟶ U) :
    (∃ k : T ⟶ Z, k ≫ ι = ψ' ≫ U.ι) ↔ ι.ker.comap U.ι ≤ ψ'.ker := by
  rw [← Scheme.IdealSheafData.le_map_iff_comap_le, Scheme.IdealSheafData.map_ker]
  constructor
  · rintro ⟨k, hk⟩
    rw [← hk]
    exact Scheme.Hom.le_ker_comp k ι
  · intro H
    exact ⟨IsClosedImmersion.lift ι (ψ' ≫ U.ι) H, IsClosedImmersion.lift_fac _ _ _⟩

end L4CS

open L4CS in
theorem solution
    {S : Type} [CommRing S] [IsNoetherianRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) [IsProper f]
    {Z₁ Z₂ : Scheme.{0}} (ι₁ : Z₁ ⟶ A) (ι₂ : Z₂ ⟶ A) [IsClosedImmersion ι₁] [IsClosedImmersion ι₂]
    (𝔭 : PrimeSpectrum S)
    (h : ∀ (R : Type) [CommRing R] (ψ : Spec (CommRingCat.of R) ⟶ A),
      (∃ t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of (Localization.AtPrime 𝔭.asIdeal)),
          t ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal))) = ψ ≫ f) →
      ((∃ ψ₁ : Spec (CommRingCat.of R) ⟶ Z₁, ψ₁ ≫ ι₁ = ψ) ↔ (∃ ψ₂ : Spec (CommRingCat.of R) ⟶ Z₂, ψ₂ ≫ ι₂ = ψ))) :
    ∃ g : S, g ∉ 𝔭.asIdeal ∧ ∀ (R : Type) [CommRing R] (ψ : Spec (CommRingCat.of R) ⟶ A),
      (∃ t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of (Localization.Away g)),
          t ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g))) = ψ ≫ f) →
      ((∃ ψ₁ : Spec (CommRingCat.of R) ⟶ Z₁, ψ₁ ≫ ι₁ = ψ) ↔ (∃ ψ₂ : Spec (CommRingCat.of R) ⟶ Z₂, ψ₂ ≫ ι₂ = ψ)) := by
  classical

  have hchart : ∀ V : A.affineOpens, ∃ gV : S, gV ∉ 𝔭.asIdeal ∧
      ∀ (B' : Type) [CommRing B'] [Algebra Γ(A, V.1) B'] [IsLocalization.Away (φ f V gV) B'],
        (ι₁.ker.ideal V).map (algebraMap Γ(A, V.1) B') = (ι₂.ker.ideal V).map (algebraMap Γ(A, V.1) B') := by
    intro V
    haveI := isNoetherianRing_chart f V
    have hloc := AlgebraicGeometry.IsClosedImmersion.map_ideal_ker_eq_of_forall_factorsThrough_iff_atPrime f ι₁ ι₂ 𝔭 h V
      (Localization (𝔭.asIdeal.primeCompl.map (φ f V).toMonoidHom))
    exact Ideal.exists_not_mem_forall_map_eq_map_of_isLocalization_of_map_eq_map_of_fg (φ f V) 𝔭.asIdeal
      (Localization (𝔭.asIdeal.primeCompl.map (φ f V).toMonoidHom)) _ _
      (IsNoetherian.noetherian _) (IsNoetherian.noetherian _) hloc
  choose gV hgV𝔭 hgV using hchart

  haveI : CompactSpace ↑A := QuasiCompact.compactSpace_of_compactSpace f
  let 𝒱 := A.affineCover.finiteSubcover
  let Vj : 𝒱.I₀ → A.affineOpens := fun j => ⟨(𝒱.f j).opensRange, isAffineOpen_opensRange (𝒱.f j)⟩
  let g : S := ∏ j, gV (Vj j)
  have hg𝔭 : g ∉ 𝔭.asIdeal := by
    intro hg
    obtain ⟨j, -, hj⟩ := Ideal.IsPrime.prod_mem_iff.mp hg
    exact hgV𝔭 (Vj j) hj
  refine ⟨g, hg𝔭, ?_⟩

  let s : Γ(Spec (CommRingCat.of S), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of S)).inv g
  let U : A.Opens := f ⁻¹ᵁ ((Spec (CommRingCat.of S)).basicOpen s)
  have hU : U = A.basicOpen (f.app ⊤ s) := Scheme.preimage_basicOpen f s
  let r : ∀ j, Γ(A, (Vj j).1) := fun j => φ f (Vj j) g
  have hr : ∀ j, (Vj j).1 ⊓ U = A.basicOpen (r j) := fun j => by
    rw [hU]
    exact (Scheme.basicOpen_res (X := A) (f.app ⊤ s) (homOfLE (le_top : (Vj j).1 ≤ f ⁻¹ᵁ ⊤)).op).symm
  let W : 𝒱.I₀ → U.toScheme.affineOpens := fun j => ⟨U.ι ⁻¹ᵁ (Vj j).1, by
    show IsAffineOpen (U.ι ⁻¹ᵁ (Vj j).1)
    rw [← U.ι.isAffineOpen_iff_of_isOpenImmersion, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_comm, hr]
    exact (Vj j).2.basicOpen (r j)⟩
  have hWcov : ⨆ j, (W j).1 = ⊤ := by
    change ⨆ j, U.ι ⁻¹ᵁ (Vj j).1 = ⊤
    rw [← Scheme.Hom.preimage_iSup]
    have : ⨆ j, (Vj j).1 = ⊤ := 𝒱.iSup_opensRange
    rw [this]
    rfl

  have hWimg : ∀ j, (⟨U.ι ''ᵁ (W j).1, (W j).2.image_of_isOpenImmersion U.ι⟩ : A.affineOpens) = A.affineBasicOpen (r j) := by
    intro j
    apply Subtype.ext
    change U.ι ''ᵁ (U.ι ⁻¹ᵁ (Vj j).1) = A.basicOpen (r j)
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm, hr]
  have hbasic : ∀ j, ι₁.ker.ideal (A.affineBasicOpen (r j)) = ι₂.ker.ideal (A.affineBasicOpen (r j)) := by
    intro j
    rw [← ι₁.ker.map_ideal_basicOpen, ← ι₂.ker.map_ideal_basicOpen]

    have inst := (Vj j).2.isLocalization_basicOpen (r j)
    let ρ : Γ(A, (Vj j).1) →+* Γ(A, A.basicOpen (r j)) := (A.presheaf.map (homOfLE (A.basicOpen_le (r j))).op).hom
    have hρ : algebraMap Γ(A, (Vj j).1) Γ(A, A.basicOpen (r j)) = ρ := rfl
    have hunit_r : IsUnit (ρ (r j)) := by rw [← hρ]; exact IsLocalization.Away.algebraMap_isUnit (r j)
    have hdvd : φ f (Vj j) (gV (Vj j)) ∣ r j := by
      change φ f (Vj j) (gV (Vj j)) ∣ φ f (Vj j) (∏ i, gV (Vj i))
      rw [map_prod]
      exact Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
    have hunit : IsUnit (ρ (φ f (Vj j) (gV (Vj j)))) := isUnit_of_dvd_unit (map_dvd ρ hdvd) hunit_r

    let Bv := Localization.Away (φ f (Vj j) (gV (Vj j)))
    have heq := hgV (Vj j) Bv
    let ℓ : Bv →+* Γ(A, A.basicOpen (r j)) := IsLocalization.Away.lift (φ f (Vj j) (gV (Vj j))) hunit
    have hℓ : ℓ.comp (algebraMap Γ(A, (Vj j).1) Bv) = ρ := IsLocalization.Away.lift_comp _ hunit
    change (ι₁.ker.ideal (Vj j)).map ρ = (ι₂.ker.ideal (Vj j)).map ρ
    rw [← hℓ, ← Ideal.map_map, ← Ideal.map_map, heq]
  have heqU : ι₁.ker.comap U.ι = ι₂.ker.comap U.ι := by
    refine Scheme.IdealSheafData.ext_of_iSup_eq_top W hWcov (fun j => ?_)
    rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
    have hb := hbasic j
    rw [← hWimg j] at hb
    rw [hb]

  intro R _ ψ ht
  obtain ⟨t, ht⟩ := ht
  have hrange : Set.range ψ.base ⊆ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    change ψ.base p ∈ f ⁻¹ᵁ ((Spec (CommRingCat.of S)).basicOpen s)
    change f.base (ψ.base p) ∈ (Spec (CommRingCat.of S)).basicOpen s
    have : f.base (ψ.base p) = (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))).base (t.base p) := by
      change (ψ ≫ f).base p = (t ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))).base p
      rw [ht]
    rw [this, basicOpen_eq_of_affine]
    have hmem : (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))).base (t.base p) ∈
        Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away g))) := ⟨t.base p, rfl⟩
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g] at hmem
    exact hmem
  let ψ' : Spec (CommRingCat.of R) ⟶ U := IsOpenImmersion.lift U.ι ψ hrange
  have hψ' : ψ' ≫ U.ι = ψ := IsOpenImmersion.lift_fac _ _ _
  rw [← hψ', factorsThrough_iff ι₁ U ψ', factorsThrough_iff ι₂ U ψ', heqU]

end S_AlgebraicGeometry_exists_not_mem_forall_factorsThrough_iff_of_forall_atPrime_of_isProper
end P2MW
export P2MW.S_AlgebraicGeometry_exists_not_mem_forall_factorsThrough_iff_of_forall_atPrime_of_isProper (solution)
