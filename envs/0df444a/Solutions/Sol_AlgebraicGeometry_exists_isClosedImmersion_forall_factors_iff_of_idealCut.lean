-- Prove2me | solution 1 for AlgebraicGeometry.exists_isClosedImmersion_forall_factors_iff_of_idealCut
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/66565d36-7e8e-574c-a135-a468c6e5a008

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_isClosedImmersion_forall_exists_comp_eq_iff_ideal_eq_bot
import Theorems.Thm_Ideal_exists_forall_iff_map_eq_bot_of_forall_away
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_isClosedImmersion_forall_factors_iff_of_idealCut

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry

namespace P2mWs30CS1

theorem ideal_eq_of_forall_map_eq_bot_iff {B : Type u} [CommRing B] (J₁ J₂ : Ideal B)
    (h : ∀ (A : Type u) [CommRing A] (φ : B →+* A), Ideal.map φ J₁ = ⊥ ↔ Ideal.map φ J₂ = ⊥) : J₁ = J₂ := by
  apply le_antisymm
  · have h2 : Ideal.map (Ideal.Quotient.mk J₂) J₂ = ⊥ := by
      rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
    have h1 := (h _ (Ideal.Quotient.mk J₂)).mpr h2
    rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker] at h1
    exact h1
  · have h1 : Ideal.map (Ideal.Quotient.mk J₁) J₁ = ⊥ := by
      rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
    have h2 := (h _ (Ideal.Quotient.mk J₁)).mp h1
    rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker] at h2
    exact h2

theorem specMap_ofHom_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] (φ : A →+* B) (χ : B →+* C) :
    Spec.map (CommRingCat.ofHom (χ.comp φ)) = Spec.map (CommRingCat.ofHom χ) ≫ Spec.map (CommRingCat.ofHom φ) := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

end P2mWs30CS1

open P2mWs30CS1 in
theorem solution
    (H : Scheme.{u})
    (Q : ∀ (A : Type u) [CommRing A], (Spec (CommRingCat.of A) ⟶ H) → Prop)

    (hQmap : ∀ (A A' : Type u) [CommRing A] [CommRing A'] (φ : A →+* A') (u : Spec (CommRingCat.of A) ⟶ H),
      Q A u → Q A' (Spec.map (CommRingCat.ofHom φ) ≫ u))

    (hQloc : ∀ (A : Type u) [CommRing A] (u : Spec (CommRingCat.of A) ⟶ H) (ι : Type u) (r : ι → A),
      Ideal.span (Set.range r) = ⊤ →
      (∀ i, Q (Localization.Away (r i))
        (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (r i)))) ≫ u)) → Q A u)

    (hQcut : ∀ (U : H.Opens) (hU : IsAffineOpen U) (B : Type u) [CommRing B]
      (e : Spec (CommRingCat.of B) ≅ (U : Scheme.{u})),
      ∃ J : Ideal B, ∀ (A : Type u) [CommRing A] (φ : B →+* A),
        Q A (Spec.map (CommRingCat.ofHom φ) ≫ e.hom ≫ U.ι) ↔ Ideal.map φ J = ⊥) :
    ∃ (C : Scheme.{u}) (ι : C ⟶ H), IsClosedImmersion ι ∧
      ∀ (A : Type u) [CommRing A] (u : Spec (CommRingCat.of A) ⟶ H),
        (∃ v : Spec (CommRingCat.of A) ⟶ C, v ≫ ι = u) ↔ Q A u := by
  classical

  have cut : ∀ (A : Type u) [CommRing A] (u : Spec (CommRingCat.of A) ⟶ H), ∃ I : Ideal A,
      ∀ (A' : Type u) [CommRing A'] (φ : A →+* A'), Q A' (Spec.map (CommRingCat.ofHom φ) ≫ u) ↔ Ideal.map φ I = ⊥ := by
    intro A _ u

    have hx : ∀ x : ↥(Spec (CommRingCat.of A)), ∃ (U : H.affineOpens) (r : A),
        x ∈ PrimeSpectrum.basicOpen r ∧ (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum A)) ⊆ u.base ⁻¹' (U : Set H) := by
      intro x
      obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
        H.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (u.base x)) isOpen_univ
      have hopen : IsOpen (u.base ⁻¹' (U : Set H)) := U.isOpen.preimage u.base.hom.continuous
      obtain ⟨_, ⟨r, rfl⟩, hxr, hrU⟩ :=
        PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (show x ∈ u.base ⁻¹' (U : Set H) from hxU) hopen
      exact ⟨⟨U, hU⟩, r, hxr, hrU⟩
    choose U r hxr hrU using hx

    have hspan : Ideal.span (Set.range r) = ⊤ := by
      rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff]
      exact top_le_iff.mp fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxr x⟩

    have hrange : ∀ x, Set.range (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (r x)))) ≫ u).base ⊆
        Set.range ((U x : H.Opens)).ι.base := by
      intro x
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      apply hrU x
      show (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (r x))))).base z ∈ PrimeSpectrum.basicOpen (r x)
      have := Set.ext_iff.mp (PrimeSpectrum.localization_away_comap_range (Localization.Away (r x)) (r x))
        ((Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (r x))))).base z)
      exact this.mp ⟨z, rfl⟩
    let g' : ∀ x, Spec (CommRingCat.of (Localization.Away (r x))) ⟶ ((U x : H.Opens) : Scheme.{u}) :=
      fun x => IsOpenImmersion.lift ((U x : H.Opens)).ι _ (hrange x)
    have hg' : ∀ x, g' x ≫ ((U x : H.Opens)).ι =
        Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (r x)))) ≫ u :=
      fun x => IsOpenImmersion.lift_fac _ _ _
    let e : ∀ x, Spec (CommRingCat.of Γ(H, (U x : H.Opens))) ≅ ((U x : H.Opens) : Scheme.{u}) :=
      fun x => (U x).2.isoSpec.symm
    let ψ : ∀ x, Γ(H, (U x : H.Opens)) →+* Localization.Away (r x) :=
      fun x => (Spec.preimage (g' x ≫ (U x).2.isoSpec.hom)).hom
    have hψ : ∀ x, Spec.map (CommRingCat.ofHom (ψ x)) ≫ (e x).hom ≫ ((U x : H.Opens)).ι =
        Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (r x)))) ≫ u := by
      intro x
      rw [← hg' x]
      change Spec.map (CommRingCat.ofHom (Spec.preimage (g' x ≫ (U x).2.isoSpec.hom)).hom) ≫ (U x).2.isoSpec.inv ≫ _ = _
      rw [CommRingCat.ofHom_hom, Spec.map_preimage, Category.assoc, Iso.hom_inv_id_assoc]

    have hJ : ∀ x, ∃ J : Ideal Γ(H, (U x : H.Opens)), ∀ (A' : Type u) [CommRing A'] (φ : Γ(H, (U x : H.Opens)) →+* A'),
        Q A' (Spec.map (CommRingCat.ofHom φ) ≫ (e x).hom ≫ ((U x : H.Opens)).ι) ↔ Ideal.map φ J = ⊥ :=
      fun x => hQcut (U x) (U x).2 _ (e x)
    choose J hJ using hJ
    refine Ideal.exists_forall_iff_map_eq_bot_of_forall_away A (fun A' _ φ => Q A' (Spec.map (CommRingCat.ofHom φ) ≫ u)) ?_ ?_ _ r hspan
      (fun x => Ideal.map (ψ x) (J x)) ?_
    ·
      intro A' A'' _ _ χ φ h
      beta_reduce at h ⊢
      rw [specMap_ofHom_comp, Category.assoc]
      exact hQmap A' A'' χ _ h
    ·
      intro A' _ φ κ s hs hk
      refine hQloc A' _ κ s hs fun k => ?_
      have := hk k
      beta_reduce at this
      rwa [specMap_ofHom_comp, Category.assoc] at this
    ·
      intro x A' _ χ
      beta_reduce
      rw [specMap_ofHom_comp, Category.assoc, ← hψ x, ← Category.assoc, ← specMap_ofHom_comp, hJ x, Ideal.map_map]

  choose I hI using cut
  have hIbc : ∀ (R R' : Type u) [CommRing R] [CommRing R'] (ψ : R →+* R') (s : Spec (CommRingCat.of R) ⟶ H),
      I R' (Spec.map (CommRingCat.ofHom ψ) ≫ s) = (I R s).map ψ := by
    intro R R' _ _ ψ s
    apply ideal_eq_of_forall_map_eq_bot_iff
    intro A' _ φ
    rw [← hI R' (Spec.map (CommRingCat.ofHom ψ) ≫ s) A' φ, Ideal.map_map, ← hI R s A' (φ.comp ψ),
      specMap_ofHom_comp, Category.assoc]
  obtain ⟨Z, ι, hι, hZ⟩ :=
    AlgebraicGeometry.Scheme.exists_isClosedImmersion_forall_exists_comp_eq_iff_ideal_eq_bot H I hIbc
  refine ⟨Z, ι, hι, fun A _ u => (hZ A u).trans ?_⟩
  have := hI A u A (RingHom.id A)
  rw [Ideal.map_id, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp] at this
  exact this.symm

end S_AlgebraicGeometry_exists_isClosedImmersion_forall_factors_iff_of_idealCut
end P2MW
export P2MW.S_AlgebraicGeometry_exists_isClosedImmersion_forall_factors_iff_of_idealCut (solution)
