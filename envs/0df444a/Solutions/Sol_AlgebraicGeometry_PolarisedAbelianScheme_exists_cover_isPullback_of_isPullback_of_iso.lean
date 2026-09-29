-- Prove2me | solution 1 for AlgebraicGeometry.PolarisedAbelianScheme.exists_cover_isPullback_of_isPullback_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/24eff8f3-6f43-5e68-850e-78dd84db56f2

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

import Theorems.Thm_Ideal_exists_finset_span_eq_top_of_forall_prime_exists_not_mem
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackComp_hom_app_pullbackLocalSection
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_cover_isPullback_of_isPullback_of_iso

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem solution
    {g d n : ℕ} {S' : Type} [CommRing S'] (v w : PolarisedAbelianScheme g d n S')
    (h : PolarisedAbelianScheme.Iso v w) :
    ∃ (m : ℕ) (r : Fin m → S'), Ideal.span (Set.range r) = ⊤ ∧
      ∀ (j : Fin m) (wj : PolarisedAbelianScheme g d n (Localization.Away (r j))),
        PolarisedAbelianScheme.IsPullback (algebraMap S' (Localization.Away (r j))) w wj →
        PolarisedAbelianScheme.IsPullback (algebraMap S' (Localization.Away (r j))) v wj := by
  classical
  obtain ⟨e, he, hhom, hP, hloc⟩ := h
  have he' : e.inv ≫ v.f = w.f := by rw [← he, Iso.inv_hom_id_assoc]

  have hinv : ∀ {T : Scheme.{0}} (τ : T ⟶ Spec (CommRingCat.of S')) (a b : SchemeHomOver τ w.f),
      (w.L.mul τ a b).1 ≫ e.inv =
        (v.L.mul τ ⟨a.1 ≫ e.inv, by rw [Category.assoc, he']; exact a.2⟩
          ⟨b.1 ≫ e.inv, by rw [Category.assoc, he']; exact b.2⟩).1 := by
    intro T τ a b
    have h1 := hhom τ ⟨a.1 ≫ e.inv, by rw [Category.assoc, he']; exact a.2⟩ ⟨b.1 ≫ e.inv, by rw [Category.assoc, he']; exact b.2⟩
    have ha : (⟨(a.1 ≫ e.inv) ≫ e.hom, by rw [Category.assoc, he]; rw [Category.assoc, he']; exact a.2⟩ : SchemeHomOver τ w.f) = a :=
      Subtype.ext (by simp)
    have hb : (⟨(b.1 ≫ e.inv) ≫ e.hom, by rw [Category.assoc, he]; rw [Category.assoc, he']; exact b.2⟩ : SchemeHomOver τ w.f) = b :=
      Subtype.ext (by simp)
    rw [ha, hb] at h1
    rw [← h1, Category.assoc, Iso.hom_inv_id, Category.comp_id]

  have hcov : ∀ 𝔭 : PrimeSpectrum S', ∃ r : S', r ∉ 𝔭.asIdeal ∧ ∃ U : (Spec (CommRingCat.of S')).Opens,
      (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum S')) ⊆ (U : Set (Spec (CommRingCat.of S'))) ∧
      Nonempty ((Scheme.Modules.pullback (v.f ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback e.hom).obj w.pol) ≅
        (Scheme.Modules.pullback (v.f ⁻¹ᵁ U).ι).obj v.pol) := by
    intro 𝔭
    obtain ⟨U, h𝔭U, hU⟩ := hloc 𝔭
    obtain ⟨_, ⟨r, rfl⟩, hr𝔭, hrU⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open h𝔭U U.isOpen
    exact ⟨r, hr𝔭, U, hrU, hU⟩
  obtain ⟨m, r, hr, hpiece⟩ := Ideal.exists_finset_span_eq_top_of_forall_prime_exists_not_mem _ hcov
  choose U hrU hisoU using hpiece
  refine ⟨m, r, hr, fun j wj hw => ?_⟩
  obtain ⟨gA, hg, hhom', hP', ⟨polIso⟩⟩ := hw
  let φj := (hisoU j).some
  let Sj := Localization.Away (r j)
  let loc := Spec.map (CommRingCat.ofHom (algebraMap S' Sj))

  have hrange : Set.range (gA ≫ e.inv).base ⊆ ((v.f ⁻¹ᵁ U j).ι).opensRange := by
    rw [Scheme.Hom.coe_opensRange, Scheme.Opens.range_ι]
    rintro p ⟨q, rfl⟩
    show ((gA ≫ e.inv) ≫ v.f).base q ∈ (U j : Set _)
    rw [Category.assoc, he', hg.w]
    apply hrU j
    have : (Spec.map (CommRingCat.ofHom (algebraMap S' Sj))).base (wj.f.base q) ∈
        Set.range (PrimeSpectrum.comap (algebraMap S' Sj)) := ⟨wj.f.base q, rfl⟩
    rwa [PrimeSpectrum.localization_away_comap_range Sj (r j)] at this
  obtain ⟨k, hk⟩ : ∃ k : wj.A ⟶ ↑(v.f ⁻¹ᵁ U j), k ≫ (v.f ⁻¹ᵁ U j).ι = gA ≫ e.inv :=
    ⟨IsOpenImmersion.lift (v.f ⁻¹ᵁ U j).ι (gA ≫ e.inv) (by rwa [Scheme.Hom.coe_opensRange] at hrange),
      IsOpenImmersion.lift_fac _ _ _⟩
  have hgA : gA = k ≫ ((v.f ⁻¹ᵁ U j).ι ≫ e.hom) := by
    rw [← Category.assoc, hk, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  subst hgA

  have hk' : k ≫ (v.f ⁻¹ᵁ U j).ι = (k ≫ ((v.f ⁻¹ᵁ U j).ι ≫ e.hom)) ≫ e.inv := by simp
  refine ⟨k ≫ (v.f ⁻¹ᵁ U j).ι, ?_, ?_, ?_, ⟨?_⟩⟩
  ·
    rw [hk']
    exact IsPullback.of_iso hg (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      (by simp [he']) (by simp)
  ·
    intro T τ x y
    conv_lhs => rw [hk', ← Category.assoc, hhom' τ x y, hinv]
    congr 2 <;> exact Subtype.ext (by simp)
  ·
    intro i
    rw [hk', ← Category.assoc, hP' i, Category.assoc, ← hP i, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  ·
    exact ((Scheme.Modules.pullbackComp k (v.f ⁻¹ᵁ U j).ι).app v.pol).symm ≪≫
      (Scheme.Modules.pullback k).mapIso φj.symm ≪≫
      (Scheme.Modules.pullback k).mapIso ((Scheme.Modules.pullbackComp (v.f ⁻¹ᵁ U j).ι e.hom).app w.pol) ≪≫
      (Scheme.Modules.pullbackComp k ((v.f ⁻¹ᵁ U j).ι ≫ e.hom)).app w.pol ≪≫ polIso

end S_AlgebraicGeometry_PolarisedAbelianScheme_exists_cover_isPullback_of_isPullback_of_iso
end P2MW
export P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_cover_isPullback_of_isPullback_of_iso (solution)
