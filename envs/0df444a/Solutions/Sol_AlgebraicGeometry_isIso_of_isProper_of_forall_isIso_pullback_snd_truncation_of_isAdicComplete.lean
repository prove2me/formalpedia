-- Prove2me | solution 1 for AlgebraicGeometry.isIso_of_isProper_of_forall_isIso_pullback_snd_truncation_of_isAdicComplete
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/5c709952-19a9-50fc-b6a0-c7da0d12ff61

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Theorems.Thm_AlgebraicGeometry_isIso_of_isFinite_of_forall_isIso_pullback_snd_truncation_of_isAdicComplete
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isIso_of_isProper_of_forall_isIso_pullback_snd_truncation_of_isAdicComplete

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    {Γ X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] (h : Γ ⟶ X) [IsProper h]

    (sR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ Spec (CommRingCat.of R))
    (hsR : ∀ n : ℕ, sR n = Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I ^ (n + 1)))))
    (hn : ∀ n : ℕ, IsIso (Limits.pullback.snd h (Limits.pullback.fst f (sR n)))) :
    IsIso h := by
  classical

  haveI : IsProper (h ≫ f) := inferInstance
  haveI : CompactSpace ↥Γ := QuasiCompact.compactSpace_of_compactSpace (h ≫ f)
  haveI : IsIso (pullback.snd h (pullback.fst f (sR 0))) := hn 0

  have hinj : ∀ γ₁ γ₂ : Γ, h γ₁ = h γ₂ → f (h γ₁) ∈ Set.range (sR 0) → γ₁ = γ₂ := by
    intro γ₁ γ₂ he hmem
    obtain ⟨t, ht⟩ := hmem
    obtain ⟨y₀, hy₀1, hy₀2⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := sR 0) (h γ₁) t ht.symm
    obtain ⟨z₁, hz₁1, hz₁2⟩ :=
      Scheme.Pullback.exists_preimage_pullback (f := h) (g := pullback.fst f (sR 0)) γ₁ y₀ hy₀1.symm
    obtain ⟨z₂, hz₂1, hz₂2⟩ :=
      Scheme.Pullback.exists_preimage_pullback (f := h) (g := pullback.fst f (sR 0)) γ₂ y₀ (he.symm.trans hy₀1.symm)
    have hz : z₁ = z₂ :=
      (pullback.snd h (pullback.fst f (sR 0))).isOpenEmbedding.injective (hz₁2.trans hz₂2.symm)
    rw [← hz₁1, ← hz₂1, hz]

  have hqf : ∀ γ : Γ, f (h γ) ∈ Set.range (sR 0) → h.QuasiFiniteAt γ := by
    intro γ hγ
    rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber]
    haveI hsub : Subsingleton ↥(h.fiber (h γ)) := by
      refine ⟨fun a b => (h.fiberHomeo (h γ)).injective (Subtype.ext ?_)⟩
      have ha : h ((h.fiberHomeo (h γ)) a).1 = h γ := ((h.fiberHomeo (h γ)) a).2
      have hb : h ((h.fiberHomeo (h γ)) b).1 = h γ := ((h.fiberHomeo (h γ)) b).2
      exact hinj _ _ (ha.trans hb.symm) (by rw [ha]; exact hγ)
    rw [Subsingleton.eq_univ_of_nonempty (Set.singleton_nonempty _)]
    exact isOpen_univ

  have hclosed : ∀ γ : Γ, IsClosed ({γ} : Set Γ) → f (h γ) ∈ Set.range (sR 0) := by
    intro γ hγ
    have hc : IsClosed ({(h ≫ f) γ} : Set ↥(Spec (CommRingCat.of R))) := by
      rw [← Set.image_singleton]
      exact (h ≫ f).isClosedMap _ hγ
    have hc' : ((h ≫ f) γ).asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp hc
    have hI : I ≤ ((h ≫ f) γ).asIdeal :=
      (IsAdicComplete.le_jacobson_bot I).trans (sInf_le ⟨bot_le, hc'⟩)
    rw [Scheme.Hom.comp_apply] at hI
    rw [hsR 0]
    have hle : I ^ (0 + 1) ≤ (f (h γ)).asIdeal := by rw [zero_add, pow_one]; exact hI
    refine ⟨⟨Ideal.map (Ideal.Quotient.mk (I ^ (0 + 1))) (f (h γ)).asIdeal, ?_⟩, ?_⟩
    · exact Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
    · apply PrimeSpectrum.ext
      rw [Spec.map_apply]
      change Ideal.comap (algebraMap R (R ⧸ I ^ (0 + 1))) (Ideal.map (Ideal.Quotient.mk (I ^ (0 + 1))) (f (h γ)).asIdeal) =
        (f (h γ)).asIdeal
      rw [Ideal.Quotient.algebraMap_eq, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
        ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
      exact sup_eq_left.mpr hle

  have hlocus : h.quasiFiniteLocus = ⊤ := by
    by_contra hne
    have hne' : ((h.quasiFiniteLocus : Set Γ)ᶜ).Nonempty := by
      rw [Set.nonempty_compl]
      intro htop
      exact hne (TopologicalSpace.Opens.ext htop)
    obtain ⟨γ, hγ, hγc⟩ := IsClosed.exists_closed_singleton h.quasiFiniteLocus.2.isClosed_compl hne'
    exact hγ (hqf γ (hclosed γ hγc))
  haveI : LocallyQuasiFinite h := (Scheme.Hom.quasiFiniteLocus_eq_top_iff h).mp hlocus
  haveI : IsFinite h := IsFinite.of_isProper_of_locallyQuasiFinite h
  exact AlgebraicGeometry.isIso_of_isFinite_of_forall_isIso_pullback_snd_truncation_of_isAdicComplete
    R I f h sR hsR hn

end S_AlgebraicGeometry_isIso_of_isProper_of_forall_isIso_pullback_snd_truncation_of_isAdicComplete
end P2MW
export P2MW.S_AlgebraicGeometry_isIso_of_isProper_of_forall_isIso_pullback_snd_truncation_of_isAdicComplete (solution)
