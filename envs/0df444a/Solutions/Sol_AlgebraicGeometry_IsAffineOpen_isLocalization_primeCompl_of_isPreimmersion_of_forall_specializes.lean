-- Prove2me | solution 1 for AlgebraicGeometry.IsAffineOpen.isLocalization_primeCompl_of_isPreimmersion_of_forall_specializes
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/13d9cf93-0f97-5eae-ab9f-ea1b799f395b

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_IsAffineOpen_isLocalization_primeCompl_of_isPreimmersion_of_forall_specializes

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {X : Scheme.{u}} [IsReduced X] {V : X.Opens} (hV : IsAffineOpen V)
    (x : X) (hxV : x ∈ V) (hmax : ∀ y : X, y ⤳ x → y = x)
    (F : Type u) [Field F] (φ : Spec (CommRingCat.of F) ⟶ X) [IsPreimmersion φ]
    (hφx : φ.base (IsLocalRing.closedPoint F) = x)
    [Algebra Γ(X, V) F]
    (hφ : Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) F)) ≫ hV.fromSpec = φ) :
    IsLocalization (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl F := by
  classical

  have hpt : hV.fromSpec.base ((Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) F))).base (IsLocalRing.closedPoint F)) = x := by
    rw [← hφx, ← hφ]; rfl
  have h𝔭 : hV.primeIdealOf ⟨x, hxV⟩ =
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) F))).base (IsLocalRing.closedPoint F) := by
    apply hV.fromSpec.isOpenEmbedding.injective
    rw [hpt]
    exact hV.fromSpec_primeIdealOf ⟨x, hxV⟩
  have hmem : ∀ s : Γ(X, V), s ∈ (hV.primeIdealOf ⟨x, hxV⟩).asIdeal ↔ algebraMap Γ(X, V) F s = 0 := by
    intro s
    rw [h𝔭]
    change algebraMap Γ(X, V) F s ∈ IsLocalRing.maximalIdeal F ↔ _
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ne_zero, not_not]

  haveI : IsPreimmersion (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) F)) ≫ hV.fromSpec) := by
    rw [hφ]; infer_instance
  have hpre : IsPreimmersion (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) F))) :=
    IsPreimmersion.of_comp _ hV.fromSpec
  have hsos : (algebraMap Γ(X, V) F).SurjectiveOnStalks :=
    ((IsPreimmersion.SpecMap_iff _).mp hpre).2

  set 𝔭 := hV.primeIdealOf ⟨x, hxV⟩ with h𝔭def
  have hkill : ∀ d ∈ 𝔭.asIdeal, ∃ c : 𝔭.asIdeal.primeCompl, (c : Γ(X, V)) * d = 0 := by
    intro d hd
    set L := Localization.AtPrime 𝔭.asIdeal with hL

    have huniq : ∀ Q : Ideal L, Q.IsPrime → Q = IsLocalRing.maximalIdeal L := by
      intro Q hQ
      let q : PrimeSpectrum Γ(X, V) := ⟨Q.comap (algebraMap Γ(X, V) L), Ideal.IsPrime.comap _⟩
      have hq𝔭 : q ≤ 𝔭 := by
        intro s hs
        by_contra hs'
        have hu : IsUnit (algebraMap Γ(X, V) L s) := IsLocalization.map_units L (⟨s, hs'⟩ : 𝔭.asIdeal.primeCompl)
        exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem Q hs hu)
      have hfx : hV.fromSpec.base 𝔭 = x := hV.fromSpec_primeIdealOf ⟨x, hxV⟩
      have hspec : hV.fromSpec.base q ⤳ x := by
        rw [← hfx]
        exact ((PrimeSpectrum.le_iff_specializes q 𝔭).mp hq𝔭).map hV.fromSpec.base.hom.continuous
      have hqx : q = 𝔭 := by
        apply hV.fromSpec.isOpenEmbedding.injective
        rw [hmax _ hspec, hfx]
      apply le_antisymm (IsLocalRing.le_maximalIdeal hQ.ne_top)
      rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
      intro s hs
      have hs' : s ∈ q.asIdeal := by rw [hqx]; exact hs
      exact hs'

    have hmax0 : IsLocalRing.maximalIdeal L = ⊥ := by
      rw [eq_bot_iff]
      intro m hm
      have : m ∈ nilradical L := by
        rw [nilradical_eq_sInf, Submodule.mem_sInf]
        intro J hJ
        rw [huniq J hJ]; exact hm
      rw [mem_nilradical] at this
      exact this.eq_zero
    have : algebraMap Γ(X, V) L d = 0 := by
      rw [← Ideal.mem_bot, ← hmax0, ← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.mem_map_of_mem _ hd
    obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff 𝔭.asIdeal.primeCompl L d).mp this
    exact ⟨c, hc⟩

  constructor; constructor
  · rintro ⟨s, hs⟩
    rw [isUnit_iff_ne_zero]
    exact fun h => hs ((hmem s).mpr h)
  · intro z
    obtain ⟨a, r, c, hc, hr, e⟩ := (RingHom.surjectiveOnStalks_iff_forall_maximal'.mp hsos) ⊥ Ideal.bot_isMaximal z
    have hc0 : c ≠ 0 := fun h => hc (h ▸ Submodule.zero_mem _)
    have hr𝔭 : r ∉ 𝔭.asIdeal := fun h => hr (by rw [(hmem r).mp h]; exact Submodule.zero_mem _)
    refine ⟨(a, ⟨r, hr𝔭⟩), ?_⟩
    show z * algebraMap Γ(X, V) F r = algebraMap Γ(X, V) F a
    have e' : c * (algebraMap Γ(X, V) F r * z) = c * algebraMap Γ(X, V) F a := by rwa [mul_assoc] at e
    have e'' := mul_left_cancel₀ hc0 e'
    rw [mul_comm]; exact e''
  · intro a b hab
    have : a - b ∈ 𝔭.asIdeal := by rw [hmem, map_sub, hab, sub_self]
    obtain ⟨c, hc⟩ := hkill _ this
    refine ⟨c, ?_⟩
    rw [← sub_eq_zero, ← mul_sub, hc]

end S_AlgebraicGeometry_IsAffineOpen_isLocalization_primeCompl_of_isPreimmersion_of_forall_specializes
end P2MW
export P2MW.S_AlgebraicGeometry_IsAffineOpen_isLocalization_primeCompl_of_isPreimmersion_of_forall_specializes (solution)
