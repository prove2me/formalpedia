-- Prove2me | solution 1 for AdicCompletion.isLocalRing_and_ringKrullDim_le_two_of_liesOver
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/523502a2-ff83-5a89-a6bc-db0dbf988857

import Mathlib
import Definitions.Def_AdicCompletionGaloisAction
import Definitions.Def_AdicCompletionRingFunctoriality
import Definitions.Def_AdicCompletionLocalRing
import Theorems.Thm_IsLocalRing_ringKrullDim_adicCompletion_maximalIdeal_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AdicCompletion_isLocalRing_and_ringKrullDim_le_two_of_liesOver

set_option autoImplicit false

open IsLocalRing
open scoped AdicCompletion.GaloisAction

namespace BDescN6

theorem map_le {C : Type} [CommRing C] (𝔫 : Ideal C) [𝔫.IsMaximal]
    (S : Type) [CommRing S] [IsLocalRing S] [Algebra C S] [IsLocalization.AtPrime S 𝔫] :
    𝔫.map (Algebra.ofId C S) ≤ maximalIdeal S := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal 𝔫 S]
  exact le_of_eq rfl

theorem levelMap_bijective {C : Type} [CommRing C] (𝔫 : Ideal C) [𝔫.IsMaximal]
    (S : Type) [CommRing S] [IsLocalRing S] [Algebra C S] [IsLocalization.AtPrime S 𝔫] (n : ℕ) :
    Function.Bijective (AdicCompletion.levelMapₐ 𝔫 (maximalIdeal S) (Algebra.ofId C S) (map_le 𝔫 S) n) := by
  classical
  have hmS : maximalIdeal S ^ n = (𝔫 ^ n).map (algebraMap C S) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal 𝔫 S, Ideal.map_pow]
  constructor
  ·
    intro x y hxy
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [AdicCompletion.levelMapₐ_mk, AdicCompletion.levelMapₐ_mk, Ideal.Quotient.eq, Algebra.ofId_apply, Algebra.ofId_apply,
      ← map_sub, hmS, IsLocalization.mem_map_algebraMap_iff 𝔫.primeCompl] at hxy
    obtain ⟨⟨⟨a, ha⟩, ⟨s, hs⟩⟩, h⟩ := hxy
    simp only at h

    rw [← map_mul] at h
    obtain ⟨⟨t, ht⟩, ht'⟩ := (IsLocalization.eq_iff_exists 𝔫.primeCompl S).mp h
    simp only at ht'

    rw [Ideal.Quotient.eq]
    have hmem : t * s * (x - y) ∈ 𝔫 ^ n := by
      have : t * ((x - y) * s) ∈ 𝔫 ^ n := by rw [ht']; exact Ideal.mul_mem_left _ _ ha
      have heq : t * s * (x - y) = t * ((x - y) * s) := by ring
      rw [heq]; exact this
    have hu : IsUnit (Ideal.Quotient.mk (𝔫 ^ n) (t * s)) := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; rw [pow_zero, Ideal.one_eq_top]; exact isUnit_of_subsingleton _
      · exact Ideal.Quotient.isUnit_mk_pow_of_notMem (I := 𝔫) (fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim ht hs)
    have h0 : Ideal.Quotient.mk (𝔫 ^ n) (t * s) * Ideal.Quotient.mk (𝔫 ^ n) (x - y) = 0 := by
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]; exact hmem
    have : Ideal.Quotient.mk (𝔫 ^ n) (x - y) = 0 := (hu.mul_right_eq_zero).mp h0
    exact Ideal.Quotient.eq_zero_iff_mem.mp this
  ·
    intro z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨⟨a, ⟨s, hs⟩⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔫.primeCompl z

    have hu : IsUnit (Ideal.Quotient.mk (𝔫 ^ n) s) := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; rw [pow_zero, Ideal.one_eq_top]; exact isUnit_of_subsingleton _
      · exact Ideal.Quotient.isUnit_mk_pow_of_notMem (I := 𝔫) hs
    obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective ((hu.unit⁻¹ : (C ⧸ 𝔫 ^ n)ˣ) : C ⧸ 𝔫 ^ n)
    have hst : s * t - 1 ∈ 𝔫 ^ n := by
      rw [← Ideal.Quotient.eq, map_mul, ht, map_one]; exact hu.mul_val_inv
    refine ⟨Ideal.Quotient.mk (𝔫 ^ n) (a * t), ?_⟩
    rw [AdicCompletion.levelMapₐ_mk, Algebra.ofId_apply, Ideal.Quotient.eq, hmS]

    have hsp : IsLocalization.mk' S a ⟨s, hs⟩ * algebraMap C S s = algebraMap C S a := IsLocalization.mk'_spec S a ⟨s, hs⟩
    have : algebraMap C S (a * t) - IsLocalization.mk' S a ⟨s, hs⟩ =
        IsLocalization.mk' S a ⟨s, hs⟩ * algebraMap C S (s * t - 1) := by
      rw [map_sub, map_one, map_mul, map_mul, ← hsp]; ring
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hst)

noncomputable def adicEquiv {C : Type} [CommRing C] (𝔫 : Ideal C) [𝔫.IsMaximal]
    (S : Type) [CommRing S] [IsLocalRing S] [Algebra C S] [IsLocalization.AtPrime S 𝔫] :
    AdicCompletion 𝔫 C ≃ₐ[C] AdicCompletion (maximalIdeal S) S :=
  AdicCompletion.mapAlgEquivOfBijective 𝔫 (maximalIdeal S) (Algebra.ofId C S) (map_le 𝔫 S) (levelMap_bijective 𝔫 S)

end BDescN6

theorem solution {O : Type} [CommRing O] [IsNoetherianRing O] [IsLocalRing O] (hdimO : ringKrullDim O = 2)
    {C : Type} [CommRing C] [Algebra O C] [Module.Finite O C]
    (𝔫 : Ideal C) [𝔫.IsMaximal] [𝔫.LiesOver (maximalIdeal O)] :
    IsLocalRing (AdicCompletion 𝔫 C) ∧ ringKrullDim (AdicCompletion 𝔫 C) ≤ (2 : WithBot ℕ∞) := by
  classical
  haveI : IsNoetherianRing C := IsNoetherianRing.of_finite O C
  let S := Localization.AtPrime 𝔫
  haveI : IsNoetherianRing S := IsLocalization.isNoetherianRing 𝔫.primeCompl S inferInstance
  let e := BDescN6.adicEquiv 𝔫 S
  have hloc : IsLocalRing (AdicCompletion (maximalIdeal S) S) := inferInstance
  haveI : Nontrivial (AdicCompletion 𝔫 C) := e.symm.injective.nontrivial
  refine ⟨IsLocalRing.of_surjective' (e.symm : AdicCompletion (maximalIdeal S) S →+* AdicCompletion 𝔫 C) e.symm.surjective, ?_⟩
  rw [ringKrullDim_eq_of_ringEquiv e.toRingEquiv, IsLocalRing.ringKrullDim_adicCompletion_maximalIdeal_eq S,
    IsLocalization.AtPrime.ringKrullDim_eq_height 𝔫 S]

  haveI : 𝔫.LiesOver (𝔫.under O) := ⟨rfl⟩
  have hle := Ideal.height_le_height_add_of_liesOver (𝔫.under O) 𝔫
  have hfib : (𝔫.map (Ideal.Quotient.mk ((𝔫.under O).map (algebraMap O C)))).height = 0 := by
    set pC : Ideal C := (𝔫.under O).map (algebraMap O C) with hpC
    have hpCP : pC ≤ 𝔫 := by rw [hpC, Ideal.map_le_iff_le_comap]
    have hker : RingHom.ker (Ideal.Quotient.mk pC) ≤ 𝔫 := by rw [Ideal.mk_ker]; exact hpCP
    haveI hPbar : (𝔫.map (Ideal.Quotient.mk pC)).IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
    rw [Ideal.height_eq_zero_iff, minimalPrimes_eq_minimals]
    refine ⟨hPbar, fun q hq hqle => ?_⟩
    haveI : q.IsPrime := hq
    let Q : Ideal C := q.comap (Ideal.Quotient.mk pC)
    haveI hQp : Q.IsPrime := Ideal.comap_isPrime _ _
    have hQP : Q ≤ 𝔫 := by
      intro x hx
      have : Ideal.Quotient.mk pC x ∈ 𝔫.map (Ideal.Quotient.mk pC) := hqle hx
      rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at this
      obtain ⟨x', hx', hxx'⟩ := this
      rw [Ideal.Quotient.eq] at hxx'
      have : x' - (x' - x) ∈ 𝔫 := 𝔫.sub_mem hx' (hpCP hxx')
      simpa using this
    have hpQ : pC ≤ Q := by
      intro x hx
      show Ideal.Quotient.mk pC x ∈ q
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]; exact q.zero_mem
    have hQO : Q.comap (algebraMap O C) = 𝔫.comap (algebraMap O C) := by
      apply le_antisymm (Ideal.comap_mono hQP)
      intro a ha
      rw [Ideal.mem_comap]
      exact hpQ (by rw [hpC]; exact Ideal.mem_map_of_mem _ ha)
    have hQeq : Q = 𝔫 := by
      by_contra hne'
      have hlt : Q < 𝔫 := lt_of_le_of_ne hQP hne'
      have := Ideal.IsIntegral.comap_lt_comap (R := O) hlt
      rw [hQO] at this
      exact lt_irrefl _ this
    intro z hz
    rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    have : x ∈ Q := by rw [hQeq]; exact hx
    exact this
  rw [hfib, add_zero] at hle
  have h𝔫O : 𝔫.under O = maximalIdeal O := (Ideal.LiesOver.over (P := 𝔫) (p := maximalIdeal O)).symm
  rw [h𝔫O] at hle
  have hO := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := O)
  rw [hdimO] at hO
  have h2 : ((maximalIdeal O).height : WithBot ℕ∞) ≤ ((2 : ℕ∞) : WithBot ℕ∞) := by rw [hO]; exact le_rfl
  have h3 : (maximalIdeal O).height ≤ 2 := WithBot.coe_le_coe.mp h2
  exact (WithBot.coe_le_coe.mpr (hle.trans h3) : ((𝔫.height : ℕ∞) : WithBot ℕ∞) ≤ ((2 : ℕ∞) : WithBot ℕ∞))

end S_AdicCompletion_isLocalRing_and_ringKrullDim_le_two_of_liesOver
end P2MW
export P2MW.S_AdicCompletion_isLocalRing_and_ringKrullDim_le_two_of_liesOver (solution)
