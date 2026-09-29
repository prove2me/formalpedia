-- Prove2me | solution 1 for AdicCompletion.exists_isRegular_pair_of_isIntegrallyClosed_of_ringKrullDim_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/6c213d97-d4d9-5300-b598-d699802cde6c

import Mathlib
import Definitions.Def_AdicCompletionGaloisAction
import Definitions.Def_AdicCompletionRingFunctoriality
import Definitions.Def_AdicCompletionLocalRing
import Theorems.Thm_IsIntegrallyClosed_exists_isRegular_pair_of_two_le_ringKrullDim
import Theorems.Thm_IsRegularLocalRing_isDomain
import Theorems.Thm_IsRegularLocalRing_uniqueFactorizationMonoid_of_ringKrullDim_le_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AdicCompletion_exists_isRegular_pair_of_isIntegrallyClosed_of_ringKrullDim_eq_two

set_option autoImplicit false

open IsLocalRing
open scoped AdicCompletion.GaloisAction TensorProduct

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

theorem BDescN5.height_map_mk_eq_zero {O : Type} [CommRing O] {C : Type} [CommRing C] [Algebra O C] [Algebra.IsIntegral O C]
    (P : Ideal C) [P.IsPrime] :
    (P.map (Ideal.Quotient.mk ((P.under O).map (algebraMap O C)))).height = 0 := by
  classical
  set pC : Ideal C := (P.under O).map (algebraMap O C) with hpC
  have hpCP : pC ≤ P := by rw [hpC, Ideal.map_le_iff_le_comap]
  have hker : RingHom.ker (Ideal.Quotient.mk pC) ≤ P := by rw [Ideal.mk_ker]; exact hpCP
  haveI hPbar : (P.map (Ideal.Quotient.mk pC)).IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  rw [Ideal.height_eq_zero_iff, minimalPrimes_eq_minimals]
  refine ⟨hPbar, fun q hq hqle => ?_⟩
  haveI : q.IsPrime := hq
  let Q : Ideal C := q.comap (Ideal.Quotient.mk pC)
  haveI hQp : Q.IsPrime := Ideal.comap_isPrime _ _
  have hQP : Q ≤ P := by
    intro x hx
    have : Ideal.Quotient.mk pC x ∈ P.map (Ideal.Quotient.mk pC) := hqle hx
    rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at this
    obtain ⟨x', hx', hxx'⟩ := this
    rw [Ideal.Quotient.eq] at hxx'
    have : x' - (x' - x) ∈ P := P.sub_mem hx' (hpCP hxx')
    simpa using this
  have hpQ : pC ≤ Q := by
    intro x hx
    show Ideal.Quotient.mk pC x ∈ q
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]; exact q.zero_mem
  have hQO : Q.comap (algebraMap O C) = P.comap (algebraMap O C) := by
    apply le_antisymm (Ideal.comap_mono hQP)
    intro a ha
    rw [Ideal.mem_comap]
    exact hpQ (by rw [hpC]; exact Ideal.mem_map_of_mem _ ha)
  have hQeq : Q = P := by
    by_contra hne'
    have hlt : Q < P := lt_of_le_of_ne hQP hne'
    have := Ideal.IsIntegral.comap_lt_comap (R := O) hlt
    rw [hQO] at this
    exact lt_irrefl _ this
  intro z hz
  rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hz
  obtain ⟨x, hx, rfl⟩ := hz
  have : x ∈ Q := by rw [hQeq]; exact hx
  exact this

theorem solution {O : Type} [CommRing O] [IsRegularLocalRing O] (hdimO : ringKrullDim O = 2)
    {C : Type} [CommRing C] [IsDomain C] (hCic : IsIntegrallyClosed C) [Algebra O C] [Module.Finite O C] [FaithfulSMul O C]
    (𝔫 : Ideal C) [𝔫.IsMaximal] [𝔫.LiesOver (maximalIdeal O)] :
    ∃ a b : AdicCompletion 𝔫 C, RingTheory.Sequence.IsRegular (AdicCompletion 𝔫 C) [a, b] := by
  classical
  haveI : IsNoetherianRing C := IsNoetherianRing.of_finite O C
  haveI : IsIntegrallyClosed C := hCic
  haveI : IsDomain O := IsRegularLocalRing.isDomain O
  haveI : UniqueFactorizationMonoid O := IsRegularLocalRing.uniqueFactorizationMonoid_of_ringKrullDim_le_two O hdimO.le
  haveI : IsIntegrallyClosed O := inferInstance
  let S := Localization.AtPrime 𝔫
  haveI : IsNoetherianRing S := IsLocalization.isNoetherianRing 𝔫.primeCompl S inferInstance
  haveI : IsDomain S := IsLocalization.isDomain_of_le_nonZeroDivisors S (Ideal.primeCompl_le_nonZeroDivisors 𝔫)
  haveI : IsIntegrallyClosed S := isIntegrallyClosed_of_isLocalization S 𝔫.primeCompl (Ideal.primeCompl_le_nonZeroDivisors 𝔫)

  have hdimS : 2 ≤ ringKrullDim S := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height 𝔫 S]
    haveI : 𝔫.LiesOver (𝔫.under O) := ⟨rfl⟩
    have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (𝔫.under O) 𝔫
    rw [BDescN5.height_map_mk_eq_zero, add_zero] at h
    have h𝔫O : 𝔫.under O = maximalIdeal O := (Ideal.LiesOver.over (P := 𝔫) (p := maximalIdeal O)).symm
    rw [h𝔫O] at h
    rw [h, IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hdimO]

  have h𝔪0 : maximalIdeal O ≠ ⊥ := by
    intro h0
    have hf : IsField O := (IsLocalRing.isField_iff_maximalIdeal_eq).mpr h0
    have := ringKrullDim_eq_zero_of_isField hf
    rw [hdimO] at this
    exact absurd this (by decide)
  obtain ⟨o, ho, ho0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔪0
  have hinjOC : Function.Injective (algebraMap O C) := (faithfulSMul_iff_algebraMap_injective O C).mp inferInstance
  have hinjCS : Function.Injective (algebraMap C S) := IsLocalization.injective S (Ideal.primeCompl_le_nonZeroDivisors 𝔫)
  set t : S := algebraMap C S (algebraMap O C o) with ht
  have ht0 : t ≠ 0 := by
    intro h
    apply ho0
    apply hinjOC; apply hinjCS
    rw [map_zero, map_zero]; exact h
  have htm : t ∈ maximalIdeal S := by
    have h1 : algebraMap O C o ∈ 𝔫 := by
      rw [← Ideal.mem_comap]; show o ∈ 𝔫.under O
      rw [← Ideal.LiesOver.over (P := 𝔫) (p := maximalIdeal O)]; exact ho
    rw [ht]; exact (IsLocalization.AtPrime.to_map_mem_maximal_iff S 𝔫 _).mpr h1
  obtain ⟨b, hbm, hreg⟩ := IsIntegrallyClosed.exists_isRegular_pair_of_two_le_ringKrullDim hdimS t htm ht0

  let SH := AdicCompletion (maximalIdeal S) S
  have hw : RingTheory.Sequence.IsWeaklyRegular S [t, b] := hreg.toIsWeaklyRegular
  have hw1 : RingTheory.Sequence.IsWeaklyRegular (S ⊗[S] SH) [t, b] := hw.isWeaklyRegular_rTensor
  have hw2 : RingTheory.Sequence.IsWeaklyRegular SH [t, b] :=
    (LinearEquiv.isWeaklyRegular_congr (TensorProduct.lid S SH) [t, b]).mp hw1
  have hw3 : RingTheory.Sequence.IsWeaklyRegular SH ([t, b].map (algebraMap S SH)) :=
    (RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff (R := S) (S := SH) (M := SH) [t, b]).mpr hw2
  have hmemS : ∀ x ∈ maximalIdeal S, algebraMap S SH x ∈ maximalIdeal SH := by
    intro x hx; rw [AdicCompletion.maximalIdeal_eq_map]; exact Ideal.mem_map_of_mem _ hx
  have hregS : RingTheory.Sequence.IsRegular SH [algebraMap S SH t, algebraMap S SH b] := by
    refine ⟨by simpa using hw3, ?_⟩
    intro htop
    have hle : Ideal.ofList [algebraMap S SH t, algebraMap S SH b] ≤ maximalIdeal SH := by
      rw [Ideal.ofList, Ideal.span_le]
      rintro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq] at hx
      rcases hx with rfl | rfl
      · exact hmemS t htm
      · exact hmemS b hbm
    have : (Ideal.ofList [algebraMap S SH t, algebraMap S SH b] • ⊤ : Ideal SH) ≤ maximalIdeal SH := by
      rw [Ideal.smul_eq_mul, Ideal.mul_top]; exact hle
    rw [← htop] at this
    exact (maximalIdeal.isMaximal SH).ne_top (top_le_iff.mp this)

  let e := BDescN6.adicEquiv 𝔫 S
  refine ⟨e.symm (algebraMap S SH t), e.symm (algebraMap S SH b), ?_⟩
  refine (AddEquiv.isRegular_congr (e := (e.symm : SH ≃+* AdicCompletion 𝔫 C).toAddEquiv) ?_).mp hregS
  refine List.Forall₂.cons (fun x => ?_) (List.Forall₂.cons (fun x => ?_) List.Forall₂.nil)
  · show e.symm (algebraMap S SH t * x) = e.symm (algebraMap S SH t) * e.symm x
    exact map_mul _ _ _
  · show e.symm (algebraMap S SH b * x) = e.symm (algebraMap S SH b) * e.symm x
    exact map_mul _ _ _

end S_AdicCompletion_exists_isRegular_pair_of_isIntegrallyClosed_of_ringKrullDim_eq_two
end P2MW
export P2MW.S_AdicCompletion_exists_isRegular_pair_of_isIntegrallyClosed_of_ringKrullDim_eq_two (solution)
