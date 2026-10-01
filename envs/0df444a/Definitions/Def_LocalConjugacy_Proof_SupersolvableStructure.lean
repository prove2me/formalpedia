-- Prove2me | Definitions.Def_LocalConjugacy_Proof_SupersolvableStructure
-- name    : LocalConjugacy_Proof_SupersolvableStructure
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-30T15:24:34.591282+00:00
-- url     : https://prove2.me/theorems/b40a834c-a613-4c2a-8992-03bb275c6a87
-- title:
--   Normal Hall factors in supersolvable groups
-- statement:
--   Structural existence proofs for cyclic normal subgroups, prime-order normal subgroups, and normal Hall subgroups of supersolvable groups. They supply the factors used by the profinite construction.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization interface.

import Mathlib
import Definitions.Def_LocalConjugacy_Groups
import Definitions.Def_LocalConjugacy_Cohomology
import Definitions.Def_LocalConjugacy_Examples
import Definitions.Def_LocalConjugacy_Proof_Definitions
import Definitions.Def_LocalConjugacy_Proof_Bridges
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_Heisenberg
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_HeisenbergStructure
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_HeisenbergSupersolvable
import Definitions.Def_LocalConjugacy_Proof_ConcreteGroups
import Definitions.Def_LocalConjugacy_Targets
import Definitions.Def_LocalConjugacy_Proof_Compactness
import Definitions.Def_LocalConjugacy_Proof_ProfiniteSylow
import Definitions.Def_LocalConjugacy_Proof_StructuralImages
import Definitions.Def_LocalConjugacy_Proof_FiniteAbelianCohomology
import Definitions.Def_LocalConjugacy_Proof_AbelianComplement
import Definitions.Def_LocalConjugacy_Proof_QuotientReduction
import Definitions.Def_LocalConjugacy_Proof_Cohomology
import Definitions.Def_LocalConjugacy_Proof_InvariantRestriction
import Definitions.Def_LocalConjugacy_Proof_CocycleActions
import Definitions.Def_LocalConjugacy_Proof_CoprimeCohomology
import Definitions.Def_LocalConjugacy_Proof_CocycleDescent
import Definitions.Def_LocalConjugacy_Proof_FiniteHall

/-! Supporting definitions and the structural proofs required by their types and values. -/

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy





/-- A nontrivial supersolvable group contains a nontrivial cyclic normal subgroup. -/
theorem supersolvable_exists_cyclic_normal {G : Type*} [Group G] [Nontrivial G]
    (hG : Supersolvable G) :
    ∃ C : Subgroup G, C.Normal ∧ C ≠ ⊥ ∧ IsCyclic C := by
  classical
  obtain ⟨n, s, h0, hn, _, hnormal, hstep⟩ := hG
  have hex : ∃ i, s i ≠ ⊥ := ⟨n, hn ▸ top_ne_bot⟩
  let i := Nat.find hex
  have hi : s i ≠ ⊥ := Nat.find_spec hex
  have hi0 : i ≠ 0 := by intro he; exact hi (he ▸ h0)
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hi0
  have hk0 : s k = ⊥ := by
    by_contra h
    have := Nat.find_min' hex h
    change i ≤ k at this
    omega
  have hin : i ≤ n := Nat.find_min' hex (hn ▸ top_ne_bot)
  obtain ⟨x, hx⟩ := hstep k (by omega)
  have hcyc : s i = Subgroup.zpowers x := by
    rw [hk, Nat.succ_eq_add_one, hx, hk0, bot_sup_eq]
  exact ⟨s i, hnormal i, hi, hcyc ▸ inferInstance⟩

/-- In the finite case one can choose the cyclic normal subgroup to have prime order. -/
theorem supersolvable_exists_prime_normal {G : Type*} [Group G] [Finite G]
    [Nontrivial G] (hG : Supersolvable G) :
    ∃ (C : Subgroup G) (q : ℕ), C.Normal ∧ q.Prime ∧ Nat.card C = q := by
  obtain ⟨B, hB, hB0, hcyc⟩ := supersolvable_exists_cyclic_normal hG
  letI := hB
  letI := hcyc
  letI : CommGroup B := IsCyclic.commGroup
  have hb : Nat.card B ≠ 1 := fun h => hB0 (B.eq_bot_iff_card.mpr h)
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hb
  let D : Subgroup B := (powMonoidHom q : B →* B).ker
  have hd : D.Characteristic := by
    apply Subgroup.characteristic_iff_le_comap.mpr
    intro e x hx
    change (e x) ^ q = 1
    change x ^ q = 1 at hx
    rw [← map_pow, hx, map_one]
  letI := hd
  refine ⟨D.map B.subtype, q, inferInstance, hq, ?_⟩
  rw [Subgroup.card_map_of_injective B.subtype_injective]
  change Nat.card (powMonoidHom q : B →* B).ker = q
  rw [IsCyclic.card_powMonoidHom_ker, Nat.gcd_eq_right hqd]

universe u

/-- The finite Hall cutoff theorem, proved from an invariant cyclic series.
The normal Hall subgroup contains exactly the prime divisors above `n`. -/
theorem supersolvable_exists_normalHall {G : Type u} [Group G] [Finite G]
    (hG : Supersolvable G) (n : ℕ) :
    ∃ M : Subgroup G, M.Normal ∧ IsHall {p | n < p} M := by
  classical
  suffices h : ∀ k : ℕ, ∀ {G : Type u} [Group G] [Finite G], Nat.card G = k →
      Supersolvable G → ∃ M : Subgroup G, M.Normal ∧ IsHall {p | n < p} M by
    exact h (Nat.card G) rfl hG
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro G _ _ hcard hG
    rcases subsingleton_or_nontrivial G with htriv | hnontriv
    · letI := htriv
      refine ⟨⊥, inferInstance, ?_, ?_⟩
      · intro p hp hd
        have : p ∣ 1 := by simpa using hd
        exact (hp.not_dvd_one this).elim
      · intro p hp hd
        have : p ∣ 1 := by simpa using hd
        exact (hp.not_dvd_one this).elim
    · letI := hnontriv
      obtain ⟨C, q, hCnormal, hq, hCcard⟩ := supersolvable_exists_prime_normal hG
      letI := hCnormal
      let π := QuotientGroup.mk' C
      have hquot : Nat.card (G ⧸ C) < k := by
        have hc := C.card_mul_index
        change Nat.card C * Nat.card (G ⧸ C) = Nat.card G at hc
        rw [hCcard, hcard] at hc
        have hpos := Nat.card_pos (α := G ⧸ C)
        have hq2 := hq.two_le
        nlinarith
      obtain ⟨D, hDnormal, hD⟩ := ih _ hquot rfl
        (supersolvable_of_surjective hG π (QuotientGroup.mk'_surjective C))
      letI := hDnormal
      let K := D.comap π
      have hCK : C ≤ K := by
        simpa only [π, QuotientGroup.ker_mk'] using Subgroup.ker_le_comap π D
      have hKmap : K.map π = D := Subgroup.map_comap_eq_self (by
        rw [π.range_eq_top_of_surjective (QuotientGroup.mk'_surjective C)]
        exact le_top)
      have hKindex : K.index = D.index := D.index_comap_of_surjective (QuotientGroup.mk'_surjective C)
      have hCsubcard : Nat.card (C.subgroupOf K) = q :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCK).toEquiv).trans hCcard
      have hCsubindex : (C.subgroupOf K).index = Nat.card D := by
        have hh := Subgroup.relIndex_ker K π
        simpa only [π, QuotientGroup.ker_mk', hKmap, Subgroup.relIndex] using hh
      have hKcard : Nat.card K = q * Nat.card D := by
        rw [← (C.subgroupOf K).card_mul_index, hCsubcard, hCsubindex]
      by_cases hqn : n < q
      · refine ⟨K, inferInstance, ?_, ?_⟩
        · intro p hp hd
          rw [hKcard] at hd
          rcases hp.dvd_mul.mp hd with hd | hd
          · exact ((Nat.prime_dvd_prime_iff_eq hp hq).mp hd) ▸ hqn
          · exact hD.1 p hp hd
        · intro p hp hd
          exact hD.2 p hp (hKindex ▸ hd)
      · have hqn' : q ≤ n := Nat.le_of_not_gt hqn
        have hcop : (Nat.card (C.subgroupOf K)).Coprime (C.subgroupOf K).index := by
          rw [hCsubcard, hCsubindex]
          exact hq.coprime_iff_not_dvd.mpr (fun hd => hqn (hD.1 q hq hd))
        obtain ⟨M, hCM⟩ := Subgroup.exists_right_complement'_of_coprime hcop
        have hMcard : Nat.card M = Nat.card D := hCM.card_right.trans hCsubindex
        have hMprimes : HasPrimes {p | n < p} M := by
          intro p hp hd
          exact hD.1 p hp (hMcard ▸ hd)
        have hMnormal : M.Normal := normal_complement_of_commute hCM
          (commute_prime_normal_of_large_primes (C.subgroupOf K) M hq hCsubcard hqn' hMprimes)
        letI := hMnormal
        have hMindex : M.index = q := hCM.index_eq_card.trans hCsubcard
        have hMHall : IsHall {p | n < p} M := by
          refine ⟨hMprimes, fun p hp hd hn => ?_⟩
          rw [hMindex] at hd
          have he := (Nat.prime_dvd_prime_iff_eq hp hq).mp hd
          exact hqn (he ▸ hn)
        letI := hMHall.characteristic_of_normal
        refine ⟨M.map K.subtype, inferInstance, hMprimes.map K.subtype, ?_⟩
        intro p hp hd hn
        rw [Subgroup.index_map_subtype, hMindex, hKindex] at hd
        rcases hp.dvd_mul.mp hd with hd | hd
        · exact hqn ((Nat.prime_dvd_prime_iff_eq hp hq).mp hd ▸ hn)
        · exact hD.2 p hp hd hn





end LocalConjugacy

end LocalConjugacy.Proof

end


