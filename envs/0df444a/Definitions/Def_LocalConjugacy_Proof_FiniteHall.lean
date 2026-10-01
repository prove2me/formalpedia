-- Prove2me | Definitions.Def_LocalConjugacy_Proof_FiniteHall
-- name    : LocalConjugacy_Proof_FiniteHall
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-30T15:21:09.977386+00:00
-- url     : https://prove2.me/theorems/b3f6b246-b0d9-4b74-acd4-e98e46e8774b
-- title:
--   Finite Hall subgroup constructions
-- statement:
--   Prime-set and coprimeness facts, images of Hall subgroups, characteristic normal Hall subgroups, and normal-complement constructions required by the profinite Hall inverse systems.
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

/-! Supporting definitions and the structural proofs required by their types and values. -/

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

theorem coprime_of_disjoint_primes {a b : ℕ} {π : Set ℕ}
    (ha : ∀ p, p.Prime → p ∣ a → p ∈ π)
    (hb : ∀ p, p.Prime → p ∣ b → p ∉ π) : a.Coprime b := by
  apply Nat.coprime_iff_gcd_eq_one.mpr
  by_contra h
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd h
  exact hb p hp (hd.trans (Nat.gcd_dvd_right a b))
    (ha p hp (hd.trans (Nat.gcd_dvd_left a b)))

theorem hom_eq_one_of_coprime_card {G F : Type*} [Group G] [Group F]
    (h : (Nat.card G).Coprime (Nat.card F)) (f : G →* F) (x : G) : f x = 1 := by
  apply orderOf_eq_one_iff.mp
  exact Nat.eq_one_of_dvd_coprimes h
    ((orderOf_map_dvd f x).trans (orderOf_dvd_natCard x)) (orderOf_dvd_natCard (f x))

theorem HasPrimes.map {G F : Type*} [Group G] [Group F] {π : Set ℕ}
    {H : Subgroup G} (hH : HasPrimes π H) (f : G →* F) : HasPrimes π (H.map f) :=
  fun p hp hd => hH p hp (hd.trans (H.card_map_dvd f))



theorem HasPrimes.le_normalHall {G : Type*} [Group G] {π : Set ℕ}
    {H K : Subgroup G} [K.Normal] (hH : HasPrimes π H) (hK : IsHall π K) : H ≤ K := by
  have hc : (Nat.card H).Coprime (Nat.card (G ⧸ K)) :=
    coprime_of_disjoint_primes hH hK.2
  intro x hx
  exact (QuotientGroup.eq_one_iff (N := K) x).mp
    (hom_eq_one_of_coprime_card hc ((QuotientGroup.mk' K).comp H.subtype) ⟨x, hx⟩)

theorem IsHall.eq_of_normal {G : Type*} [Group G] {π : Set ℕ}
    {H K : Subgroup G} [H.Normal] [K.Normal] (hH : IsHall π H) (hK : IsHall π K) :
    H = K := le_antisymm (hH.1.le_normalHall hK) (hK.1.le_normalHall hH)

theorem IsHall.characteristic_of_normal {G : Type*} [Group G] {π : Set ℕ}
    {H : Subgroup G} [H.Normal] (hH : IsHall π H) : H.Characteristic := by
  apply Subgroup.characteristic_iff_map_le.mpr
  intro e
  exact (hH.1.map e.toMonoidHom).le_normalHall hH



theorem IsHall.map_surjective {G F : Type*} [Group G] [Group F] {π : Set ℕ}
    {H : Subgroup G} (hH : IsHall π H) (f : G →* F) (hf : Function.Surjective f) :
    IsHall π (H.map f) := by
  refine ⟨hH.1.map f, fun p hp hd => hH.2 p hp ?_⟩
  exact hd.trans (H.index_map_dvd hf)

theorem complement_map_of_disjoint {G F : Type*} [Group G] [Group F]
    {M Q : Subgroup G} (h : M.IsComplement' Q) (f : G →* F)
    (hf : Function.Surjective f) (hd : Disjoint (M.map f) (Q.map f)) :
    (M.map f).IsComplement' (Q.map f) := by
  refine ⟨Subgroup.mul_injective_of_disjoint hd, ?_⟩
  intro y
  obtain ⟨x, rfl⟩ := hf y
  obtain ⟨⟨m, q⟩, rfl⟩ := h.2 x
  exact ⟨(⟨f m, Subgroup.mem_map_of_mem f m.property⟩,
    ⟨f q, Subgroup.mem_map_of_mem f q.property⟩), (f.map_mul m q).symm⟩

theorem disjoint_of_cutoff_primes {G : Type*} [Group G] {n : ℕ}
    {M Q : Subgroup G} (hM : HasPrimes {p | n < p} M)
    (hQ : HasPrimes {p | p ≤ n} Q) : Disjoint M Q := by
  apply Subgroup.disjoint_of_coprime_natCard
  exact coprime_of_disjoint_primes hM
    (fun p hp hd hn => Nat.not_lt_of_ge (hQ p hp hd) hn)



/-- A complement normalized by its own elements is also normalized by a
commuting complementary factor. -/
theorem normal_complement_of_commute {G : Type*} [Group G]
    {C M : Subgroup G} (h : C.IsComplement' M)
    (hc : ∀ (c : C) (m : M), Commute (c : G) (m : G)) : M.Normal := by
  constructor
  intro x hx g
  obtain ⟨⟨c, m⟩, rfl⟩ := h.2 g
  have hm : (m : G) * x * (m : G)⁻¹ ∈ M :=
    M.mul_mem (M.mul_mem m.property hx) (M.inv_mem m.property)
  have he := (hc c ⟨_, hm⟩).eq
  change (c : G) * ((m : G) * x * (m : G)⁻¹) =
    ((m : G) * x * (m : G)⁻¹) * c at he
  have hh : ((c : G) * m) * x * ((c : G) * m)⁻¹ = (m : G) * x * (m : G)⁻¹ := by
    calc
      _ = (c : G) * ((m : G) * x * (m : G)⁻¹) * (c : G)⁻¹ := by group
      _ = _ := by rw [he]; group
  simpa only [hh] using hm

/-- A group with all prime divisors larger than `n` acts trivially on a
normal subgroup of prime order at most `n`. -/
theorem commute_prime_normal_of_large_primes {G : Type*} [Group G] [Finite G]
    (C M : Subgroup G) [C.Normal] {n q : ℕ}
    (hq : q.Prime) (hC : Nat.card C = q) (hqn : q ≤ n)
    (hM : HasPrimes {p | n < p} M) :
    ∀ (c : C) (m : M), Commute (c : G) (m : G) := by
  letI : Fact q.Prime := ⟨hq⟩
  letI : IsCyclic C := isCyclic_of_prime_card hC
  have hq2 := hq.two_le
  have ha : Nat.card (MulAut C) = q - 1 := by
    rw [IsCyclic.card_mulAut, hC, Nat.totient_prime hq]
  have hcop : (Nat.card M).Coprime (Nat.card (MulAut C)) := by
    apply coprime_of_disjoint_primes hM
    intro p hp hd hn
    rw [ha] at hd
    have hle := Nat.le_of_dvd (by omega : 0 < q - 1) hd
    change n < p at hn
    omega
  intro c m
  have he := congrArg (fun a : MulAut C => a c)
    (hom_eq_one_of_coprime_card hcop ((MulAut.conjNormal (H := C)).comp M.subtype) m)
  have he' := congrArg Subtype.val he
  change (m : G) * c * (m : G)⁻¹ = c at he'
  exact by calc
    (c : G) * m = ((m : G) * c * (m : G)⁻¹) * m := by rw [he']
    _ = (m : G) * c := by group

end LocalConjugacy

end LocalConjugacy.Proof

end


