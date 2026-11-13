-- Prove2me | Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_SetupLemma151
-- name    : OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_SetupLemma151
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T09:53:18.445198+00:00
-- url     : https://prove2.me/theorems/b488bcf2-a5c7-4818-881f-896f79e4d43a
-- title:
--   BG §15: notation and Lemma 15.1 ($UM_\sigma$ auxiliary structure)
-- statement:
--   The §15 notation and Lemma 15.1 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem* on the auxiliary structure $UM_\sigma$, split from the former monolithic §15 file. Lemmas include criteria for type $\mathcal{P}$ and type $F$ via Hall $\kappa$-subgroups and a $E$-setup when the Hall $\kappa$-subgroup is trivial.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 15 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch4_FamilyOfMaximal/S15_MF/SetupLemma151.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch4_FamilyOfMaximal/S15_MF/SetupLemma151.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_Basics
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_LocalStructure
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_SigmaLengthOne
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_TypePDuality
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_GlobalCounting
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03h_Thm38
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03g_Thm310ElemAbelian
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S05_NarrowCharacterization
import Definitions.Def_OddOrder_Mathlib_Subgroup
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_AutAbelianCore

namespace OddOrder.BG.Ch4.S15

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.BG.Ch3.S12

open OddOrder.BG.Ch4.S14

open scoped Pointwise

open scoped IsMulCommutative

open scoped commutatorElement

variable {G : Type*} [Group G]

/-- **`K ≠ ⊥` for a Hall `κ(M)`-subgroup of `M` forces `IsTypeP M`** (`§14`-independent bridge).
A nontrivial Hall `κ(M)`-subgroup has a prime divisor, which lies in `κ(M)`; hence `κ(M)` is
nonempty, i.e. `M` is type `P`.  This converts the `K ≠ ⊥` case split of Lemma 15.1 into the
`IsTypeP M` hypothesis that the §14 results (`typeP_duality`, `typeP_structure`) require. -/
theorem isTypeP_of_isHall_kappa_subgroupOf_ne_bot [Finite G] {M K : Subgroup G}
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M)) (hKne : K.subgroupOf M ≠ ⊥) :
    S14.IsTypeP M := by
  have hcard : Nat.card ↥(K.subgroupOf M) ≠ 1 := fun h => hKne (Subgroup.card_eq_one.mp h)
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hcard
  exact ⟨p, hK.1 p (Nat.mem_primeFactors.mpr ⟨hp, hpdvd, Nat.card_pos.ne'⟩)⟩

/-- **Abstract second-derived containment** (`§14`-independent, reusable): if `N ⊴ H` and the
derived subgroup of the quotient `H ⧸ N` is abelian, then `⁅H', H'⁆ ≤ N` (the second derived
subgroup of `H`, as a subgroup of `H`, lies in `N`).  The quotient map `mk'` sends `⁅H', H'⁆`
onto `(H/N)''`, which is trivial because `(H/N)'` is abelian; hence `⁅H', H'⁆ ≤ ker mk' = N`.
This is the "(M/M_σ)' abelian ⟹ M'' ≤ M_σ" step of Lemma 15.1(a). -/
theorem commutator_commutator_le_of_quotient_commutator_commutative {H : Type*} [Group H]
    {N : Subgroup H} [hN : N.Normal] (hab : IsMulCommutative ↥(commutator (H ⧸ N))) :
    ⁅commutator H, commutator H⁆ ≤ N := by
  -- `(H/N)'' = ⁅(H/N)', (H/N)'⁆ = ⊥` since `(H/N)'` is abelian.
  have hdd_bot : ⁅commutator (H ⧸ N), commutator (H ⧸ N)⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have := hab.is_comm.comm (⟨y, hy⟩ : ↥(commutator (H ⧸ N))) ⟨x, hx⟩
    exact congrArg Subtype.val this
  -- `(H/N)' = (H').map mk'` and `(H/N)'' = ⁅H', H'⁆.map mk'` (mk' surjective).
  have hsurj : (QuotientGroup.mk' N).range = ⊤ :=
    MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N)
  have hmap1 : (commutator H).map (QuotientGroup.mk' N) = commutator (H ⧸ N) := by
    rw [map_commutator_eq, hsurj, _root_.commutator_def]
  have hmap2 : (⁅commutator H, commutator H⁆).map (QuotientGroup.mk' N) =
      ⁅commutator (H ⧸ N), commutator (H ⧸ N)⁆ := by
    rw [Subgroup.map_commutator, hmap1]
  rw [hdd_bot, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hmap2
  exact hmap2

/-- **`IsMulCommutative` of a commutator subgroup transports along a `MulEquiv`** (`§14`-
independent, reusable): if `A ≃* B` and `A'` is abelian, then `B'` is abelian.  The equivalence
maps `A'` onto `B'`, so `↥A' ≃* ↥B'`. -/
theorem isMulCommutative_commutator_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hA : IsMulCommutative ↥(commutator A)) : IsMulCommutative ↥(commutator B) := by
  have hmap : (commutator A).map (e : A →* B) = commutator B := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective, _root_.commutator_def]
  exact OddOrder.BG.Ch3.S11.isMulCommutative_of_mulEquiv
    ((MulEquiv.subgroupMap e (commutator A)).trans (MulEquiv.subgroupCongr hmap)) hA

/-- **Lemma 15.1(a), the `M'' ≤ M_σ` conjunct** (`§14`-independent): the second derived subgroup
of a maximal subgroup `M` is contained in `M_σ`.  Equivalently `(M/M_σ)'` is abelian; this is
Corollary 12.10(b) (`E' = (M/M_σ)'` abelian via the complement `M = M_σ ⋊ E`).  Proof: pick a
`SubgroupESetup` complement `E`, get `IsMulCommutative (derivedInG E)` from Cor 12.10(b), transport
it to `(↥M ⧸ N)'` abelian along `↥M ⧸ N ≃* E` (`IsComplement'.QuotientMulEquiv`), then apply the
abstract `commutator_commutator_le_of_quotient_commutator_commutative` and push to the ambient. -/
theorem derivedDerived_le_Msigma [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    derivedInG (derivedInG M) ≤ OddOrder.BG.Ch3.S10.Msigma M := by
  classical
  -- §12 complement setup and `(M/M_σ)' = E'` abelian (Cor 12.10(b)).
  obtain ⟨E, E₁, E₂, E₃, hsetup⟩ := OddOrder.BG.Ch3.S12.exists_subgroupESetup hG hM
  obtain ⟨_, ⟨_, hE'ab⟩, _⟩ := OddOrder.BG.Ch3.S12.nilpotent_sigmaComplement_abelian hG hsetup
  set N : Subgroup ↥M := (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M with hNdef
  have hNnorm : N.Normal := by rw [hNdef, OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
  -- `derivedInG E ≅ commutator ↥E`, so `commutator ↥E` is abelian.
  have hcommE_ab : IsMulCommutative ↥(commutator ↥E) := by
    have e : ↥(commutator ↥E) ≃* ↥(derivedInG E) :=
      Subgroup.equivMapOfInjective (commutator ↥E) E.subtype E.subtype_injective
    exact OddOrder.BG.Ch3.S11.isMulCommutative_of_mulEquiv e.symm hE'ab
  -- transport `commutator ↥E` abelian to `commutator (↥M ⧸ N)` abelian via the complement iso.
  have hquot_ab : IsMulCommutative ↥(commutator (↥M ⧸ N)) := by
    have hcompl : (E.subgroupOf M).IsComplement' N := hsetup.isComplement'_subgroupOf.symm
    have e1 : (↥M ⧸ N) ≃* ↥(E.subgroupOf M) := hcompl.QuotientMulEquiv
    have e2 : ↥(E.subgroupOf M) ≃* ↥E := Subgroup.subgroupOfEquivOfLe hsetup.E_le
    exact isMulCommutative_commutator_of_mulEquiv (e1.trans e2).symm hcommE_ab
  -- abstract lemma: `⁅commutator ↥M, commutator ↥M⁆ ≤ N`, then push to the ambient.
  have hle : ⁅commutator ↥M, commutator ↥M⁆ ≤ N :=
    commutator_commutator_le_of_quotient_commutator_commutative hquot_ab
  -- `derivedInG (derivedInG M) = ⁅commutator ↥M, commutator ↥M⁆.map M.subtype`.
  have hderiv_eq : derivedInG (derivedInG M) =
      (⁅commutator ↥M, commutator ↥M⁆).map M.subtype := by
    rw [show derivedInG (derivedInG M) = ⁅derivedInG M, derivedInG M⁆ from
        Subgroup.map_subtype_commutator (derivedInG M),
      derivedInG, Subgroup.map_commutator]
  rw [hderiv_eq]
  calc (⁅commutator ↥M, commutator ↥M⁆).map M.subtype
      ≤ N.map M.subtype := Subgroup.map_mono hle
    _ = OddOrder.BG.Ch3.S10.Msigma M := by
        rw [hNdef, Subgroup.map_subgroupOf_eq_of_le (OddOrder.BG.Ch3.S10.Msigma_le M)]

/-- **`K = ⊥` forces `κ(M) = ∅`** (`§14`-independent): if the Hall `κ(M)`-subgroup `K ≤ M` of `M`
is trivial, then `M` has no `κ(M)`-prime, so `κ(M) = ∅`, i.e. `M` is type `F`.  (A `κ(M)`-prime
would divide `|M|` — `κ(M) ⊆ π(M)` — and the Hall `κ(M)`-subgroup would be nontrivial.) -/
theorem isTypeF_of_isHall_kappa_eq_bot [Finite G] {M K : Subgroup G} (_hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M)) (hKbot : K = ⊥) :
    S14.IsTypeF M := by
  by_contra hF
  -- `¬ IsTypeF M` means `κ(M) ≠ ∅`, so there is a `κ(M)`-prime `p`.
  rw [S14.IsTypeF, ← ne_eq, ← Set.nonempty_iff_ne_empty] at hF
  obtain ⟨p, hp⟩ := hF
  -- `p ∈ κ(M)`, so `p` is prime with a line `P ∈ ℰ_p¹(G)`, `P ≤ M`, `M_σ ⊓ C_G(P) ≠ 1`.
  have hpp : p.Prime := hp.1
  obtain ⟨_, P, hP, hPM, _⟩ := hp.2
  have : Fact p.Prime := ⟨hpp⟩
  -- `p ∣ |P|` (since `|P| = p`) and `P ≤ M`, so `p ∣ |M|`.
  have hpdvdP : p ∣ Nat.card ↥P := by
    obtain ⟨_, hPcard⟩ := hP
    rw [hPcard, pow_one]
  have hpM : p ∈ (Nat.card ↥M).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hpp, hpdvdP.trans (Subgroup.card_dvd_of_le hPM), Nat.card_pos.ne'⟩
  -- `p ∤ [M : K.subgroupOf M]` (Hall), so `p ∣ |K.subgroupOf M|`, contradicting `K = ⊥`.
  have hpidx : ¬ p ∣ (K.subgroupOf M).index := fun hdvd =>
    hK.2 p (Nat.mem_primeFactors.mpr ⟨hpp, hdvd, Subgroup.index_ne_zero_of_finite⟩) hp
  have hpKcard : p ∣ Nat.card ↥(K.subgroupOf M) := by
    have hsplit : Nat.card ↥(K.subgroupOf M) * (K.subgroupOf M).index = Nat.card ↥M :=
      Subgroup.card_mul_index _
    rcases (Nat.Prime.dvd_mul hpp).mp (hsplit ▸ (Nat.dvd_of_mem_primeFactors hpM)) with h | h
    · exact h
    · exact absurd h hpidx
  rw [hKbot, Subgroup.bot_subgroupOf, Subgroup.card_bot] at hpKcard
  exact (Nat.Prime.one_lt hpp).ne' (Nat.dvd_one.mp hpKcard)

/-- **`K = ⊥ → U` is a `σ(M)'`-complement and `M = U ⊔ M_σ`** (`§14`-independent Hall complement).
When `κ(M) = ∅` (i.e. `K = ⊥`), `(κ(M) ∪ σ(M))' = σ(M)'`, so `U ≤ M` is a `σ(M)'`-Hall subgroup of
`M`; it must coincide with the §12 complement `E` (both `σ(M)'`-Hall in `M`, with `U ≤ E`), and
`M_σ ⊔ E = M`.  Returns the `SubgroupESetup` exhibiting `U` as the complement (`E = U`), which
also feeds the type-`F` half of Lemma 15.1(d)(e) (Theorem 12.12 with `E := U`). -/
theorem subgroupESetup_of_isHall_kappa_eq_bot [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M)) (hKbot : K = ⊥)
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    ∃ E₁ E₂ E₃ : Subgroup G, OddOrder.BG.Ch3.S12.SubgroupESetup M U E₁ E₂ E₃ := by
  classical
  set σ := OddOrder.BG.Ch3.S10.sigma M with hσ
  have hF : S14.IsTypeF M := isTypeF_of_isHall_kappa_eq_bot hKM hK hKbot
  have hκ : S14.kappa M = ∅ := hF
  -- `U` is a `σ'`-Hall subgroup of `M`.
  have hUσ' : Ch03.IsHallSubgroup (σᶜ) (U.subgroupOf M) := by
    have heq : (S14.kappa M ∪ σ)ᶜ = σᶜ := by rw [hκ, Set.empty_union]
    rwa [heq] at hU
  have hU_pi : Subgroup.IsPiSubgroup (σᶜ) U := by
    intro p hp
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv] at hp
    exact hUσ'.1 p hp
  -- §12 complement `E ⊇ U`, `σ'`-Hall.
  obtain ⟨E, E₁, E₂, E₃, hsetup, hUE, hE_pi⟩ :=
    OddOrder.BG.Ch3.S12.exists_subgroupESetup_with_le hG hM hUM hU_pi
  -- `U = E`:  `E` is a `σ'`-group, `U` is `σ'`-Hall, and `U ≤ E`, so `|E| ∣ |U|` and `|U| ∣ |E|`.
  have hUEeq : U = E := by
    have hEpi : Ch03.Subgroup.IsPiGroup (σᶜ) (E.subgroupOf M) := by
      intro q hq
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsetup.E_le).toEquiv] at hq
      exact hE_pi q hq
    have hEdvdU : Nat.card ↥E ∣ Nat.card ↥U := by
      have hd := hUσ'.card_dvd_of_isPiGroup hEpi
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsetup.E_le).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv] at hd
    exact Subgroup.eq_of_le_of_card_ge hUE
      (Nat.dvd_antisymm hEdvdU (Subgroup.card_dvd_of_le hUE)).le
  -- transport the `SubgroupESetup` from `E` to `U`.
  exact ⟨E₁, E₂, E₃, hUEeq ▸ hsetup⟩

/-- **The three Hall factors `K`, `U`, `M_σ` partition `|M|`** (`§14`-independent counting helper).
With `K` a `κ(M)`-Hall, `U` a `(κ(M) ∪ σ(M))'`-Hall, and `M_σ` the `σ(M)`-Hall of `M`, the three
prime sets `κ`, `(κ ∪ σ)'`, `σ` are pairwise disjoint and cover every prime, so the orders multiply
to `|M|`.  Proven by prime-by-prime factorization: each prime `p` of `|M|` lies in exactly one of
the three sets, and the corresponding Hall subgroup carries the full `p`-part (its index is a
`p'`-number). -/
theorem card_mul_card_mul_card_eq_of_three_hall [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    Nat.card ↥(K.subgroupOf M) * Nat.card ↥(U.subgroupOf M) *
      Nat.card ↥((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) = Nat.card ↥M := by
  classical
  set a := Nat.card ↥(K.subgroupOf M) with ha
  set b := Nat.card ↥(U.subgroupOf M) with hb
  set c := Nat.card ↥((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) with hc
  set n := Nat.card ↥M with hn
  have hMσ : Ch03.IsHallSubgroup (OddOrder.BG.Ch3.S10.sigma M)
      ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) :=
    OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall hG hM
  have hane : a ≠ 0 := Nat.card_pos.ne'
  have hbne : b ≠ 0 := Nat.card_pos.ne'
  have hcne : c ≠ 0 := Nat.card_pos.ne'
  have hnne : n ≠ 0 := Nat.card_pos.ne'
  -- Each Hall card divides `|M|`.
  have hadvd : a ∣ n := Subgroup.card_subgroup_dvd_card _
  have hbdvd : b ∣ n := Subgroup.card_subgroup_dvd_card _
  have hcdvd : c ∣ n := Subgroup.card_subgroup_dvd_card _
  -- Prime-set membership of the three Hall cards.
  have hUprimes_compl : ∀ p ∈ b.primeFactors, p ∈ (S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ :=
    hU.1
  have hUprimes_notκ : ∀ p ∈ b.primeFactors, p ∉ S14.kappa M := fun p hp hpκ =>
    hUprimes_compl p hp (Or.inl hpκ)
  have hUprimes_notσ : ∀ p ∈ b.primeFactors, p ∉ OddOrder.BG.Ch3.S10.sigma M := fun p hp hpσ =>
    hUprimes_compl p hp (Or.inr hpσ)
  have hKprimes_notσ : ∀ p ∈ a.primeFactors, p ∉ OddOrder.BG.Ch3.S10.sigma M := fun p hp =>
    S14.kappa_subset_sigmaCompl (hK.1 p hp)
  -- Pairwise coprimality of the three Hall cards (disjoint prime sets).
  have hcop_ab : Nat.Coprime a b :=
    Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl (π := S14.kappa M) hane hbne hK.1
      hUprimes_notκ
  have hcop_ac : Nat.Coprime a c :=
    Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      (π := OddOrder.BG.Ch3.S10.sigma M) hcne hane hMσ.1 hKprimes_notσ |>.symm
  have hcop_bc : Nat.Coprime b c :=
    Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      (π := OddOrder.BG.Ch3.S10.sigma M) hcne hbne hMσ.1 hUprimes_notσ |>.symm
  -- `a * b * c ∣ n` from pairwise coprimality + each `∣ n`.
  have habc_dvd : a * b * c ∣ n :=
    (Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.coprime_mul_iff_left.mpr ⟨hcop_ac, hcop_bc⟩)
      (hcop_ab.mul_dvd_of_dvd_of_dvd hadvd hbdvd) hcdvd)
  -- `n ∣ a * b * c` by prime-by-prime factorization: each prime of `n` lies in `κ`, `σ`, or
  -- `(κ ∪ σ)'`, and the corresponding Hall subgroup carries its full `p`-part.
  have hn_dvd : n ∣ a * b * c := by
    rw [← Nat.factorization_prime_le_iff_dvd hnne (mul_ne_zero (mul_ne_zero hane hbne) hcne)]
    intro p hp
    rw [Nat.factorization_mul (mul_ne_zero hane hbne) hcne,
      Nat.factorization_mul hane hbne, Finsupp.add_apply, Finsupp.add_apply]
    -- For a Hall `π`-subgroup `H` of `M` with `p ∉ index`, `n.factorization p = (card H).factor p`.
    -- Choose the Hall whose prime set contains `p`.
    by_cases hpκ : p ∈ S14.kappa M
    · -- `p ∈ κ`: `K` carries the `p`-part.
      have hpidx : ¬ p ∣ (K.subgroupOf M).index := fun hd =>
        hK.2 p (Nat.mem_primeFactors.mpr ⟨hp, hd, Subgroup.index_ne_zero_of_finite⟩) hpκ
      have hsplit : a * (K.subgroupOf M).index = n := Subgroup.card_mul_index _
      have : n.factorization p = a.factorization p := by
        rw [← hsplit, Nat.factorization_mul hane (Subgroup.index_ne_zero_of_finite),
          Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hpidx, add_zero]
      omega
    · by_cases hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma M
      · -- `p ∈ σ`: `M_σ` carries the `p`-part.
        have hpidx : ¬ p ∣ ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).index := fun hd =>
          hMσ.2 p (Nat.mem_primeFactors.mpr ⟨hp, hd, Subgroup.index_ne_zero_of_finite⟩) hpσ
        have hsplit : c * ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).index = n :=
          Subgroup.card_mul_index _
        have : n.factorization p = c.factorization p := by
          rw [← hsplit, Nat.factorization_mul hcne (Subgroup.index_ne_zero_of_finite),
            Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hpidx, add_zero]
        omega
      · -- `p ∈ (κ ∪ σ)'`: `U` carries the `p`-part.
        have hpcompl : p ∈ (S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ :=
          Set.mem_compl (fun h => h.elim hpκ hpσ)
        have hpidx : ¬ p ∣ (U.subgroupOf M).index := fun hd =>
          hU.2 p (Nat.mem_primeFactors.mpr ⟨hp, hd, Subgroup.index_ne_zero_of_finite⟩) hpcompl
        have hsplit : b * (U.subgroupOf M).index = n := Subgroup.card_mul_index _
        have : n.factorization p = b.factorization p := by
          rw [← hsplit, Nat.factorization_mul hbne (Subgroup.index_ne_zero_of_finite),
            Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hpidx, add_zero]
        omega
  exact Nat.dvd_antisymm habc_dvd hn_dvd

/-- **BG Lemma 15.1(b)** (mmd L4169): for a maximal `M` with nontrivial κ-Hall `K`,
`M' = U M_σ` and `U` is abelian (`U` a `(κ∪σ)'`-Hall subgroup of `M`).

Proof: `K ≠ ⊥` forces `IsTypeP M`, so Theorem 14.7(h) (`typeP_duality`) gives that `M'` complements
the κ-Hall `K` in `M`, with `|M'|`, `|K|` coprime.  Then:
* `U ⊓ M_σ = ⊥` (coprime orders: `|U|` is a `(κ∪σ)'`-number, `|M_σ|` a `σ`-number);
* `M_σ ≤ M'` (`Msigma_le_derived`) and `U ≤ M'` (the κ'-number `|U|` is coprime to the κ-number
  index `[M:M'] = |K|`, so `U ≤ M'` via `le_of_coprime_index`); hence `U M_σ ≤ M'`;
* `|M'| = |U|·|M_σ|` from the three-Hall partition `|M| = |K|·|U|·|M_σ|`
  (`card_mul_card_mul_card_eq_of_three_hall`) and the complement `|M'|·|K| = |M|`; combined with
  `U ⊓ M_σ = ⊥` (so `|U M_σ| = |U|·|M_σ|`) this gives `|U M_σ| = |M'|`, hence equality;
* `U` abelian: `⁅U,U⁆ ≤ U ⊓ M_σ = ⊥` (using `U ≤ M'` and `M'' ≤ M_σ` from
  `derivedDerived_le_Msigma`), so `commutator ↥U = ⊥`. -/
theorem typeP_hall_derived_eq_and_abelian [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hKM : K ≤ M) (hUM : U ≤ M)
    (hKne : K ≠ ⊥)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    derivedInG M = U ⊔ OddOrder.BG.Ch3.S10.Msigma M ∧ IsMulCommutative ↥U := by
  classical
  set Mσ := OddOrder.BG.Ch3.S10.Msigma M with hMσdef
  have hM'le : derivedInG M ≤ M := Subgroup.map_subtype_le _
  -- `IsTypeP M` from `K ≠ ⊥`.
  have hKofne : K.subgroupOf M ≠ ⊥ := by
    rw [ne_eq, Subgroup.subgroupOf_eq_bot]
    exact fun hd => hKne (hd.eq_bot_of_le hKM)
  have hP : S14.IsTypeP M := isTypeP_of_isHall_kappa_subgroupOf_ne_bot hK hKofne
  -- Theorem 14.7(h): `M'` complements `K` in `M`, with coprime orders.
  obtain ⟨hcompl, _hcoprime, _⟩ := typeP_duality hG hM hP hKM hK rfl
  -- `M_σ ≤ M'`.
  have hMσ_le_M' : Mσ ≤ derivedInG M := OddOrder.BG.Ch3.S10.Msigma_le_derived hG hM
  -- `M_σ` is `σ`-Hall in `M`.
  have hMσHall : Ch03.IsHallSubgroup (OddOrder.BG.Ch3.S10.sigma M) (Mσ.subgroupOf M) :=
    OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall hG hM
  -- `U ⊓ M_σ = ⊥`: `|U|` is a `(κ∪σ)'`-number, `|M_σ|` a `σ`-number, so coprime.
  have hUMσ_bot : U ⊓ Mσ = ⊥ := by
    have hcop : Nat.Coprime (Nat.card ↥U) (Nat.card ↥Mσ) := by
      refine Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
        (π := (S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) Nat.card_pos.ne' Nat.card_pos.ne'
        ?_ ?_
      · intro p hp
        exact hU.1 p (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv])
      · intro p hp hpcompl
        have hpMσ : p ∈ (Nat.card ↥(Mσ.subgroupOf M)).primeFactors := by
          rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (OddOrder.BG.Ch3.S10.Msigma_le
              M)).toEquiv]
        exact hpcompl (Or.inr (hMσHall.1 p hpMσ))
    exact (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  -- `U ≤ M'`: `|U|` (a κ'-number) is coprime to `[M:M'] = |K|` (a κ-number).
  have hU_le_M' : U ≤ derivedInG M := by
    have hM'norm : ((derivedInG M).subgroupOf M).Normal := by
      rw [derivedInG, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
      infer_instance
    have := hM'norm
    -- `[M:M'] = |K|` (index of the complement factor).
    have hidx : ((derivedInG M).subgroupOf M).index = Nat.card ↥(K.subgroupOf M) :=
      hcompl.symm.index_eq_card
    -- `Coprime |U.subgroupOf M| [M:M']`.
    have hcop : Nat.Coprime (Nat.card ↥(U.subgroupOf M)) ((derivedInG M).subgroupOf M).index := by
      rw [hidx]
      refine (Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl (π := S14.kappa M)
        Nat.card_pos.ne' Nat.card_pos.ne' hK.1 ?_).symm
      intro p hp hpκ
      exact hU.1 p hp (Or.inl hpκ)
    have hUsub_le : U.subgroupOf M ≤ (derivedInG M).subgroupOf M :=
      S14.le_of_coprime_index (N := (derivedInG M).subgroupOf M) (H := U.subgroupOf M) hcop
    -- Push back to the ambient via `M.subtype`.
    calc U = (U.subgroupOf M).map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hUM).symm
      _ ≤ ((derivedInG M).subgroupOf M).map M.subtype := Subgroup.map_mono hUsub_le
      _ = derivedInG M := Subgroup.map_subgroupOf_eq_of_le hM'le
  -- `U M_σ ≤ M'`.
  have hsup_le : U ⊔ Mσ ≤ derivedInG M := sup_le hU_le_M' hMσ_le_M'
  -- Cardinalities.  `|M'| = |U|·|M_σ|`.
  have hcardM' : Nat.card ↥(derivedInG M) = Nat.card ↥U * Nat.card ↥Mσ := by
    -- complement: `|M'.subgroupOf M| · |K.subgroupOf M| = |M|`.
    have hcompl_card : Nat.card ↥((derivedInG M).subgroupOf M) * Nat.card ↥(K.subgroupOf M)
        = Nat.card ↥M := hcompl.card_mul_card
    -- three-Hall partition: `|K|·|U|·|M_σ| = |M|` (subgroupOf).
    have hthree := card_mul_card_mul_card_eq_of_three_hall hG hM hK hU
    -- transport subgroupOf cards to ambient cards.
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'le).toEquiv] at hcompl_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (OddOrder.BG.Ch3.S10.Msigma_le M)).toEquiv]
      at hthree
    -- `|M'| · |K| = |M| = |K| · |U| · |M_σ|`, cancel `|K|`.
    have hKpos : 0 < Nat.card ↥(K.subgroupOf M) := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_right hKpos
    rw [hcompl_card, ← hthree]
    ring
  -- `|U M_σ| = |U|·|M_σ|` (disjoint, `U ≤ M ≤ N_G(M_σ)`).
  have hUnorm : U ≤ Subgroup.normalizer (Mσ : Set G) := by
    refine le_trans hUM ?_
    rw [hMσdef, OddOrder.BG.Ch3.S10.Msigma]
    exact le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) M
  have hcardSup : Nat.card ↥(U ⊔ Mσ) = Nat.card ↥U * Nat.card ↥Mσ :=
    card_sup_eq_mul_of_le_normalizer_of_disjoint hUnorm hUMσ_bot
  -- `M' = U M_σ` by `le_antisymm` + equal cardinality.
  have hderiv_eq : derivedInG M = U ⊔ Mσ := by
    refine (Subgroup.eq_of_le_of_card_ge hsup_le ?_).symm
    rw [hcardSup, hcardM']
  refine ⟨hderiv_eq, ?_⟩
  -- `U` abelian: `derivedInG U ≤ U ⊓ M_σ = ⊥`, so `commutator ↥U = ⊥`.
  have hUU_le_M'' : derivedInG U ≤ Mσ :=
    (OddOrder.BG.Ch3.S12.derivedInG_le_derivedInG hU_le_M').trans
      (derivedDerived_le_Msigma hG hM)
  have hUU_le_U : derivedInG U ≤ U := Subgroup.map_subtype_le (commutator ↥U)
  have hUU_bot : derivedInG U = ⊥ := le_bot_iff.mp (hUMσ_bot ▸ le_inf hUU_le_U hUU_le_M'')
  -- `derivedInG U = (commutator ↥U).map U.subtype = ⊥` and `U.subtype` injective ⟹ `comm ↥U = ⊥`.
  have hcomm_bot : commutator ↥U = ⊥ := by
    have := hUU_bot
    rw [derivedInG, Subgroup.map_eq_bot_iff, U.ker_subtype] at this
    exact le_bot_iff.mp this
  exact (commutator_eq_bot_iff ↥U).mp hcomm_bot

/-- **BG Lemma 15.1(d)** (mmd L4171): the subgroup `⟨C_U(x) | x ∈ M_σ#⟩` generated by the
centralizers in `U` of the nonidentity `σ`-elements is abelian.

Proof by the `K = ⊥` case split:

* `K ≠ ⊥`: `U` itself is abelian (`typeP_hall_derived_eq_and_abelian`, mmd 15.1(b)); the
  generated subgroup `centralizerGeneratedBySigma M U ≤ U` (a `sSup` of subgroups `U ⊓ C(x) ≤ U`),
  so a subgroup of an abelian group is abelian.
* `K = ⊥`: `M` is type `F`, so `κ(M) = ∅` and `U` is the `σ`-complement `E` of a §12 `E`-setup
  (`subgroupESetup_of_isHall_kappa_eq_bot`).  Theorem 12.12(a)
  (`frobenius_factorization_of_regular`) supplies an abelian normal subgroup `A₀ ≤ U` swallowing
  every `C_U(x)` (`x ∈ M_σ#`); its regularity hypothesis `hreg` is discharged via Lemma 14.1
  (`msigma_structure_of_notMem_sigma_kappa`): a prime-order power `f` of a `(τ₁∪τ₃)`-element
  `e ∈ U#` generates `A = ⟨f⟩ ∈ ℰ_p^{r_p(M)}(M)` with `p ∉ σ(M)` (`τ₁∪τ₃ ⊆ σ′`) and
  `p ∉ κ(M) = ∅`, giving `M_σ ⊓ C(A) = ⊥`, whence `M_σ ⊓ C(e) ≤ M_σ ⊓ C(f) = ⊥`.  Then
  `centralizerGeneratedBySigma M U ≤ A₀` (`sSup` of swallowed generators), so abelian. -/
theorem typeP_centralizerGeneratedBySigma_isMulCommutative [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K U : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    IsMulCommutative ↥(centralizerGeneratedBySigma M U) := by
  classical
  set Mσ := OddOrder.BG.Ch3.S10.Msigma M with hMσdef
  by_cases hKbot : K = ⊥
  · -- **Case `K = ⊥`**: `U` is the `σ`-complement `E` of a §12 `E`-setup; Theorem 12.12(a).
    have hκ : S14.kappa M = ∅ := isTypeF_of_isHall_kappa_eq_bot hKM hK hKbot
    obtain ⟨E₁, E₂, E₃, hsetup⟩ :=
      subgroupESetup_of_isHall_kappa_eq_bot hG hM hKM hUM hK hKbot hU
    -- Discharge the regularity hypothesis of Theorem 12.12 via Lemma 14.1.
    have hreg : ∀ e ∈ U, e ≠ 1 →
        (∀ r ∈ (orderOf e).primeFactors, r ∈ tau1 M ∪ tau3 M) →
          Mσ ⊓ Subgroup.centralizer ({e} : Set G) = ⊥ := by
      intro e heU hene hprimes
      -- pick a prime divisor `p` of `orderOf e`; then `p ∈ τ₁(M) ∪ τ₃(M)`.
      have hord1 : orderOf e ≠ 1 := fun hc => hene (orderOf_eq_one_iff.mp hc)
      obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hord1
      have : Fact p.Prime := ⟨hp⟩
      have hpτ : p ∈ tau1 M ∪ tau3 M :=
        hprimes p (Nat.mem_primeFactors.mpr ⟨hp, hpdvd, (orderOf_pos e).ne'⟩)
      -- the prime-order power `f = e^(orderOf e / p)` and its cyclic group `A = ⟨f⟩`.
      set f : G := e ^ (orderOf e / p) with hfdef
      have hford : orderOf f = p := orderOf_pow_orderOf_div (orderOf_pos e).ne' hpdvd
      have hfU : f ∈ U := U.pow_mem heU _
      have hfM : f ∈ M := hUM hfU
      set A : Subgroup G := Subgroup.zpowers f with hAdef
      have hAcard : Nat.card ↥A = p := by rw [hAdef, Nat.card_zpowers]; exact hford
      have hAelem : A.IsElementaryAbelian p := Subgroup.IsElementaryAbelian.of_card_prime hAcard
      have hAM : A ≤ M := by rw [hAdef, Subgroup.zpowers_le]; exact hfM
      -- Lemma 14.1 hypotheses: `p ∈ π(M)`, `p ∉ σ(M)` (`τ₁∪τ₃ ⊆ σ′`), `p ∉ κ(M) = ∅`.
      have hpπ : p ∈ S14.piSet M :=
        Nat.mem_primeFactors.mpr ⟨hp, hpdvd.trans ((U.orderOf_dvd_natCard heU).trans
          (Subgroup.card_dvd_of_le hUM)), Nat.card_pos.ne'⟩
      have hpσ : p ∉ OddOrder.BG.Ch3.S10.sigma M :=
        hpτ.elim (fun h => tau1_subset_sigma_compl M h) (fun h => tau3_subset_sigma_compl M h)
      have hpκ : p ∉ S14.kappa M := by rw [hκ]; simp
      -- maximal-rank elementary abelian witness: `r_p(M) = 1`, so `A ∈ ℰ_p^{r_p(M)}(M)`.
      have hr1 : pRank ↥M p = 1 :=
        hpτ.elim tau1_pRank_eq_one tau3_pRank_eq_one
      have hAr : A ∈ elemAbelianOfRank G p (pRank ↥M p) := by
        rw [hr1, mem_elemAbelianOfRank]
        exact ⟨hAelem, by rw [hAcard, pow_one]⟩
      -- Lemma 14.1: `M_σ ⊓ C(A) = ⊥`; antitonicity `C(e) ≤ C(f) = C(A)` lifts it to `e`.
      obtain ⟨_, hCA, _⟩ :=
        S14.msigma_structure_of_notMem_sigma_kappa hG hM hpπ hpσ hpκ hAr hAM
      -- `C(A) = C(f)` and `C(e) ≤ C(f)`: centralizing `e` centralizes its power `f = e^k`.
      have hCfA : Subgroup.centralizer (A : Set G) = Subgroup.centralizer ({f} : Set G) := by
        rw [hAdef, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      have hCef : Subgroup.centralizer ({e} : Set G) ≤ Subgroup.centralizer ({f} : Set G) := by
        intro x hx
        rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
        rw [hfdef]
        exact (show Commute x e from hx).pow_right _
      rw [eq_bot_iff, ← hCA, hCfA]
      exact inf_le_inf_left _ hCef
    -- Theorem 12.12(a): abelian normal `A₀ ≤ U` swallowing every `C_U(x)`.
    obtain ⟨⟨A₀, hA₀le, hA₀ab, _hA₀norm, hA₀swallow⟩, _⟩ :=
      frobenius_factorization_of_regular hG hsetup hreg
    -- `centralizerGeneratedBySigma M U ≤ A₀`, so abelian.
    refine isMulCommutative_of_le hA₀ab ?_
    rw [centralizerGeneratedBySigma]
    refine sSup_le ?_
    rintro C ⟨x, hx, rfl⟩
    obtain ⟨hxMσ, hxne⟩ := hx
    exact hA₀swallow x hxMσ (by simpa using hxne)
  · -- **Case `K ≠ ⊥`**: `U` is abelian; the generated subgroup is `≤ U`.
    obtain ⟨_, hUab⟩ := typeP_hall_derived_eq_and_abelian hG hM hKM hUM hKbot hK hU
    refine isMulCommutative_of_le hUab ?_
    rw [centralizerGeneratedBySigma]
    refine sSup_le ?_
    rintro C ⟨x, _, rfl⟩
    exact inf_le_left

/-- **`E`-setup-free Frobenius packaging** (generalizes `isFrobeniusGroup_of_regular`,
`S12_Theorem1212`): for a maximal `M` and a nonidentity `U₀ ≤ M` with `M_σ ⊓ U₀ = 1` acting
regularly on `M_σ` (`M_σ ⊓ C_G(a) = 1` for `a ∈ U₀#`), the product `M_σ U₀` is a Frobenius group
with kernel `M_σ` and complement `U₀`.  The proof of `isFrobeniusGroup_of_regular` only uses the
`SubgroupESetup` via `h.mem_maximal`, `h.E_le` and `h.E_compl_inf`; here those become the explicit
`hM`, `hU0M` and `hU0inf`, so the `K ≠ ⊥` (type-`P`) case of Lemma 15.1(e) can reuse it with
`U₀ ≤ U ≤ M` without aligning a `σ`-complement. -/
theorem isFrobeniusGroup_of_regular_le_maximal [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M U0 : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hU0M : U0 ≤ M) (hU0ne : U0 ≠ ⊥)
    (hU0inf : OddOrder.BG.Ch3.S10.Msigma M ⊓ U0 = ⊥)
    (hreg₀ : ∀ a ∈ U0, a ≠ 1 →
      OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({a} : Set G) = ⊥) :
    OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(OddOrder.BG.Ch3.S10.Msigma M ⊔ U0)
      ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf (OddOrder.BG.Ch3.S10.Msigma M ⊔ U0))
      (U0.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M ⊔ U0)) := by
  have hMσne : OddOrder.BG.Ch3.S10.Msigma M ≠ ⊥ := OddOrder.BG.Ch3.S10.Msigma_ne_bot hG hM
  have hMσM_normal : ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).Normal := by
    rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
  have hM_le_N : M ≤ Subgroup.normalizer ((OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (OddOrder.BG.Ch3.S10.Msigma_le M)).mp hMσM_normal
  have hsup_le_M : OddOrder.BG.Ch3.S10.Msigma M ⊔ U0 ≤ M :=
    sup_le (OddOrder.BG.Ch3.S10.Msigma_le M) hU0M
  have hsup_le_N : OddOrder.BG.Ch3.S10.Msigma M ⊔ U0 ≤
      Subgroup.normalizer ((OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) : Set G) :=
    hsup_le_M.trans hM_le_N
  refine
    { isNormal := (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hsup_le_N
      isComplement := ?_
      ne_bot_kernel := ?_
      ne_bot_complement := ?_
      conj_frobenius := ?_ }
  · have : ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf
        (OddOrder.BG.Ch3.S10.Msigma M ⊔ U0)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hsup_le_N
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
    · rw [disjoint_iff]
      have hinf : (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf
            (OddOrder.BG.Ch3.S10.Msigma M ⊔ U0) ⊓
            U0.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M ⊔ U0)
          = (OddOrder.BG.Ch3.S10.Msigma M ⊓ U0).subgroupOf
            (OddOrder.BG.Ch3.S10.Msigma M ⊔ U0) := rfl
      rw [hinf, hU0inf, Subgroup.bot_subgroupOf]
    · rw [← Subgroup.normal_mul, ← Subgroup.subgroupOf_sup le_sup_left le_sup_right,
        Subgroup.subgroupOf_self, Subgroup.coe_top]
  · rw [ne_eq, Subgroup.subgroupOf_eq_bot]
    exact fun hd => hMσne (hd.eq_bot_of_le le_sup_left)
  · rw [ne_eq, Subgroup.subgroupOf_eq_bot]
    exact fun hd => hU0ne (hd.eq_bot_of_le le_sup_right)
  · intro a ha hane n hn hne hfix
    have ha_mem : (a : G) ∈ U0 := Subgroup.mem_subgroupOf.mp ha
    have hn_mem : (n : G) ∈ OddOrder.BG.Ch3.S10.Msigma M := Subgroup.mem_subgroupOf.mp hn
    have ha_ne : (a : G) ≠ 1 := fun hc => hane (by exact_mod_cast hc)
    have hfixG : (a : G) * (n : G) * (a : G)⁻¹ = (n : G) := by
      have := Subtype.ext_iff.mp hfix
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this
    have hncent : (n : G) ∈ Subgroup.centralizer ({(a : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      rw [Set.mem_singleton_iff] at hm; subst hm
      exact mul_inv_eq_iff_eq_mul.mp hfixG
    have hmem : (n : G) ∈ OddOrder.BG.Ch3.S10.Msigma M ⊓
        Subgroup.centralizer ({(a : G)} : Set G) :=
      Subgroup.mem_inf.mpr ⟨hn_mem, hncent⟩
    rw [hreg₀ (a : G) ha_mem ha_ne, Subgroup.mem_bot] at hmem
    exact hne (by exact_mod_cast hmem)

/-- **Frobenius-factor assembly engine** (BG Lemma 15.1(e), `K ≠ ⊥` core).  Given an abelian
`U ≤ M` with `M_σ ⊓ U = 1`, and for **each** prime `p ∣ |U|` a `p`-subgroup `Z_p ≤ U` that
realizes the `p`-part of `exp U` (`v_p(exp U) ≤ v_p(exp Z_p)`) and acts regularly on `M_σ`, the
internal direct product `U₀ = ⊔_p Z_p` has `exp U₀ = exp U` and `U₀ M_σ` is a Frobenius group with
kernel `M_σ` and complement `U₀`.

Because `U` is abelian, every internal-direct-product hypothesis is automatic (`U ≤ N_G(Z_p)` from
`U ≤ C_G(Z_p)`); regularity propagates from prime-order elements (each lands in one `Z_p` by
`mem_Z_of_orderOf_prime_mem`); the exponent is matched prime-by-prime
(`exponent_eq_of_forall_factorization_le`); and `isFrobeniusGroup_of_regular_le_maximal` packages
the result.  This isolates the type-`P` content of Lemma 15.1(e) to constructing the per-prime
`Z_p` (`τ₁∪τ₃`: cyclic `Sylow_p(U)`; `τ₂`: a regular cyclic line). -/
theorem frobenius_factor_of_regular_components [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M U : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hUM : U ≤ M) (hUne : U ≠ ⊥)
    (hUab : IsMulCommutative ↥U)
    (hUinf : OddOrder.BG.Ch3.S10.Msigma M ⊓ U = ⊥)
    (hcomp : ∀ p ∈ (Nat.card ↥U).primeFactors, ∃ Z : Subgroup G,
      Z ≤ U ∧ IsPGroup p ↥Z ∧
        (Monoid.exponent ↥U).factorization p ≤ (Monoid.exponent ↥Z).factorization p ∧
        (∀ z ∈ Z, z ≠ 1 →
          OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({z} : Set G) = ⊥)) :
    ∃ U0 : Subgroup G, U0 ≤ U ∧ Monoid.exponent ↥U0 = Monoid.exponent ↥U ∧
      OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(U0 ⊔ OddOrder.BG.Ch3.S10.Msigma M)
        ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf (U0 ⊔ OddOrder.BG.Ch3.S10.Msigma M))
        (U0.subgroupOf (U0 ⊔ OddOrder.BG.Ch3.S10.Msigma M)) := by
  classical
  set T := (Nat.card ↥U).primeFactors with hTdef
  choose! Z hZU hZpg hZexp hZreg using hcomp
  set U0 : Subgroup G := T.sup Z with hU0def
  have hTp : ∀ p ∈ T, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  -- `U` abelian ⟹ `U ≤ C_G(U) ≤ C_G(Z_p) ≤ N_G(Z_p)`.
  have hUcentU : U ≤ Subgroup.centralizer (U : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hUab
  have hUnorm : ∀ p ∈ T, U ≤ Subgroup.normalizer ((Z p : Subgroup G) : Set G) := fun p hp =>
    ((hUcentU.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (hZU p hp)))).trans
      (Subgroup.centralizer_le_normalizer _))
  have hU0U : U0 ≤ U := Finset.sup_le hZU
  have hU0inf : OddOrder.BG.Ch3.S10.Msigma M ⊓ U0 = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_left _ hU0U).trans hUinf.le)
  -- **Exponent**: `exp U₀ = exp U`.
  have hexp : Monoid.exponent ↥U0 = Monoid.exponent ↥U := by
    refine exponent_eq_of_forall_factorization_le hU0U fun r hrp => ?_
    have : Fact r.Prime := ⟨hrp⟩
    by_cases hrT : r ∈ T
    · obtain ⟨g, hg⟩ := hrp.exists_orderOf_eq_pow_factorization_exponent ↥(Z r)
      have hZrU0 : Z r ≤ U0 := Finset.le_sup hrT
      refine ⟨Subgroup.inclusion hZrU0 g, ?_⟩
      rw [orderOf_injective (Subgroup.inclusion hZrU0) (Subgroup.inclusion_injective _) g, hg,
        Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, Nat.Prime.factorization_self hrp,
        mul_one]
      exact hZexp r hrT
    · have hrnU : ¬ r ∣ Nat.card ↥U := fun hd =>
        hrT (Nat.mem_primeFactors.mpr ⟨hrp, hd, Nat.card_pos.ne'⟩)
      have h0 : (Monoid.exponent ↥U).factorization r = 0 := by
        rw [Nat.factorization_eq_zero_iff]
        exact Or.inr (Or.inl fun hd => hrnU (hd.trans Group.exponent_dvd_nat_card))
      exact ⟨1, by rw [h0]; exact Nat.zero_le _⟩
  have hU0ne : U0 ≠ ⊥ := by
    intro hbot
    refine hUne (Subgroup.eq_bot_iff_forall _ |>.mpr fun x hx => ?_)
    have : Subsingleton ↥U :=
      Monoid.exp_eq_one_iff.mp (by rw [← hexp, hbot]; exact Monoid.exp_eq_one_of_subsingleton)
    have hx1 : (⟨x, hx⟩ : ↥U) = 1 := Subsingleton.elim _ _
    simpa using Subtype.ext_iff.mp hx1
  -- **Regularity**: every nonidentity element of `U₀` is regular on `M_σ`.
  have hU0reg : ∀ a ∈ U0, a ≠ 1 →
      OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({a} : Set G) = ⊥ := by
    refine inf_centralizer_eq_bot_of_forall_prime_order ?_
    intro a haU0 harp
    have haU : a ∈ U := hU0U haU0
    have hrT : orderOf a ∈ T := Nat.mem_primeFactors.mpr
      ⟨harp, (Subgroup.orderOf_coe (⟨a, haU⟩ : ↥U)) ▸ orderOf_dvd_natCard _, Nat.card_pos.ne'⟩
    have haZr : a ∈ Z (orderOf a) :=
      mem_Z_of_orderOf_prime_mem T Z hTp hZU hUnorm hZpg hrT haU0 rfl
    have hane : a ≠ 1 := fun hc => by
      rw [hc, orderOf_one] at harp; exact harp.ne_one rfl
    exact hZreg (orderOf a) hrT a haZr hane
  refine ⟨U0, hU0U, hexp, ?_⟩
  rw [show U0 ⊔ OddOrder.BG.Ch3.S10.Msigma M
      = OddOrder.BG.Ch3.S10.Msigma M ⊔ U0 from sup_comm _ _]
  exact isFrobeniusGroup_of_regular_le_maximal hG hM (hU0U.trans hUM) hU0ne hU0inf hU0reg

/-- **Per-prime regular component** for the type-`P` Frobenius factor (BG Lemma 15.1(e), `K ≠ ⊥`):
for each prime `p ∣ |U|` (with `U` the abelian `(κ∪σ)'`-Hall of a maximal `M`), `Sylow_p(U)`
contains a `p`-subgroup `Z` realizing the `p`-part of `exp U` and acting regularly on `M_σ`.  This
is the single mathematical kernel of the `K ≠ ⊥` branch; the assembly into `U₀ = ⊔_p Z_p` is
`frobenius_factor_of_regular_components`.

Proof (BG mmd 4178 + Theorem 12.12 `C_E(S)=E` argument), to be supplied:

* `p ∈ τ₁(M) ∪ τ₃(M)` (`r_p(M) = 1`): `Z = Sylow_p(U)` is cyclic; regularity is Lemma 14.1
  (`Ω₁(Z) ∈ ℰ_p¹(M)`, `p ∉ σ ∪ κ`), the same discharge as the `K = ⊥` branch.
* `p ∈ τ₂(M)` (`r_p(M) = 2`): since `U` is abelian, `C_U(Sylow_p(U)) = U`, so we are always in the
  "easy" `C_E(S) = E` case.  Abelian `Sylow_p(G)`: `Sylow_p(U) = Sylow_p(G) ≤ M` (full-Sylow-in-`G`
  via `centralizer_le_E_of_tau2`), and `exists_cyclic_Enormal_regular_of_CES_eq` supplies the
  regular cyclic line.  Nonabelian `Sylow_p(G)`: `Sylow_p(U) = C_S(A) = A₀ × Z` (Theorem 12.7,
  mmd 3237) and `Z` is the regular cyclic factor of full exponent (`A₀` has order `p`). -/
theorem typeP_hall_regular_component_at_prime [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M U : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hUM : U ≤ M) (hUab : IsMulCommutative ↥U)
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {p : ℕ} (hp : p ∈ (Nat.card ↥U).primeFactors) :
    ∃ Z : Subgroup G, Z ≤ U ∧ IsPGroup p ↥Z ∧
      (Monoid.exponent ↥U).factorization p ≤ (Monoid.exponent ↥Z).factorization p ∧
      (∀ z ∈ Z, z ≠ 1 →
        OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({z} : Set G) = ⊥) := by
  classical
  have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
  -- `p ∈ π(U) ⟹ p ∉ σ(M) ∪ κ(M)` (U is a `(κ∪σ)'`-Hall).
  have hpcompl : p ∈ (S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ :=
    hU.1 p (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv])
  have hpσ : p ∉ OddOrder.BG.Ch3.S10.sigma M := fun h => hpcompl (Set.mem_union_right _ h)
  have hpκ : p ∉ S14.kappa M := fun h => hpcompl (Set.mem_union_left _ h)
  have hpdvdM : p ∣ Nat.card ↥M :=
    (Nat.dvd_of_mem_primeFactors hp).trans (Subgroup.card_dvd_of_le hUM)
  have hpπ : p ∈ S14.piSet M := Nat.mem_primeFactors.mpr ⟨Fact.out, hpdvdM, Nat.card_pos.ne'⟩
  -- **Linchpin**: an `E`-setup of `M` with `U ≤ E` (`U` is a `σ'`-subgroup).
  have hUpi : Subgroup.IsPiSubgroup ((OddOrder.BG.Ch3.S10.sigma M)ᶜ) U := by
    intro q hq
    exact fun hqσ => (hU.1 q (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv]))
      (Set.mem_union_right _ hqσ)
  obtain ⟨E, E₁, E₂, E₃, hsetup, hUE, _hEpi⟩ :=
    exists_subgroupESetup_with_le hG hM hUM hUpi
  have hpE : p ∈ (Nat.card ↥E).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Fact.out,
      (Nat.dvd_of_mem_primeFactors hp).trans (Subgroup.card_dvd_of_le hUE), Nat.card_pos.ne'⟩
  by_cases hpτ2 : p ∈ tau2 M
  · -- **τ₂ case** (`r_p(M) = 2`): the regular cyclic line in `Sylow_p(U)`.
    by_cases habel : ∀ Sp : Sylow p G, IsMulCommutative ↥(Sp : Subgroup G)
    · -- **abelian `Sylow_p(G)`**: `Sylow_p(U)` is a full `G`-Sylow, so the trimmed `C_E(S)=E`
      -- construction (`exists_regular_cyclic_in_abelianSylow_tau2`) supplies `Z ≤ Sylow_p(U) ≤ U`.
      -- `ν_p(|U|) = ν_p(|M|)` (`U` is the `(κ∪σ)'`-Hall, `p ∈ (κ∪σ)'`).
      have hUMfact : (Nat.card ↥U).factorization p = (Nat.card ↥M).factorization p := by
        have hmul := Subgroup.card_mul_index (U.subgroupOf M)
        have hcard_eqUM : Nat.card ↥(U.subgroupOf M) = Nat.card ↥U :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv
        have hidx : ((U.subgroupOf M).index).factorization p = 0 := by
          rw [Nat.factorization_eq_zero_iff]
          exact Or.inr (Or.inl fun hd => (hU.2 p (Nat.mem_primeFactors.mpr
            ⟨Fact.out, hd, Subgroup.index_ne_zero_of_finite⟩)) hpcompl)
        have hh := congrArg (fun n => n.factorization p) hmul
        simp only [Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
          Finsupp.add_apply, hidx, add_zero] at hh
        rw [hcard_eqUM] at hh; exact hh
      -- `SUG = Sylow_p(U)` pushed into `G`.
      obtain ⟨SU⟩ : Nonempty (Sylow p ↥U) := inferInstance
      set SUG : Subgroup G := (SU : Subgroup ↥U).map U.subtype with hSUGdef
      have hSUG_U : SUG ≤ U := Subgroup.map_subtype_le _
      have hSUG_M : SUG ≤ M := hSUG_U.trans hUM
      have hSUGcard : Nat.card ↥SUG = p ^ (Nat.card ↥U).factorization p := by
        rw [hSUGdef, Subgroup.card_map_of_injective U.subtype_injective, SU.card_eq_multiplicity]
      have hSUGcardM : Nat.card ↥SUG = p ^ (Nat.card ↥M).factorization p := by
        rw [hSUGcard, hUMfact]
      have hSUGsubM_card : Nat.card ↥(SUG.subgroupOf M) = p ^ (Nat.card ↥M).factorization p := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSUG_M).toEquiv]; exact hSUGcardM
      set SM : Sylow p ↥M := Sylow.ofCard (SUG.subgroupOf M) hSUGsubM_card with hSMdef
      have hpRankSUG : 2 ≤ pRank ↥SUG p := by
        have e1 := pRank_sylow_eq SM
        rw [hSMdef, Sylow.coe_ofCard] at e1
        have e2 : pRank ↥(SUG.subgroupOf M) p = pRank ↥SUG p :=
          le_antisymm
            (pRank_le_of_injective (f := (Subgroup.subgroupOfEquivOfLe hSUG_M).toMonoidHom)
              (Subgroup.subgroupOfEquivOfLe hSUG_M).injective)
            (pRank_le_of_injective (f := (Subgroup.subgroupOfEquivOfLe hSUG_M).symm.toMonoidHom)
              (Subgroup.subgroupOfEquivOfLe hSUG_M).symm.injective)
        have hr2 : pRank ↥M p = 2 := hpτ2.2
        omega
      -- a rank-2 `A ≤ SUG` (de-private `S12_Proposition1215`).
      obtain ⟨A, hA, hASUG⟩ := exists_mem_elemAbelianOfRank_two_le_of_two_le_pRank
        (Fact.out : p.Prime) hpRankSUG
      have hAE : A ≤ E := hASUG.trans (hSUG_U.trans hUE)
      -- **full `G`-Sylow**: `ν_p(|M|) = ν_p(|G|)` via abelian `S' ⊇ A` with `S' ≤ C_G(A) ≤ E ≤ M`.
      obtain ⟨S', hAS'⟩ := hA.1.isPGroup.exists_le_sylow
      have hS'M : (S' : Subgroup G) ≤ M :=
        ((le_centralizer_of_le_of_le (habel S') le_rfl hAS').trans
          (centralizer_le_E_of_tau2 hG hsetup hpτ2 hA hAE).1).trans hsetup.E_le
      have hMG : (Nat.card ↥M).factorization p ≤ (Nat.card G).factorization p :=
        (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
          (Subgroup.card_subgroup_dvd_card M) p
      have hGM : (Nat.card G).factorization p ≤ (Nat.card ↥M).factorization p := by
        have hdvd : Nat.card ↥(S' : Subgroup G) ∣ Nat.card ↥M := Subgroup.card_dvd_of_le hS'M
        rw [S'.card_eq_multiplicity] at hdvd
        exact (Nat.Prime.pow_dvd_iff_le_factorization Fact.out Nat.card_pos.ne').mp hdvd
      have hfull : (Nat.card ↥M).factorization p = (Nat.card G).factorization p :=
        le_antisymm hMG hGM
      have hSUGfull : Nat.card ↥SUG = p ^ (Nat.card G).factorization p := by
        rw [hSUGcardM, hfull]
      set SG : Sylow p G := Sylow.ofCard SUG hSUGfull with hSGdef
      have hSGcoe : (SG : Subgroup G) = SUG := by rw [hSGdef, Sylow.coe_ofCard]
      have hSGab : IsMulCommutative ↥(SG : Subgroup G) := by
        rw [hSGcoe]
        exact Subgroup.le_centralizer_iff_isMulCommutative.mp
          (hSUG_U.trans ((Subgroup.le_centralizer_iff_isMulCommutative.mpr hUab).trans
            (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hSUG_U))))
      obtain ⟨Z, hZS, _hZcyc, _hZne, hZexp, hZreg⟩ :=
        exists_regular_cyclic_in_abelianSylow_tau2 hG hsetup hpτ2 hA hAE
          (hSGcoe ▸ hASUG) (hSGcoe ▸ hSUG_M) hSGab
      have hZSUG : Z ≤ SUG := hSGcoe ▸ hZS
      refine ⟨Z, hZSUG.trans hSUG_U, (SG.isPGroup'.to_le hZS), ?_, hZreg⟩
      -- exponent: `exp Z = exp SUG`, and `ν_p(exp U) ≤ ν_p(exp SUG)` (`Sylow_p(U)`).
      have hSUGsubU : SUG.subgroupOf U = (SU : Subgroup ↥U) := by
        rw [hSUGdef, Subgroup.subgroupOf,
          Subgroup.comap_map_eq_self_of_injective U.subtype_injective]
      have hSUGsubU_card : Nat.card ↥(SUG.subgroupOf U) = p ^ (Nat.card ↥U).factorization p := by
        rw [hSUGsubU, SU.card_eq_multiplicity]
      have hZexp' : Monoid.exponent ↥Z = Monoid.exponent ↥SUG := by rw [hZexp, hSGcoe]
      rw [hZexp']
      exact factorization_exponent_le_of_sylow hSUG_U hSUGsubU_card
    · -- **nonabelian `Sylow_p(G)`**: `Sylow_p(U) = C_{S'}(A) = A₀ ⊔ Z` (Lemma 10.13); `Z` is the
      -- regular cyclic factor (`Ω₁(Z) ≠ A₀`, regular by the canonical line's clause (c)).
      have hUMfact : (Nat.card ↥U).factorization p = (Nat.card ↥M).factorization p := by
        have hmul := Subgroup.card_mul_index (U.subgroupOf M)
        have hcard_eqUM : Nat.card ↥(U.subgroupOf M) = Nat.card ↥U :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv
        have hidx : ((U.subgroupOf M).index).factorization p = 0 := by
          rw [Nat.factorization_eq_zero_iff]
          exact Or.inr (Or.inl fun hd => (hU.2 p (Nat.mem_primeFactors.mpr
            ⟨Fact.out, hd, Subgroup.index_ne_zero_of_finite⟩)) hpcompl)
        have hh := congrArg (fun n => n.factorization p) hmul
        simp only [Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
          Finsupp.add_apply, hidx, add_zero] at hh
        rw [hcard_eqUM] at hh; exact hh
      obtain ⟨SU⟩ : Nonempty (Sylow p ↥U) := inferInstance
      set SUG : Subgroup G := (SU : Subgroup ↥U).map U.subtype with hSUGdef
      have hSUG_U : SUG ≤ U := Subgroup.map_subtype_le _
      have hSUG_M : SUG ≤ M := hSUG_U.trans hUM
      have hSUGcard : Nat.card ↥SUG = p ^ (Nat.card ↥U).factorization p := by
        rw [hSUGdef, Subgroup.card_map_of_injective U.subtype_injective, SU.card_eq_multiplicity]
      have hSUGcardM : Nat.card ↥SUG = p ^ (Nat.card ↥M).factorization p := by
        rw [hSUGcard, hUMfact]
      have hSUGpg : IsPGroup p ↥SUG := IsPGroup.of_card hSUGcard
      have hSUGsubM_card : Nat.card ↥(SUG.subgroupOf M) = p ^ (Nat.card ↥M).factorization p := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSUG_M).toEquiv]; exact hSUGcardM
      set SM : Sylow p ↥M := Sylow.ofCard (SUG.subgroupOf M) hSUGsubM_card with hSMdef
      have hpRankSUG : 2 ≤ pRank ↥SUG p := by
        have e1 := pRank_sylow_eq SM
        rw [hSMdef, Sylow.coe_ofCard] at e1
        have e2 : pRank ↥(SUG.subgroupOf M) p = pRank ↥SUG p :=
          le_antisymm
            (pRank_le_of_injective (f := (Subgroup.subgroupOfEquivOfLe hSUG_M).toMonoidHom)
              (Subgroup.subgroupOfEquivOfLe hSUG_M).injective)
            (pRank_le_of_injective (f := (Subgroup.subgroupOfEquivOfLe hSUG_M).symm.toMonoidHom)
              (Subgroup.subgroupOfEquivOfLe hSUG_M).symm.injective)
        have hr2 : pRank ↥M p = 2 := hpτ2.2
        omega
      obtain ⟨A, hA, hASUG⟩ := exists_mem_elemAbelianOfRank_two_le_of_two_le_pRank
        (Fact.out : p.Prime) hpRankSUG
      have hAE : A ≤ E := hASUG.trans (hSUG_U.trans hUE)
      have hAM : A ≤ M := hASUG.trans hSUG_M
      have hSUGab : IsMulCommutative ↥SUG :=
        Subgroup.le_centralizer_iff_isMulCommutative.mp
          (hSUG_U.trans ((Subgroup.le_centralizer_iff_isMulCommutative.mpr hUab).trans
            (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hSUG_U))))
      have hAmax : IsMaximalElementaryAbelian p A :=
        (isMaximalElementaryAbelian_of_mem_tau2 hG hM Fact.out hpτ2 hAM hA).1
      -- nonabelian Sylow `S' ⊇ SUG`.
      push Not at habel
      obtain ⟨S', hSUGS'⟩ := hSUGpg.exists_le_sylow
      have hAS' : A ≤ (S' : Subgroup G) := hASUG.trans hSUGS'
      have hS'nonab : ¬ IsMulCommutative ↥(S' : Subgroup G) := by
        obtain ⟨S₀, hS₀⟩ := habel
        obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S₀ S'
        intro hab
        apply hS₀
        have hcoe : (S₀ : Subgroup G) = MulAut.conj g⁻¹ • (S' : Subgroup G) := by
          rw [← hg, Sylow.coe_subgroup_smul, ← mul_smul, ← map_mul, inv_mul_cancel,
            map_one, one_smul]
        rw [hcoe, mulAut_smul_eq_map]
        exact OddOrder.BG.Ch3.S11.isMulCommutative_of_mulEquiv
          (Subgroup.equivMapOfInjective _ _ (MulAut.conj g⁻¹).injective) hab
      -- `C_G(A) ⊓ S' = SUG`.
      have hSUG_le_C : SUG ≤ Subgroup.centralizer (A : Set G) ⊓ (S' : Subgroup G) :=
        le_inf (le_centralizer_of_le_of_le hSUGab le_rfl hASUG) hSUGS'
      have hC_le_M : Subgroup.centralizer (A : Set G) ⊓ (S' : Subgroup G) ≤ M :=
        (inf_le_left.trans (centralizer_le_E_of_tau2 hG hsetup hpτ2 hA hAE).1).trans hsetup.E_le
      have hCcard_le : Nat.card ↥(Subgroup.centralizer (A : Set G) ⊓ (S' : Subgroup G)) ≤
          Nat.card ↥SUG := by
        rw [hSUGcardM]
        obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp (S'.isPGroup'.to_le inf_le_right)
        rw [hk]
        exact Nat.pow_le_pow_right (Fact.out : p.Prime).one_lt.le
          ((Nat.Prime.pow_dvd_iff_le_factorization Fact.out Nat.card_pos.ne').mp
            (hk ▸ Subgroup.card_dvd_of_le hC_le_M))
      have hCeqSUG : Subgroup.centralizer (A : Set G) ⊓ (S' : Subgroup G) = SUG :=
        (Subgroup.eq_of_le_of_card_ge hSUG_le_C hCcard_le).symm
      -- canonical line `A₀` + clause (c).
      obtain ⟨A₀, _hA₀eq, hA₀card, hA₀A, hMσA₀, hcReg, _hA₀max⟩ :=
        exists_canonical_line_of_nonabelianSylow hG hsetup hpτ2 hA hAE habel
      have hMσ_ne : OddOrder.BG.Ch3.S10.Msigma M ≠ ⊥ := OddOrder.BG.Ch3.S10.Msigma_ne_bot hG hM
      have hA₀mem : A₀ ∈ elemAbelianOfRank G p 1 :=
        ⟨Subgroup.IsElementaryAbelian.of_card_prime hA₀card, by rw [hA₀card, pow_one]⟩
      have hA₀C : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (A₀ : Set G) ≠ ⊥ := by
        rw [inf_eq_left.mpr hMσA₀]; exact hMσ_ne
      have hM_single : maximalSubgroupsContaining (Subgroup.centralizer (A₀ : Set G)) = {M} :=
        maximalContaining_centralizer_line_eq_singleton hG hsetup hpτ2 hA hAE hA₀mem hA₀A hA₀C
      have hCA₀_le_M : Subgroup.centralizer (A₀ : Set G) ≤ M := by
        have hlt : Subgroup.centralizer (A₀ : Set G) < ⊤ :=
          lt_of_le_of_lt (Subgroup.centralizer_le_normalizer _)
            (normalizer_lt_top_of_le_of_ne_bot hG hM (hA₀A.trans hAM)
              (ne_bot_of_mem_elemAbelianOfRank_one hA₀mem))
        obtain ⟨Mst, hco, hle⟩ := (eq_top_or_exists_le_coatom _).resolve_left hlt.ne
        have hmem : Mst ∈ maximalSubgroupsContaining (Subgroup.centralizer (A₀ : Set G)) :=
          mem_maximalSubgroupsContaining.mpr ⟨hco, hle⟩
        rw [hM_single, Set.mem_singleton_iff] at hmem
        exact hmem ▸ hle
      -- `S' ⊄ M` (nonabelian, but `Sylow_p(M) = SUG` abelian).
      have hS'_not_le_M : ¬ ((S' : Subgroup G) ≤ M) := by
        intro hS'M
        have hcardle : Nat.card ↥(S' : Subgroup G) ≤ Nat.card ↥SUG := by
          rw [hSUGcardM, S'.card_eq_multiplicity]
          exact Nat.pow_le_pow_right (Fact.out : p.Prime).one_lt.le
            ((Nat.Prime.pow_dvd_iff_le_factorization Fact.out Nat.card_pos.ne').mp
              (S'.card_eq_multiplicity ▸ Subgroup.card_dvd_of_le hS'M))
        exact hS'nonab ((Subgroup.eq_of_le_of_card_ge hSUGS' hcardle) ▸ hSUGab)
      -- `A₀ ≠ Ω₁(Z(S'))`.
      set Z₀' : Subgroup G := OddOrder.BG.Ch3.S10.omega1CenterInG (S' : Subgroup G) p with hZ₀'def
      have hS'_cent_Z₀ : (S' : Subgroup G) ≤ Subgroup.centralizer (Z₀' : Set G) := by
        intro q hq
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [SetLike.mem_coe, hZ₀'def, OddOrder.BG.Ch3.S10.omega1CenterInG, Subgroup.mem_map] at hz
        obtain ⟨z', hz', rfl⟩ := hz
        have hz'c : z' ∈ Subgroup.center ↥(S' : Subgroup G) := (mem_omega1OfAbelian.mp hz').1
        exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz'c ⟨q, hq⟩)).symm
      have hA₀_ne_Z₀ : A₀ ≠ Z₀' := by
        rintro rfl
        exact hS'_not_le_M (hS'_cent_Z₀.trans hCA₀_le_M)
      -- Lemma 10.13: `C_{S'}(A) = A₀ ⊔ Z` with `Z` cyclic, `A₀ ⊓ Z = ⊥`.
      have hpG : p ∈ (Nat.card G).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨Fact.out,
          (hA.2 ▸ dvd_pow_self p two_ne_zero).trans (Subgroup.card_subgroup_dvd_card A),
          Nat.card_pos.ne'⟩
      obtain ⟨Z, _hZS', hZcyc, _hZ₀Z, hA₀Z, hCdecomp⟩ :=
        (OddOrder.BG.Ch3.S10.nonabelian_pSubgroup_rankTwo_elemAbelian_structure hG hpG hA hAmax
          S'.isPGroup' hS'nonab hAS' ⟨hA₀mem, hA₀A⟩ hA₀_ne_Z₀).2.1
      have hSUGdecomp : SUG = A₀ ⊔ Z := hCeqSUG ▸ hCdecomp
      have hZSUG : Z ≤ SUG := hSUGdecomp ▸ le_sup_right
      refine ⟨Z, hZSUG.trans hSUG_U, hSUGpg.to_le hZSUG, ?_, ?_⟩
      · -- exponent: `ν_p(exp U) ≤ ν_p(exp SUG) ≤ ν_p(exp Z)` (`exp SUG ∣ exp Z`,
        -- since `SUG = A₀ ⊔ Z` with `|A₀| = p ∣ exp Z`).
        have hSUGsubU_card : Nat.card ↥(SUG.subgroupOf U) = p ^ (Nat.card ↥U).factorization p := by
          rw [show SUG.subgroupOf U = (SU : Subgroup ↥U) from by
            rw [hSUGdef, Subgroup.subgroupOf,
              Subgroup.comap_map_eq_self_of_injective U.subtype_injective], SU.card_eq_multiplicity]
        refine le_trans (factorization_exponent_le_of_sylow hSUG_U hSUGsubU_card) ?_
        have := hSUGab
        obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp (hSUGpg.to_le hZSUG)
        have hA₀NZ : A₀ ≤ Subgroup.normalizer (Z : Set G) :=
          (le_centralizer_of_le_of_le hSUGab (hA₀A.trans hASUG) hZSUG).trans
            (Subgroup.centralizer_le_normalizer _)
        have hcardSUG : Nat.card ↥SUG = p ^ (k + 1) := by
          rw [hSUGdecomp, card_sup_eq_mul_of_le_normalizer_of_disjoint hA₀NZ hA₀Z, hA₀card, hk,
            ← pow_succ']
        -- `SUG` is not cyclic (it contains the rank-2 elementary abelian `A`), so
        -- `exp SUG < |SUG|`.
        have hSUGnotcyc : ¬ IsCyclic ↥SUG := by
          intro hcyc
          have := hcyc
          have hAcyc : IsCyclic ↥A :=
            isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hASUG).toMonoidHom
              (Subgroup.subgroupOfEquivOfLe hASUG).surjective
          have hdvdp : Monoid.exponent ↥A ∣ p :=
            Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => hA.1.2 x)
          rw [hAcyc.exponent_eq_card, hA.2] at hdvdp
          exact absurd (Nat.le_of_dvd (Fact.out : p.Prime).pos hdvdp)
            (by nlinarith [(Fact.out : p.Prime).two_le])
        have hexpSUGne : Monoid.exponent ↥SUG ≠ Nat.card ↥SUG :=
          fun heq => hSUGnotcyc (IsCyclic.of_exponent_eq_card heq)
        obtain ⟨m, hm_le, hm⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp
          (hcardSUG ▸ Group.exponent_dvd_nat_card)
        have hmk : m ≤ k := by
          by_contra hc
          push Not at hc
          exact hexpSUGne (by rw [hm, show m = k + 1 by omega, hcardSUG])
        have hfp : ∀ n, (p ^ n).factorization p = n := fun n => by
          rw [Nat.factorization_pow, Finsupp.smul_apply,
            Nat.Prime.factorization_self (Fact.out : p.Prime), smul_eq_mul, mul_one]
        rw [hm, hZcyc.exponent_eq_card, hk, hfp, hfp]
        exact hmk
      · -- regularity: every prime-order `z ∈ Z` generates a line `⟨z⟩ ≠ A₀` (`A₀ ⊓ Z = ⊥`),
        -- which clause (c) shows is regular on `M_σ`.
        refine inf_centralizer_eq_bot_of_forall_prime_order ?_
        intro z hzZ hzprime
        have hordz : orderOf z = p := by
          obtain ⟨j, hj⟩ := (IsPGroup.iff_card).mp (hSUGpg.to_le hZSUG)
          have hqdvd : orderOf z ∣ p ^ j := by
            have h := (Subgroup.orderOf_coe (⟨z, hzZ⟩ : ↥Z)) ▸ orderOf_dvd_natCard (⟨z, hzZ⟩ : ↥Z)
            rwa [hj] at h
          exact (Nat.prime_dvd_prime_iff_eq hzprime Fact.out).mp (hzprime.dvd_of_dvd_pow hqdvd)
        set X : Subgroup G := Subgroup.zpowers z with hXdef
        have hXcard : Nat.card ↥X = p := by rw [hXdef, Nat.card_zpowers]; exact hordz
        have hXmem : X ∈ elemAbelianOfRank G p 1 :=
          ⟨Subgroup.IsElementaryAbelian.of_card_prime hXcard, by rw [hXcard, pow_one]⟩
        have hXZ : X ≤ Z := by rw [hXdef, Subgroup.zpowers_le]; exact hzZ
        have hXE : X ≤ E := (hXZ.trans hZSUG).trans (hSUG_U.trans hUE)
        have hXneA₀ : X ≠ A₀ := by
          intro he
          have hbot : A₀ = ⊥ := le_bot_iff.mp (hA₀Z ▸ le_inf le_rfl (he ▸ hXZ))
          rw [hbot, Subgroup.card_bot] at hA₀card
          exact (Fact.out : p.Prime).ne_one hA₀card.symm
        have hreg := (hcReg X hXmem hXE hXneA₀).1
        rwa [hXdef, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at hreg
  · -- **τ₁ ∪ τ₃ case** (`r_p(M) = 1`): `Z = Sylow_p(U)` is regular by Lemma 14.1.
    have hr1 : pRank ↥M p = 1 := by
      have hle : pRank ↥M p ≤ 2 := hsetup.pRank_M_le_two hG hpE
      have hge : 1 ≤ pRank ↥M p :=
        (one_le_pRank_of_mem_primeFactors hpE).trans
          (pRank_le_of_injective (Subgroup.inclusion_injective hsetup.E_le))
      have hne2 : pRank ↥M p ≠ 2 := fun h2 => hpτ2 ⟨hpσ, h2⟩
      omega
    -- `Z = Sylow_p(U)`, pushed into `G`.
    set SU : Sylow p ↥U := default with hSUdef
    set Z : Subgroup G := (SU : Subgroup ↥U).map U.subtype with hZdef
    have hZU : Z ≤ U := Subgroup.map_subtype_le _
    have hZcard : Nat.card ↥Z = p ^ (Nat.card ↥U).factorization p := by
      rw [hZdef, Subgroup.card_map_of_injective U.subtype_injective, SU.card_eq_multiplicity]
    have hZpg : IsPGroup p ↥Z := IsPGroup.of_card hZcard
    have hZsub : Z.subgroupOf U = (SU : Subgroup ↥U) := by
      rw [hZdef, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective U.subtype_injective]
    have hZcard' : Nat.card ↥(Z.subgroupOf U) = p ^ (Nat.card ↥U).factorization p := by
      rw [hZsub, SU.card_eq_multiplicity]
    refine ⟨Z, hZU, hZpg, factorization_exponent_le_of_sylow hZU hZcard', ?_⟩
    -- **Regularity** (Lemma 14.1, `r_p = 1`, `p ∉ σ ∪ κ`): same discharge as the `K = ⊥` branch.
    intro z hzZ hzne
    obtain ⟨k, hk0⟩ := (IsPGroup.iff_orderOf.mp hZpg) ⟨z, hzZ⟩
    have hk : orderOf z = p ^ k := (Subgroup.orderOf_coe ⟨z, hzZ⟩).trans hk0
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | hpos
      · rw [pow_zero, orderOf_eq_one_iff] at hk; exact absurd hk hzne
      · exact hpos
    have hpdvd : p ∣ orderOf z := hk ▸ dvd_pow_self p (by omega)
    set f : G := z ^ (orderOf z / p) with hfdef
    have hford : orderOf f = p := orderOf_pow_orderOf_div (orderOf_pos z).ne' hpdvd
    have hfZ : f ∈ Z := Z.pow_mem hzZ _
    have hfM : f ∈ M := (hZU.trans hUM) hfZ
    set A : Subgroup G := Subgroup.zpowers f with hAdef
    have hAcard : Nat.card ↥A = p := by rw [hAdef, Nat.card_zpowers]; exact hford
    have hAelem : A.IsElementaryAbelian p := Subgroup.IsElementaryAbelian.of_card_prime hAcard
    have hAM : A ≤ M := by rw [hAdef, Subgroup.zpowers_le]; exact hfM
    have hAr : A ∈ elemAbelianOfRank G p (pRank ↥M p) := by
      rw [hr1, mem_elemAbelianOfRank]; exact ⟨hAelem, by rw [hAcard, pow_one]⟩
    obtain ⟨_, hCA, _⟩ := S14.msigma_structure_of_notMem_sigma_kappa hG hM hpπ hpσ hpκ hAr hAM
    have hCfA : Subgroup.centralizer (A : Set G) = Subgroup.centralizer ({f} : Set G) := by
      rw [hAdef, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    have hCzf : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.centralizer ({f} : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
      rw [hfdef]; exact (show Commute x z from hx).pow_right _
    rw [eq_bot_iff, ← hCA, hCfA]
    exact inf_le_inf_left _ hCzf

/-- **BG Lemma 15.1(e)** (mmd L4148): the Frobenius factor `U₀ M_σ`.  For a maximal `M` with
`κ(M)`-Hall `K` and `(κ ∪ σ)'`-Hall `U ≠ 1`, there is a subgroup `U₀ ≤ U` of the same exponent as
`U` such that `U₀ M_σ` is a Frobenius group with kernel `M_σ` and complement `U₀`.

Proof by the `K = ⊥` / `K ≠ ⊥` split:

* `K = ⊥` (type `F`): `U` is the `σ`-complement `E` of a §12 `E`-setup
  (`subgroupESetup_of_isHall_kappa_eq_bot`), and Theorem 12.12(b)
  (`frobenius_factorization_of_regular`, part (b)) supplies `U₀ = E₀ ≤ E = U` directly, with
  `exp U₀ = exp U` and `U₀ M_σ` Frobenius.  The regularity hypothesis is discharged exactly as in
  `typeP_centralizerGeneratedBySigma_isMulCommutative` (Lemma 14.1 for `(τ₁∪τ₃)`-elements).

* `K ≠ ⊥` (type `P`): `U` is abelian (`typeP_hall_derived_eq_and_abelian`).  We build `U₀ ≤ U`
  **`M`-internally** as the internal direct product `⨆_{p ∈ π(U)} Z_p`, where for each prime
  `p ∈ π(U)` the cyclic `Z_p ≤ Sylow_p(U)` realizes the `p`-part of `exp U` and acts regularly on
  `M_σ`:
  - `p ∈ (τ₁ ∪ τ₃)` (`r_p(M) = 1`): `Sylow_p(U)` is cyclic, take `Z_p = Sylow_p(U)`; regular by
    Lemma 14.1 (`Ω₁(Sylow_p(U)) ∈ ℰ_p¹(M)`, `p ∉ σ ∪ κ`).
  - `p ∈ τ₂` (`r_p(M) = 2`): `Sylow_p(U)` is abelian of rank `2`; Theorem 12.5(f) gives a regular
    line `A₁ ∈ ℰ_p¹(M)` inside `A := Ω₁(Sylow_p(U))`, and a cyclic `Z_p ≤ Sylow_p(U)` with
    `Ω₁(Z_p) = A₁`, `exp Z_p = exp Sylow_p(U)` propagates regularity to all of `Z_p`. -/
theorem typeP_hall_frobenius_factor [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hUne : U ≠ ⊥) :
    ∃ U0 : Subgroup G, U0 ≤ U ∧ Monoid.exponent ↥U0 = Monoid.exponent ↥U ∧
      OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(U0 ⊔ OddOrder.BG.Ch3.S10.Msigma M)
        ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf (U0 ⊔ OddOrder.BG.Ch3.S10.Msigma M))
        (U0.subgroupOf (U0 ⊔ OddOrder.BG.Ch3.S10.Msigma M)) := by
  classical
  set Mσ := OddOrder.BG.Ch3.S10.Msigma M with hMσdef
  by_cases hKbot : K = ⊥
  · -- **Case `K = ⊥`** (type `F`): `U = E` is the §12 `σ`-complement; Theorem 12.12(b).
    obtain ⟨E₁, E₂, E₃, hsetup⟩ :=
      subgroupESetup_of_isHall_kappa_eq_bot hG hM hKM hUM hK hKbot hU
    -- Discharge the regularity hypothesis of Theorem 12.12 via Lemma 14.1 (copied from
    -- `typeP_centralizerGeneratedBySigma_isMulCommutative`'s `K = ⊥` branch).
    have hreg : ∀ e ∈ U, e ≠ 1 →
        (∀ r ∈ (orderOf e).primeFactors, r ∈ tau1 M ∪ tau3 M) →
          Mσ ⊓ Subgroup.centralizer ({e} : Set G) = ⊥ := by
      intro e heU hene hprimes
      have hord1 : orderOf e ≠ 1 := fun hc => hene (orderOf_eq_one_iff.mp hc)
      obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hord1
      have : Fact p.Prime := ⟨hp⟩
      have hpτ : p ∈ tau1 M ∪ tau3 M :=
        hprimes p (Nat.mem_primeFactors.mpr ⟨hp, hpdvd, (orderOf_pos e).ne'⟩)
      set f : G := e ^ (orderOf e / p) with hfdef
      have hford : orderOf f = p := orderOf_pow_orderOf_div (orderOf_pos e).ne' hpdvd
      have hfU : f ∈ U := U.pow_mem heU _
      have hfM : f ∈ M := hUM hfU
      set A : Subgroup G := Subgroup.zpowers f with hAdef
      have hAcard : Nat.card ↥A = p := by rw [hAdef, Nat.card_zpowers]; exact hford
      have hAelem : A.IsElementaryAbelian p := Subgroup.IsElementaryAbelian.of_card_prime hAcard
      have hAM : A ≤ M := by rw [hAdef, Subgroup.zpowers_le]; exact hfM
      have hpπ : p ∈ S14.piSet M :=
        Nat.mem_primeFactors.mpr ⟨hp, hpdvd.trans ((U.orderOf_dvd_natCard heU).trans
          (Subgroup.card_dvd_of_le hUM)), Nat.card_pos.ne'⟩
      have hpσ : p ∉ OddOrder.BG.Ch3.S10.sigma M :=
        hpτ.elim (fun h => tau1_subset_sigma_compl M h) (fun h => tau3_subset_sigma_compl M h)
      have hpκ : p ∉ S14.kappa M := by
        rw [isTypeF_of_isHall_kappa_eq_bot hKM hK hKbot]; simp
      have hr1 : pRank ↥M p = 1 :=
        hpτ.elim tau1_pRank_eq_one tau3_pRank_eq_one
      have hAr : A ∈ elemAbelianOfRank G p (pRank ↥M p) := by
        rw [hr1, mem_elemAbelianOfRank]
        exact ⟨hAelem, by rw [hAcard, pow_one]⟩
      obtain ⟨_, hCA, _⟩ :=
        S14.msigma_structure_of_notMem_sigma_kappa hG hM hpπ hpσ hpκ hAr hAM
      have hCfA : Subgroup.centralizer (A : Set G) = Subgroup.centralizer ({f} : Set G) := by
        rw [hAdef, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      have hCef : Subgroup.centralizer ({e} : Set G) ≤ Subgroup.centralizer ({f} : Set G) := by
        intro x hx
        rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
        rw [hfdef]
        exact (show Commute x e from hx).pow_right _
      rw [eq_bot_iff, ← hCA, hCfA]
      exact inf_le_inf_left _ hCef
    -- Theorem 12.12(b): the same-exponent regular complement `E₀ ≤ U`.
    obtain ⟨_, E₀, hE₀le, hexp, hFrob⟩ :=
      frobenius_factorization_of_regular hG hsetup hreg
    refine ⟨E₀, hE₀le, hexp, ?_⟩
    -- `FrobFactConclusion` states it for `M_σ ⊔ E₀`; commute to `E₀ ⊔ M_σ`.
    rw [show E₀ ⊔ Mσ = Mσ ⊔ E₀ from sup_comm _ _]
    exact hFrob
  · -- **Case `K ≠ ⊥`** (type `P`): `U` is abelian (15.1(b)); assemble `U₀ = ⊔_p Z_p` from the
    -- per-prime regular components (`typeP_hall_regular_component_at_prime`) via the engine.
    obtain ⟨_, hUab⟩ := typeP_hall_derived_eq_and_abelian hG hM hKM hUM hKbot hK hU
    have hUinf : Mσ ⊓ U = ⊥ := by
      have hMσHall : Ch03.IsHallSubgroup (OddOrder.BG.Ch3.S10.sigma M) (Mσ.subgroupOf M) :=
        OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall hG hM
      have hcop : Nat.Coprime (Nat.card ↥U) (Nat.card ↥Mσ) := by
        refine Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
          (π := (S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) Nat.card_pos.ne' Nat.card_pos.ne'
          ?_ ?_
        · intro q hq
          exact hU.1 q (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv])
        · intro q hq hqcompl
          have hqMσ : q ∈ (Nat.card ↥(Mσ.subgroupOf M)).primeFactors := by
            rwa [Nat.card_congr
              (Subgroup.subgroupOfEquivOfLe (OddOrder.BG.Ch3.S10.Msigma_le M)).toEquiv]
          exact hqcompl (Or.inr (hMσHall.1 q hqMσ))
      rw [inf_comm]; exact (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
    exact frobenius_factor_of_regular_components hG hM hUM hUne hUab hUinf
      (fun p hp => typeP_hall_regular_component_at_prime hG hM hUM hUab hU hp)

/-- **Forward lemma: the `§14`-gated structural content of BG Lemma 15.1** (faithful to mmd L4116,
proof deferred).  Bundles the conjuncts of Lemma 15.1 that depend on the §14 results
(Proposition 14.2(a)'s normal complement `M = K U M_σ`, Theorem 14.7(d)(h)) and Theorem 12.12:

* `K ≠ ⊥ → M' = U M_σ ∧ U` abelian (mmd 15.1(b), Theorem 14.7(h) + Corollary 12.10(b));
* mmd 15.1(c): the `C_{M_σ}(X) ≠ 1` ⟹ `𝓜(C_G(X)) = {M}`, `X` cyclic `τ₂` funnel (Corollary 14.3 +
  Theorem 12.5(d) + Corollary 12.10(b));
* mmd 15.1(d): `⟨C_U(x) | x ∈ M_σ#⟩` abelian (Theorem 12.12(a) for `K = 1`; `U` abelian for
  `K ≠ 1`);
* mmd 15.1(e): the Frobenius subgroup `U₀ M_σ` (Theorem 12.12(b) for `K = 1`; the componentwise
  construction for `K ≠ 1`).

These are isolated here so that `typeP_auxiliary_structure` discharges conjuncts 3 (`M_σ ≤ M'`) and
4 (`M'' ≤ M_σ`) with no `sorry` of its own, citing this lemma only for the §14 parts.  §14
(Prop 14.2(a), Thm 14.7(h)) and the Theorem 12.12 `K ≠ 1` Frobenius construction have landed, and
this forward lemma is the single discharge point. -/
theorem typeP_auxiliary_structure_gated [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      (U.subgroupOf M)) :
    (K ≠ ⊥ → derivedInG M = U ⊔ OddOrder.BG.Ch3.S10.Msigma M ∧ IsMulCommutative ↥U) ∧
      (∀ X : Subgroup G, X ≤ U → X ≠ ⊥ →
        OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥ →
          maximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M} ∧
            IsCyclic ↥X ∧ (↑(Nat.card ↥X).primeFactors ⊆ tau2 M)) ∧
      IsMulCommutative ↥(centralizerGeneratedBySigma M U) ∧
      (U ≠ ⊥ → ∃ U0 : Subgroup G,
        U0 ≤ U ∧ Monoid.exponent U0 = Monoid.exponent U ∧
          OddOrder.Isaacs.Ch06.IsFrobeniusGroup
            ↥(U0 ⊔ OddOrder.BG.Ch3.S10.Msigma M)
            ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf
              (U0 ⊔ OddOrder.BG.Ch3.S10.Msigma M))
            (U0.subgroupOf (U0 ⊔ OddOrder.BG.Ch3.S10.Msigma M))) :=
  -- All four conjuncts of BG Lemma 15.1 are now standalone clean lemmas (issue 7007).
  ⟨fun hKbot => typeP_hall_derived_eq_and_abelian hG hM hKM hUM hKbot hK hU,
   fun _X hXU hXne hCX => typeP_hall_small_subgroup_cyclic_tau2 hG hM hUM hU hXU hXne hCX,
   typeP_centralizerGeneratedBySigma_isMulCommutative hG hM hKM hUM hK hU,
   fun hUne => typeP_hall_frobenius_factor hG hM hKM hUM hK hU hUne⟩

/-- **BG Lemma 15.1** (mmd L4116): auxiliary structure around the `U`-factor of an
**arbitrary** maximal subgroup `M = KUM_σ`.  The quotient assertion `M'/M_sigma` abelian is
encoded as `M'' <= M_sigma`, avoiding premature quotient API commitments.

Faithfulness fix (Lane G): the previous scaffold added a spurious `IsTypeP M` hypothesis;
mmd Lemma 15.1 holds for every `M ∈ ℳ` (the `K ≠ 1` clauses are guarded inline), and the
general form is what Theorem A(2) and Theorem B cite.

`K ≠ 1` exposure (Lane G): the `K ≠ ⊥` clause now also records `M = K M'` as the relative
complement `IsComplement' (M'.subgroupOf M) (K.subgroupOf M)` together with the `(|M'|, |K|)`
coprimality — both are mmd 15.1(a)+(b) (`M = KUM_σ`, `K ≠ 1 → M' = UM_σ`, with `|K|` a
`κ(M)`-number and `|M'|` a `κ(M)'`-number).  This supplies exactly the hypotheses of
`Msigma_inf_centralizer_le_derivedDerived_of_isComplement'` (the §14-independent `K* ⊆ M''`
engine), so Corollary 15.6's `K* ⊆ M''` clause becomes a single citation once §14 lands.

Faithfulness fix (Lane G 2026-06-15): added `hKM : K ≤ M` and `hUM : U ≤ M`.  In BG, `K` and
`U` are *subgroups of* `M` (Hall `κ(M)`- and `(κ∪σ)'`-subgroups of `M`); without these the
`κ`/`σ`-prime bookkeeping degenerates (e.g. `K ⊓ M = 1` with `K ≠ 1` makes `K ≠ ⊥ → …` false).
The sole caller (`fitting_decomposition`) constructs `K = K'.map M.subtype`, `U = U'.map M.subtype`,
so both containments hold there.

Proof status (2026-06-23): **now fully sorry-free + axiom-clean** (`#print axioms
typeP_auxiliary_structure` = `[propext, Classical.choice, Quot.sound]`).  The §14-gated parts below
have all landed — `typeP_auxiliary_structure_gated` is now a clean term-mode citation of four
standalone lemmas, and Thm 14.7 (`typeP_duality`) is itself sorry-free — so the "(sorried)"
qualifiers in the historical status below are stale.  Original (Lane G 2026-06-15) breakdown:
* **Conjunct 3** (`M_σ ≤ M'`, Thm 10.2(c)) and **conjunct 4** (`M'' ≤ M_σ` via
  `derivedDerived_le_Msigma`, Cor 12.10(b)) are **sorry-free** (`#print axioms
  derivedDerived_le_Msigma` = `[propext, Classical.choice, Quot.sound]`), citing no `sorry`.
* **Conjunct 1** (`U M_σ ⊴ M`): the `K = ⊥` branch is sorry-free
  (`subgroupESetup_of_isHall_kappa_eq_bot` ⟹ `U M_σ = M`); the `K ≠ ⊥` branch reduces to
  `M' = U M_σ` (forward lemma).
* **Conjunct 2** (`K` cyclic): `K = ⊥` sorry-free; `K ≠ ⊥` cites the (sorried) §14 `typeP_duality`
  (Thm 14.7(d)), with `IsTypeP M` derived from `K ≠ ⊥`
  (`isTypeP_of_isHall_kappa_subgroupOf_ne_bot`).
* **Conjunct 5** (`K ≠ ⊥` package): `IsComplement'` + coprimality cite the §14
  `typeP_duality` (Thm 14.7(h)); `M' = U M_σ` and `U` abelian come from the forward lemma.
* **Conjuncts 6** (Cor 14.3 funnel — the `X` cyclic-`τ₂` step needs `X` abelian, which routes
  through Hall-`τ₂`-conjugacy for `K = ⊥`), **7**, and **8** route through the §14 results
  (Prop 14.2(a) normal complement, Thm 14.7) and Theorem 12.12.

All of the `§14`-structural content is isolated in the single faithful forward lemma
`typeP_auxiliary_structure_gated`; this theorem itself introduces no `sorry` of its own. -/
theorem typeP_auxiliary_structure [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      (U.subgroupOf M)) :
    M ≤ Subgroup.normalizer ((U ⊔ OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) : Set G) ∧
      IsCyclic ↥K ∧
      OddOrder.BG.Ch3.S10.Msigma M ≤ derivedInG M ∧
      derivedInG (derivedInG M) ≤ OddOrder.BG.Ch3.S10.Msigma M ∧
      (K ≠ ⊥ → derivedInG M = U ⊔ OddOrder.BG.Ch3.S10.Msigma M ∧
        IsMulCommutative ↥U ∧
        Subgroup.IsComplement' ((derivedInG M).subgroupOf M) (K.subgroupOf M) ∧
        Nat.Coprime (Nat.card ↥((derivedInG M).subgroupOf M))
          (Nat.card ↥(K.subgroupOf M))) ∧
      (∀ X : Subgroup G, X ≤ U → X ≠ ⊥ →
        OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥ →
          maximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M} ∧
            IsCyclic ↥X ∧ (↑(Nat.card ↥X).primeFactors ⊆ tau2 M)) ∧
      IsMulCommutative ↥(centralizerGeneratedBySigma M U) ∧
      (U ≠ ⊥ → ∃ U0 : Subgroup G,
        U0 ≤ U ∧ Monoid.exponent U0 = Monoid.exponent U ∧
          OddOrder.Isaacs.Ch06.IsFrobeniusGroup
            ↥(U0 ⊔ OddOrder.BG.Ch3.S10.Msigma M)
            ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf
              (U0 ⊔ OddOrder.BG.Ch3.S10.Msigma M))
            (U0.subgroupOf (U0 ⊔ OddOrder.BG.Ch3.S10.Msigma M))) := by
  classical
  set Mσ := OddOrder.BG.Ch3.S10.Msigma M with hMσ
  -- The §14-gated structural facts (forward lemma).
  obtain ⟨hM'gated, hX, hCab, hFrob⟩ :=
    typeP_auxiliary_structure_gated hG hM hKM hUM hK hU
  -- **Conjunct 5** (`K ≠ ⊥` package): `M' = U M_σ`, `U` abelian (forward), plus the complement /
  -- coprimality from Theorem 14.7(h) (`typeP_duality`, with `IsTypeP` from `K ≠ ⊥`).
  have hconj5 : K ≠ ⊥ → derivedInG M = U ⊔ Mσ ∧ IsMulCommutative ↥U ∧
      Subgroup.IsComplement' ((derivedInG M).subgroupOf M) (K.subgroupOf M) ∧
      Nat.Coprime (Nat.card ↥((derivedInG M).subgroupOf M)) (Nat.card ↥(K.subgroupOf M)) := by
    intro hKne
    obtain ⟨hM'eq, hUab⟩ := hM'gated hKne
    -- `IsTypeP M` from `K ≠ ⊥` (`K ≤ M` makes `K.subgroupOf M ≠ ⊥`).
    have hKofne : K.subgroupOf M ≠ ⊥ := by
      rw [ne_eq, Subgroup.subgroupOf_eq_bot]
      exact fun hd => hKne (hd.eq_bot_of_le hKM)
    have hP : S14.IsTypeP M := isTypeP_of_isHall_kappa_subgroupOf_ne_bot hK hKofne
    obtain ⟨hcompl, hcop, _⟩ := typeP_duality hG hM hP hKM hK hKstar
    exact ⟨hM'eq, hUab, hcompl, hcop⟩
  -- **Conjunct 2** (`K` cyclic).
  have hconj2 : IsCyclic ↥K := by
    by_cases hKne : K = ⊥
    · rw [hKne]; infer_instance
    · have hKofne : K.subgroupOf M ≠ ⊥ := by
        rw [ne_eq, Subgroup.subgroupOf_eq_bot]
        exact fun hd => hKne (hd.eq_bot_of_le hKM)
      have hP : S14.IsTypeP M := isTypeP_of_isHall_kappa_subgroupOf_ne_bot hK hKofne
      obtain ⟨_, _, _Mstar, ⟨_, _, _, _, hcyc, _, _, _⟩, _⟩ := typeP_duality hG hM hP hKM hK hKstar
      have := hcyc
      exact Subgroup.isCyclic_of_le (le_sup_left : K ≤ K ⊔ Kstar)
  -- **Conjunct 1** (`M ≤ N_G(U M_σ)`): `U M_σ = M` (`K = ⊥`) or `= M'` (`K ≠ ⊥`), both normal.
  have hconj1 : M ≤ Subgroup.normalizer ((U ⊔ Mσ : Subgroup G) : Set G) := by
    by_cases hKne : K = ⊥
    · -- `K = ⊥ → U M_σ = M`, so `N_G(U M_σ) = N_G(M) ⊇ M`.
      obtain ⟨E₁, E₂, E₃, hsetup⟩ :=
        subgroupESetup_of_isHall_kappa_eq_bot hG hM hKM hUM hK hKne hU
      have hUMσ : U ⊔ Mσ = M := by rw [sup_comm]; exact hsetup.E_compl_sup
      rw [hUMσ]; exact Subgroup.le_normalizer
    · -- `K ≠ ⊥ → U M_σ = M'`, and `M ≤ N_G(M')` (`M' ⊴ M`).
      obtain ⟨hM'eq, _, _, _⟩ := hconj5 hKne
      rw [← hM'eq]
      exact OddOrder.BG.Ch3.S10.le_normalizer_derivedInG M
  exact ⟨hconj1, hconj2, OddOrder.BG.Ch3.S10.Msigma_le_derived hG hM,
    derivedDerived_le_Msigma hG hM, hconj5, hX, hCab, hFrob⟩

end OddOrder.BG.Ch4.S15


