-- Prove2me | Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_ElemAbelianNeighbor
-- name    : OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_ElemAbelianNeighbor
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T09:09:29.87412+00:00
-- url     : https://prove2.me/theorems/1cf23cf5-93ae-4d59-b9a3-bfc274e1bdeb
-- title:
--   BG §14: type-$\mathcal{P}$ counting, elementary abelian neighbors
-- statement:
--   A part of the §14 type-$\mathcal{P}$ counting development of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, split from the local-structure file. Lemmas include the structure of $M_\sigma$ for primes outside $\sigma\cup\kappa$, centralizers of $M_\sigma$ against elementary abelian subgroups, existence of rank-two elementary abelian subgroups in $E_2$, and that $\sigma(M)=\beta(M)$ in case $\tau_1$.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 10 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch4_FamilyOfMaximal/S14_TypePCounting/ElemAbelianNeighbor.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch4_FamilyOfMaximal/S14_TypePCounting/ElemAbelianNeighbor.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_Basics

namespace OddOrder.BG.Ch4.S14

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.BG.Ch3.S12

open OddOrder.BG.Ch3.S13

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **BG Lemma 14.1** (mmd L3811): suppose `M ∈ 𝓜` and `p ∈ π(M) - (σ(M) ∪ κ(M))`.
Let `A` be an elementary abelian `p`-subgroup of `M` of maximal rank `r_p(M)`
(realized by `A = Ω₁(S)` for `S ∈ Syl_p(M)`).  Then `|A| ≤ p²`, `C_{M_σ}(A) = 1`,
and `M_σ` is nilpotent.

BG's hypothesis `M ∉ 𝓜_{𝓟₁}` only guarantees that such a prime `p` exists; once
`p` is given (`hpπ`, `hpσ`, `hpκ`), it plays no role in the proof, so it is dropped
here.  The `A = Ω₁(S)` binding is encoded as `A ∈ ℰ_p^{r_p(M)}(M)` (the same
`Ω`-deferral used in Theorem 12.5), under which `|A| = p^{r_p(M)}`, so the
cardinality assertion `|A| ≤ p²` is the rank bound `r_p(M) ≤ 2`.

Proof: by the τ-classification `r_p(M) ∈ {1, 2}`.  If `r_p(M) = 2` then `p ∈ τ₂(M)`
and all three assertions are Theorem 12.5(a)(d).  If `r_p(M) = 1` then
`p ∈ τ₁(M) ∪ τ₃(M)`; `C_{M_σ}(A) = 1` because `p ∉ κ(M)`, and since `A` has prime
order it then acts fixed-point-freely on `M_σ`, so `M_σ` is nilpotent by Theorem
3.7 (`isNilpotent_of_normalizing_primeOrder_fixedPointFree`). -/
theorem msigma_structure_of_notMem_sigma_kappa [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime]
    (hpπ : p ∈ piSet M) (hpσ : p ∉ OddOrder.BG.Ch3.S10.sigma M) (hpκ : p ∉ kappa M)
    {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p (pRank ↥M p)) (hAM : A ≤ M) :
    Nat.card ↥A ≤ p ^ 2 ∧
      OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (A : Set G) = ⊥ ∧
      Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma M) := by
  classical
  have hp : p.Prime := Fact.out
  have hpM : p ∈ (Nat.card ↥M).primeFactors := hpπ
  -- Rank bounds `1 ≤ r_p(M) ≤ 2` via the §12 `E`-setup.
  obtain ⟨E, E₁, E₂, E₃, hsetup⟩ := exists_subgroupESetup hG hM
  have hpE : p ∈ (Nat.card ↥E).primeFactors :=
    mem_primeFactors_E_of_mem_M_of_not_sigma hG hsetup hp hpM hpσ
  have h1r : 1 ≤ pRank ↥M p := one_le_pRank_of_mem_primeFactors hpM
  have h2r : pRank ↥M p ≤ 2 := hsetup.pRank_M_le_two hG hpE
  have hcardA : Nat.card ↥A = p ^ pRank ↥M p := hA.2
  -- (1) `|A| ≤ p²` is the rank bound.
  have hbound : Nat.card ↥A ≤ p ^ 2 := by
    rw [hcardA]; exact Nat.pow_le_pow_right hp.one_le h2r
  refine ⟨hbound, ?_⟩
  have hrank12 : pRank ↥M p = 1 ∨ pRank ↥M p = 2 := by omega
  rcases hrank12 with hr1 | hr2
  · -- `r_p(M) = 1`: `p ∈ τ₁(M) ∪ τ₃(M)`, fixed-point-free action.
    have hAr1 : A ∈ elemAbelianOfRank G p 1 := by rw [← hr1]; exact hA
    have hcardp : Nat.card ↥A = p := by rw [hcardA, hr1, pow_one]
    have hpτ13 : p ∈ tau1 M ∪ tau3 M := by
      by_cases hM' : p ∈ (Nat.card ↥(derivedInG M)).primeFactors
      · exact Or.inr ((mem_tau3_iff M p).mpr ⟨hpσ, hM', hr1⟩)
      · exact Or.inl ((mem_tau1_iff M p).mpr ⟨hpσ, hM', hr1⟩)
    -- `C_{M_σ}(A) = 1` because `p ∉ κ(M)`.
    have hC : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (A : Set G) = ⊥ := by
      by_contra hne
      exact hpκ ⟨hp, hpτ13, A, hAr1, hAM, hne⟩
    refine ⟨hC, ?_⟩
    -- `A` is commutative, hence `A ≤ C_G(A)`.
    have hAcent : A ≤ Subgroup.centralizer (A : Set G) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have := hA.1.comm (⟨b, hb⟩ : ↥A) (⟨a, ha⟩ : ↥A)
      exact congrArg (Subtype.val) this
    -- Hypotheses for Theorem 3.7 (`N = M_σ`, `R = A`).
    have hMsolv : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
    have : Group.IsSolvable ↥(OddOrder.BG.Ch3.S10.Msigma M ⊔ A) :=
      Group.isSolvable_of_isSolvable_injective
        (Subgroup.inclusion_injective (sup_le (OddOrder.BG.Ch3.S10.Msigma_le M) hAM))
    have hAnorm : A ≤ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma M) :=
      hAM.trans (le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) M)
    have hdisj : Disjoint (OddOrder.BG.Ch3.S10.Msigma M) A := by
      rw [disjoint_iff]
      refine le_antisymm ?_ bot_le
      calc OddOrder.BG.Ch3.S10.Msigma M ⊓ A
            ≤ OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (A : Set G) :=
              inf_le_inf_left _ hAcent
        _ = ⊥ := hC
    have hMσne : OddOrder.BG.Ch3.S10.Msigma M ≠ ⊥ := OddOrder.BG.Ch3.S10.Msigma_ne_bot hG hM
    have hAne : A ≠ ⊥ := ne_bot_of_mem_elemAbelianOfRank_one hAr1
    -- `A` acts fixed-point-freely on `M_σ`: an element fixed by `r ∈ A#` would
    -- centralize `⟨r⟩ = A` and so lie in `C_{M_σ}(A) = 1`.
    have hgen : ∀ r ∈ A, r ≠ 1 → A = Subgroup.zpowers r := by
      intro r hr hr1'
      have hle : Subgroup.zpowers r ≤ A := Subgroup.zpowers_le.mpr hr
      have hcardzp : Nat.card ↥(Subgroup.zpowers r) = p := by
        have hdvd : orderOf r ∣ p := by
          rw [← hcardp, ← Nat.card_zpowers]; exact Subgroup.card_dvd_of_le hle
        rw [Nat.card_zpowers]
        rcases (Nat.dvd_prime hp).mp hdvd with h1 | hpp
        · exact absurd (orderOf_eq_one_iff.mp h1) hr1'
        · exact hpp
      exact (Subgroup.eq_of_le_of_card_ge hle (hcardp.trans hcardzp.symm).le).symm
    have hFPF : ∀ r ∈ A, r ≠ 1 → ∀ n ∈ OddOrder.BG.Ch3.S10.Msigma M, n ≠ 1 →
        r * n * r⁻¹ ≠ n := by
      intro r hr hr1' n hn hn1 heq
      have hcomm : Commute r n := mul_inv_eq_iff_eq_mul.mp heq
      have hAr : A = Subgroup.zpowers r := hgen r hr hr1'
      have hncent : n ∈ Subgroup.centralizer (A : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro a haA
        rw [hAr, SetLike.mem_coe, Subgroup.mem_zpowers_iff] at haA
        obtain ⟨k, rfl⟩ := haA
        exact hcomm.zpow_left k
      have hmem : n ∈ OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (A : Set G) :=
        ⟨hn, hncent⟩
      rw [hC, Subgroup.mem_bot] at hmem
      exact hn1 hmem
    exact OddOrder.BG.Ch1.S03c.isNilpotent_of_normalizing_primeOrder_fixedPointFree
      hAnorm hdisj hMσne hAne ⟨p, hp, hcardp⟩ hFPF
  · -- `r_p(M) = 2`: `p ∈ τ₂(M)`; Theorem 12.5(a),(d).
    have hpτ2 : p ∈ tau2 M := (mem_tau2_iff M p).mpr ⟨hpσ, hr2⟩
    have hA2 : A ∈ elemAbelianOfRank G p 2 := by rw [← hr2]; exact hA
    have h125 := Msigma_nilpotent_of_tau2 hG hM hpτ2 hA2 hAM
    exact ⟨h125.2.2.2.1, h125.1⟩

/-- Helper for `Msigma_centralizer_E23_eq_bot_of_caseTau1`: a maximal-rank elementary abelian
`p`-subgroup `A ≤ M` satisfying Lemma 14.1's hypotheses (`p ∈ π(M) ∖ (σ(M) ∪ κ(M))`) gives
`C_{M_σ}(A) = 1` (Lemma 14.1); since `A ≤ U`, centralizer antitonicity lifts this to
`C_{M_σ}(U) ≤ C_{M_σ}(A) = 1`. -/
theorem msigma_centralizer_eq_bot_of_elemAb_le [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {U A : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hpπ : p ∈ piSet M) (hpσ : p ∉ OddOrder.BG.Ch3.S10.sigma M) (hpκ : p ∉ kappa M)
    (hA : A ∈ elemAbelianOfRank G p (pRank ↥M p)) (hAM : A ≤ M) (hAU : A ≤ U) :
    OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (U : Set G) = ⊥ ∧
      Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma M) := by
  obtain ⟨_, hCA, hnilp⟩ := msigma_structure_of_notMem_sigma_kappa hG hM hpπ hpσ hpκ hA hAM
  refine ⟨?_, hnilp⟩
  rw [eq_bot_iff, ← hCA]
  exact inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hAU))

/-- Helper for `Msigma_centralizer_E23_eq_bot_of_caseTau1`, case `E₃ = ⊥`: for `q ∈ τ₂(M)` and a
`q`-element `y' ∈ E₂#`, `Ω₁(E₂)` is a rank-two elementary abelian `q`-subgroup *of `E₂`* (not just
`E`) containing `y'`.  Same as `exists_elemAb_rank_two_le_E_mem_of_tau2` but exposes the stronger
containment `A ≤ E₂`, which the `U = E₂E₃ = E₂` reduction needs. -/
private theorem exists_elemAb_rank_two_le_E2_mem_of_tau2 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃) {q : ℕ} [Fact q.Prime] (hq : q ∈ tau2 M)
    {y' : G} (hy'E2 : y' ∈ E₂) (hy'q : y' ^ q = 1) (_hy'1 : y' ≠ 1) :
    ∃ A ∈ elemAbelianOfRank G q 2, A ≤ E₂ ∧ y' ∈ A := by
  classical
  have hE2comm : IsMulCommutative ↥E₂ := (nilpotent_sigmaComplement_abelian hG h).2.1.1
  have hcomm : ∀ x ∈ E₂, ∀ y ∈ E₂, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE2comm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  set A : Subgroup G := omega1OfAbelian G E₂ q hcomm with hAdef
  have hAelem : A.IsElementaryAbelian q := omega1OfAbelian_isElementaryAbelian
  have hAE2 : A ≤ E₂ := omega1OfAbelian_le
  have hy'A : y' ∈ A := (mem_omega1OfAbelian).mpr ⟨hy'E2, hy'q⟩
  -- `r_q(E₂) = 2`: two `q`-coprime index steps `E₂ ≤ E ≤ M`, then `r_q(M) = 2`.
  have hpRankE2 : pRank ↥E₂ q = 2 := by
    have hr1 : pRank ↥E₂ q = pRank ↥E q :=
      pRank_eq_of_le_of_not_dvd_index h.E₂_le (fun hdvd =>
        h.E₂_hall.index_no_pi q (Nat.mem_primeFactors.mpr
          ⟨Fact.out, hdvd, Subgroup.index_ne_zero_of_finite⟩) hq)
    have hr2 : pRank ↥E q = pRank ↥M q := by
      refine pRank_eq_of_le_of_not_dvd_index h.E_le (fun hdvd => ?_)
      have hqσ : q ∉ OddOrder.BG.Ch3.S10.sigma M := tau2_subset_sigma_compl M hq
      have hidxeq : (E.subgroupOf M).index = Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) := by
        rw [h.isComplement'_subgroupOf.index_eq_card,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe (OddOrder.BG.Ch3.S10.Msigma_le M)).toEquiv]
      rw [hidxeq] at hdvd
      exact hqσ (OddOrder.BG.Ch3.S10.Msigma_isPiGroup M q
        (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩))
    rw [hr1, hr2, tau2_pRank_eq_two hq]
  -- `|A| = q²` from `q² ∣ |A|` (rank ≥ 2) and `log_q |A| ≤ r_q(E₂) = 2`.
  have hAcard : Nat.card ↥A = q ^ 2 := by
    have hdvd : q ^ 2 ∣ Nat.card ↥A :=
      hAdef ▸ pow_dvd_card_omega1OfAbelian_of_pos_le_pRank (by norm_num) hpRankE2.ge
    have hlog_le : Nat.log q (Nat.card ↥A) ≤ 2 := by
      have hAsub : (A.subgroupOf E₂).IsElementaryAbelian q :=
        IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAE2).symm hAelem
      have hcardeq : Nat.card ↥(A.subgroupOf E₂) = Nat.card ↥A :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAE2).toEquiv
      have hle := le_pRank (A.subgroupOf E₂) hAsub
      rwa [hcardeq, hpRankE2] at hle
    have hcardpow : Nat.card ↥A = q ^ Nat.log q (Nat.card ↥A) := by
      rw [hAelem.log_card_eq_finrank, hAelem.card_eq_pow_finrank]
    have h2le : 2 ≤ Nat.log q (Nat.card ↥A) := by
      rw [hcardpow] at hdvd
      exact (Nat.pow_dvd_pow_iff_le_right (Fact.out : q.Prime).one_lt).mp hdvd
    rw [hcardpow]; congr 1; omega
  exact ⟨A, ⟨hAelem, hAcard⟩, hAE2, hy'A⟩

/-- **`C_{M_σ}(U) = 1`** for `U = E₂E₃` in case `τ₁` (BG Lemma 14.1 bridge).  `U` is a Hall
`(κ(M) ∪ σ(M))'`-subgroup; picking any prime `p ∈ π(U)` and a maximal-rank elementary abelian
`p`-subgroup `A ≤ U`, Lemma 14.1 (`msigma_structure_of_notMem_sigma_kappa`) gives `C_{M_σ}(A) = 1`,
and `C_{M_σ}(U) ≤ C_{M_σ}(A)`.  (In case `τ₁`, `κ(M) ∩ τ₃(M) = ∅` ensures `π(U) ∩ κ(M) = ∅`.)
This is the `C_{M_σ}(U) = 1` hypothesis Proposition 14.2(g) feeds to Theorem 3.10(a).

Proof: since `U = E₂E₃ ≠ 1`, either `E₃ ≠ 1` or `E₂ ≠ 1`.  If `E₃ ≠ 1`, a prime `p ∣ |E₃|`
lies in `τ₃(M)` (as `E₃` is Hall `τ₃(M)` of `E`) with `r_p(M) = 1`, and a cyclic `A = ⟨g⟩ ≤ E₃`
of order `p` is rank-one elementary abelian; `p ∉ κ(M)` because `κ(M) ∩ τ₃(M) = ∅`.  If `E₃ = 1`
then `U = E₂ ≠ 1`; a prime `q ∣ |E₂|` lies in `τ₂(M)` with `r_q(M) = 2`, and `A = Ω₁(E₂) ≤ E₂`
is rank-two elementary abelian; `q ∉ κ(M) ⊆ τ₁(M) ∪ τ₃(M)` since `r_q(M) = 2 ≠ 1`.  Either way
Lemma 14.1 (via `msigma_centralizer_eq_bot_of_elemAb_le`) closes the goal. -/
theorem Msigma_centralizer_E23_eq_bot_of_caseTau1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃)
    (hτ3 : ¬ (kappa M ∩ tau3 M).Nonempty)
    (hUne : (E₂ ⊔ E₃ : Subgroup G) ≠ ⊥) :
    OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ((E₂ ⊔ E₃ : Subgroup G) : Set G) = ⊥ ∧
      Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma M) := by
  classical
  by_cases hE3 : E₃ = ⊥
  · -- Case `E₃ = ⊥`: `U = E₂E₃ = E₂ ≠ ⊥`; pick `q ∈ τ₂(M)` and `A = Ω₁(E₂)` of rank two.
    have hE2 : E₂ ≠ ⊥ := by
      intro hb; exact hUne (by rw [hb, hE3, bot_sup_eq])
    have hcard2 : Nat.card ↥E₂ ≠ 1 := fun hc => hE2 (Subgroup.card_eq_one.mp hc)
    obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hcard2
    have : Fact q.Prime := ⟨hq⟩
    obtain ⟨y', hy'⟩ := exists_prime_orderOf_dvd_card' (G := ↥E₂) q hqdvd
    have hy'E2 : (y' : G) ∈ E₂ := y'.2
    have hy'ord : orderOf (y' : G) = q :=
      (orderOf_injective E₂.subtype E₂.subtype_injective y').trans hy'
    have hy'q : (y' : G) ^ q = 1 := by rw [← hy'ord]; exact pow_orderOf_eq_one _
    have hy'1 : (y' : G) ≠ 1 := by
      intro hc; rw [hc, orderOf_one] at hy'ord; exact hq.ne_one hy'ord.symm
    -- `q ∈ τ₂(M)`: `q ∣ |E₂|`, and `E₂` is Hall `τ₂(M)` of `E`.
    have hqE2 : q ∈ (Nat.card ↥E₂).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hq, hqdvd, Nat.card_pos.ne'⟩
    have hqτ2 : q ∈ tau2 M := by
      have hc2 : Nat.card ↥(E₂.subgroupOf E) = Nat.card ↥E₂ :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₂_le).toEquiv
      exact h.E₂_hall.1 q (hc2 ▸ hqE2)
    -- rank-two `A = Ω₁(E₂) ≤ E₂`.
    obtain ⟨A, hAmem, hAE2, _⟩ :=
      exists_elemAb_rank_two_le_E2_mem_of_tau2 hG h hqτ2 hy'E2 hy'q hy'1
    have hAM : A ≤ M := hAE2.trans (h.E₂_le.trans h.E_le)
    have hArank : A ∈ elemAbelianOfRank G q (pRank ↥M q) := by
      rw [tau2_pRank_eq_two hqτ2]; exact hAmem
    have hpπ : q ∈ piSet M :=
      Nat.mem_primeFactors.mpr ⟨hq,
        hqdvd.trans (Subgroup.card_dvd_of_le (h.E₂_le.trans h.E_le)), Nat.card_pos.ne'⟩
    have hqσ : q ∉ OddOrder.BG.Ch3.S10.sigma M := tau2_subset_sigma_compl M hqτ2
    -- `q ∉ κ(M) ⊆ τ₁(M) ∪ τ₃(M)`: `r_q(M) = 2`, but `τ₁, τ₃` have `r = 1`.
    have hqκ : q ∉ kappa M := by
      intro hqκ
      have hr2 := tau2_pRank_eq_two hqτ2
      rcases kappa_subset_tau1_union_tau3 hqκ with hτ1 | hτ3'
      · have := tau1_pRank_eq_one hτ1; omega
      · have := tau3_pRank_eq_one hτ3'; omega
    have hAU : A ≤ (E₂ ⊔ E₃ : Subgroup G) := hAE2.trans le_sup_left
    exact msigma_centralizer_eq_bot_of_elemAb_le hG h.mem_maximal hpπ hqσ hqκ hArank hAM hAU
  · -- Case `E₃ ≠ ⊥`: pick `p ∈ τ₃(M)` and a cyclic rank-one `A = ⟨g⟩ ≤ E₃`.
    have hcard3 : Nat.card ↥E₃ ≠ 1 := fun hc => hE3 (Subgroup.card_eq_one.mp hc)
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hcard3
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥E₃) p hpdvd
    have hgE3 : (g : G) ∈ E₃ := g.2
    have hgord : orderOf (g : G) = p :=
      (orderOf_injective E₃.subtype E₃.subtype_injective g).trans hg
    have hPcard : Nat.card ↥(Subgroup.zpowers (g : G)) = p := by rw [Nat.card_zpowers]; exact hgord
    have hAE3 : Subgroup.zpowers (g : G) ≤ E₃ := Subgroup.zpowers_le.mpr hgE3
    have hAr1 : Subgroup.zpowers (g : G) ∈ elemAbelianOfRank G p 1 :=
      ⟨Subgroup.IsElementaryAbelian.of_card_prime hPcard, by rw [hPcard, pow_one]⟩
    -- `p ∈ τ₃(M)`: `p ∣ |E₃|`, and `E₃` is Hall `τ₃(M)` of `E`.
    have hpE3 : p ∈ (Nat.card ↥E₃).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, hpdvd, Nat.card_pos.ne'⟩
    have hpτ3 : p ∈ tau3 M := by
      have hc3 : Nat.card ↥(E₃.subgroupOf E) = Nat.card ↥E₃ :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₃_le).toEquiv
      exact h.E₃_hall.1 p (hc3 ▸ hpE3)
    have hAM : Subgroup.zpowers (g : G) ≤ M := hAE3.trans (h.E₃_le.trans h.E_le)
    have hArank : Subgroup.zpowers (g : G) ∈ elemAbelianOfRank G p (pRank ↥M p) := by
      rw [tau3_pRank_eq_one hpτ3]; exact hAr1
    have hpπ : p ∈ piSet M :=
      Nat.mem_primeFactors.mpr ⟨hp, hpdvd.trans (Subgroup.card_dvd_of_le
        (h.E₃_le.trans h.E_le)), Nat.card_pos.ne'⟩
    have hpσ : p ∉ OddOrder.BG.Ch3.S10.sigma M := tau3_subset_sigma_compl M hpτ3
    -- `p ∉ κ(M)`: `κ(M) ∩ τ₃(M) = ∅` and `p ∈ τ₃(M)`.
    have hpκ : p ∉ kappa M := fun hpκ => hτ3 ⟨p, hpκ, hpτ3⟩
    have hAU : Subgroup.zpowers (g : G) ≤ (E₂ ⊔ E₃ : Subgroup G) := hAE3.trans le_sup_right
    exact msigma_centralizer_eq_bot_of_elemAb_le hG h.mem_maximal hpπ hpσ hpκ hArank hAM hAU

/-- **BG Proposition 14.2(g), TI conjunct** (mmd L3850): if `σ(M) = β(M)` then `M_σ^#` is a
TI-subset of `G` with normalizer-bound `N_G(M_σ)`.  For `g` producing an overlap of `M_σ^#`
with its `g`-conjugate, either `g ∈ M ≤ N_G(M_σ)`, or `g ∉ M` and Lemma 12.17
(`Msigma_inf_conj_isBetaCompl`) makes `M_σ ∩ M_σ^g` a `β(M)′ = σ(M)′`-group; being also a
`σ(M)`-group (`≤ M_σ`) it is trivial, contradicting the nontrivial overlap.  This is the
TI clause Proposition 14.2(g) concludes from `β(M) = σ(M)`. -/
theorem isTISubset_sigmaSharp_of_sigma_eq_beta [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hσβ : OddOrder.BG.Ch3.S10.sigma M = OddOrder.BG.Ch3.S10.beta M) :
    IsTISubset (sigmaSharp M)
      (Subgroup.normalizer ((OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) : Set G)) := by
  intro g hov
  obtain ⟨a, haS, hgaS⟩ := hov
  simp only [sigmaSharp, sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff,
    SetLike.mem_coe] at haS hgaS
  obtain ⟨haMσ, _ha1⟩ := haS
  obtain ⟨hgaMσ, hga1⟩ := hgaS
  by_cases hgM : g ∈ M
  · exact le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) M hgM
  · exfalso
    -- `g a g⁻¹ ∈ M_σ ∩ (conj g • M_σ)`, nontrivial.
    have hgaConj : g * a * g⁻¹ ∈ MulAut.conj g • OddOrder.BG.Ch3.S10.Msigma M := by
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using haMσ
    have hmemInf : g * a * g⁻¹ ∈
        OddOrder.BG.Ch3.S10.Msigma M ⊓ MulAut.conj g • OddOrder.BG.Ch3.S10.Msigma M :=
      Subgroup.mem_inf.mpr ⟨hgaMσ, hgaConj⟩
    have hcard : Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M ⊓
        MulAut.conj g • OddOrder.BG.Ch3.S10.Msigma M) ≠ 1 := fun h =>
      hga1 (Subgroup.mem_bot.mp ((Subgroup.card_eq_one.mp h) ▸ hmemInf))
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hcard
    have : Fact p.Prime := ⟨hp⟩
    -- `p ∈ σ(M)` since the intersection is `≤ M_σ`.
    have hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma M :=
      OddOrder.BG.Ch3.S10.Msigma_isPiGroup M p (Nat.mem_primeFactors.mpr
        ⟨hp, hpdvd.trans (Subgroup.card_dvd_of_le inf_le_left), Nat.card_pos.ne'⟩)
    -- `p ∉ β(M)` by Lemma 12.17, since the intersection is `≤ M_σ ⊓ M^g`.
    have hle : OddOrder.BG.Ch3.S10.Msigma M ⊓ MulAut.conj g • OddOrder.BG.Ch3.S10.Msigma M ≤
        OddOrder.BG.Ch3.S10.Msigma M ⊓ MulAut.conj g • M :=
      inf_le_inf_left _ (Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr
        (OddOrder.BG.Ch3.S10.Msigma_le M))
    have hpβ := OddOrder.BG.Ch3.S12.Msigma_inf_conj_isBetaCompl hG hM hgM p
      (Nat.mem_primeFactors.mpr ⟨hp, hpdvd.trans (Subgroup.card_dvd_of_le hle), Nat.card_pos.ne'⟩)
    exact hpβ (hσβ ▸ hpσ)

/-- **BG Proposition 14.2(g), Frobenius core** (mmd L3850): in case `κ ⊆ τ₁` with `E₁ = K`
non-regular prime on `M_σ` and `U = E₂E₃ ≠ 1`, the type-`P₂` conclusions `σ(M) = β(M)` and
`|K|` prime hold.  `E = E₁ ⋉ U` is a Frobenius group (`isFrobeniusGroup_E_of_caseTau1`) with
`C_{M_σ}(U) = 1` and `M_σ` nilpotent (`Msigma_centralizer_E23_eq_bot_of_caseTau1`); since `E₁`
is prime on the nilpotent `M_σ`, Theorem 3.10(a) gives `|E₁|` prime.  Coprime fixed-point-free
action gives `U = [U, E₁] ≤ E'` (`le_commutator_of_coprime_inf_centralizer_eq_bot`), so `U`
is abelian (Corollary 12.10(b): `E'` abelian) and, by Lemma 12.19, `U` centralizes a Hall
`β(M)'`-subgroup `W` of `M_σ`; `W ≤ C_{M_σ}(U) = 1`, so `M_σ` is a `β(M)`-group, forcing
`σ(M) = β(M)`. -/
theorem sigma_eq_beta_and_prime_card_E1_of_caseTau1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃) (hE1ne : E₁ ≠ ⊥)
    (hKstar : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E₁ : Set G) ≠ ⊥)
    (hτ3 : ¬ (kappa M ∩ tau3 M).Nonempty) (hUne : (E₂ ⊔ E₃ : Subgroup G) ≠ ⊥) :
    OddOrder.BG.Ch3.S10.sigma M = OddOrder.BG.Ch3.S10.beta M ∧
      ∃ q : ℕ, q.Prime ∧ Nat.card ↥E₁ = q := by
  classical
  have hMsolv : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups h.mem_maximal
  have hMσM : OddOrder.BG.Ch3.S10.Msigma M ≤ M := OddOrder.BG.Ch3.S10.Msigma_le M
  have hUleE_sup : (E₂ ⊔ E₃ : Subgroup G) ≤ E := sup_le h.E₂_le h.E₃_le
  -- `E = E₁ ⋉ U` is Frobenius; `C_{M_σ}(U) = 1` and `M_σ` is nilpotent.
  have hfrob := isFrobeniusGroup_E_of_caseTau1 hG h hE1ne hKstar hτ3 hUne
  obtain ⟨hCU, hMnilp⟩ := Msigma_centralizer_E23_eq_bot_of_caseTau1 hG h hτ3 hUne
  -- `M_σ ≠ ⊥`.
  have hMσne : OddOrder.BG.Ch3.S10.Msigma M ≠ ⊥ := fun hb => hKstar (by rw [hb, bot_inf_eq])
  -- Coprime `|E₁|` and `|U|` (Frobenius kernel/complement).
  have hcopKU : Nat.Coprime (Nat.card ↥E₁) (Nat.card ↥(E₂ ⊔ E₃)) := by
    have hc := (hfrob.coprime_card_kernel_complement).symm
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₁_le).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUleE_sup).toEquiv] at hc
  -- `C_U(E₁) = ⊥` (regular action of `E₁` on `U`).
  have hCUK : (E₂ ⊔ E₃ : Subgroup G) ⊓ Subgroup.centralizer (E₁ : Set G) = ⊥ := by
    obtain ⟨⟨g₀, hg₀E1⟩, hg₀ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE1ne
    have hg₀1 : g₀ ≠ 1 := fun hc => hg₀ne (Subtype.ext hc)
    have hr := actsRegularlyOn_E23_E1_of_caseTau1 hG h hE1ne hKstar hτ3 g₀ hg₀E1 hg₀1
    rw [fixedByElement_def] at hr
    rw [eq_bot_iff, ← hr]
    exact inf_le_inf_left _
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hg₀E1))
  -- **Task B**: `U = [U, E₁] ≤ E'`.
  have hE1solv : Group.IsSolvable ↥E₁ :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective (h.E₁_le.trans h.E_le))
  have hUleE' : (E₂ ⊔ E₃ : Subgroup G) ≤ derivedInG E := by
    have hUcomm : (E₂ ⊔ E₃ : Subgroup G) ≤ ⁅E₁, E₂ ⊔ E₃⁆ :=
      OddOrder.BG.Ch2.S08.le_commutator_of_coprime_inf_centralizer_eq_bot
        (h.E₁_le.trans (h.E23_normal hG)) hcopKU hCUK
    have hcomm_le : (⁅E₁, E₂ ⊔ E₃⁆ : Subgroup G) ≤ ⁅E, E⁆ :=
      Subgroup.commutator_mono h.E₁_le hUleE_sup
    exact hUcomm.trans (le_of_le_of_eq hcomm_le (Subgroup.map_subtype_commutator E).symm)
  -- `U` is abelian (`U ≤ E'` and `E'` is abelian by Corollary 12.10(b)).
  have hE'ab : IsMulCommutative ↥(derivedInG E) := (nilpotent_sigmaComplement_abelian hG h).2.1.2
  have hUab : ∀ a b : ↥(E₂ ⊔ E₃), (a : G) * (b : G) = (b : G) * (a : G) := fun a b =>
    congrArg Subtype.val (hE'ab.is_comm.comm ⟨a, hUleE' a.2⟩ ⟨b, hUleE' b.2⟩)
  -- `E₁` is prime on `M_σ` ⟹ the `hcond3` hypothesis of Theorem 3.10(a).
  have hE1prime : ActsPrimeOn (OddOrder.BG.Ch3.S10.Msigma M) E₁ := E1_actsPrime hG h hE1ne
  have hcond3 : ∀ x ∈ E₁, x ≠ 1 →
      OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({x} : Set G) =
        OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E₁ : Set G) := by
    intro x hx hx1
    have := hE1prime x hx hx1
    rwa [fixedByElement_def, fixedBy_def] at this
  -- `E ≤ N_G(M_σ)`, coprime `|E|` `|M_σ|`, and `M_σ ⊔ E` solvable.
  have hEMσ : E ≤ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma M) :=
    h.E_le.trans (le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) M)
  have hcopEMσ : Nat.Coprime (Nat.card ↥E) (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M)) := by
    have h1 := (OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall hG h.mem_maximal).coprime_index
    rw [h.isComplement'_subgroupOf.symm.index_eq_card] at h1
    rw [Nat.coprime_comm] at h1
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E_le).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMσM).toEquiv] at h1
  have hsolvME : Group.IsSolvable ↥(OddOrder.BG.Ch3.S10.Msigma M ⊔ E) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective (sup_le hMσM h.E_le))
  -- **Theorem 3.10(a)**: `|E₁|` has prime order.
  have hKprime : ∃ q : ℕ, q.Prime ∧ Nat.card ↥E₁ = q :=
    OddOrder.BG.Ch1.S03.prime_card_complement_of_frobenius_conj hsolvME hUleE_sup h.E₁_le hfrob
      hUab hEMσ hMσne hcopEMσ hCU hcond3
  -- **σ = β**: Lemma 12.19 gives `W` a Hall `β'`-subgroup of `M_σ` with `E' ≤ C_G(W)`; since
  -- `U ≤ E'` we get `W ≤ C_{M_σ}(U) = 1`, so `M_σ` is a `β(M)`-group, forcing `σ(M) = β(M)`.
  obtain ⟨W, hWMσ, hWHall, hE'centW⟩ :=
    OddOrder.BG.Ch3.S12.derivedE_centralizes_betaComplement hG h
  have hWcentU : W ≤ Subgroup.centralizer ((E₂ ⊔ E₃ : Subgroup G) : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact ((Subgroup.mem_centralizer_iff.mp (hE'centW (hUleE' hu))) w hw).symm
  have hWbot : W = ⊥ := by
    have hWle : W ≤ OddOrder.BG.Ch3.S10.Msigma M ⊓
        Subgroup.centralizer ((E₂ ⊔ E₃ : Subgroup G) : Set G) := le_inf hWMσ hWcentU
    rw [hCU] at hWle; exact le_bot_iff.mp hWle
  have hπMσβ : ∀ p ∈ (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M)).primeFactors,
      p ∈ OddOrder.BG.Ch3.S10.beta M := by
    intro p hp
    have hidx : (W.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)).index =
        Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) := by
      rw [hWbot, Subgroup.bot_subgroupOf, Subgroup.index_bot]
    have hmem := hWHall.2 p (hidx ▸ hp)
    simp only [Set.mem_compl_iff, not_not] at hmem
    exact hmem
  have hσβ : OddOrder.BG.Ch3.S10.sigma M = OddOrder.BG.Ch3.S10.beta M := by
    refine Set.eq_of_subset_of_subset (fun p hp => ?_) (fun p hp =>
      OddOrder.BG.Ch3.S10.alpha_subset_sigma hG h.mem_maximal
        (OddOrder.BG.Ch3.S10.beta_subset_alpha M hp))
    -- `σ ⊆ β`: `p ∈ σ ⟹ p ∣ |M_σ|` (Hall) `⟹ p ∈ β`.
    refine hπMσβ p ?_
    obtain ⟨hpπM, _⟩ := (OddOrder.BG.Ch3.S10.mem_sigma_iff M p).mp hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpπM
    refine Nat.mem_primeFactors.mpr ⟨hpp, ?_, Nat.card_pos.ne'⟩
    by_contra hndvd
    have hHall := OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall hG h.mem_maximal
    have hcardM := Subgroup.card_mul_index ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)
    have hcardeq : Nat.card ↥((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) =
        Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMσM).toEquiv
    have hpM : p ∣ Nat.card ↥M := (Nat.mem_primeFactors.mp hpπM).2.1
    rw [← hcardM, hcardeq] at hpM
    have hpidx : p ∣ ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).index :=
      (hpp.dvd_mul.mp hpM).resolve_left hndvd
    exact hHall.2 p (Nat.mem_primeFactors.mpr
      ⟨hpp, hpidx, Subgroup.index_ne_zero_of_finite⟩) hp
  exact ⟨hσβ, hKprime⟩

/-- **BG Proposition 14.2(g), type-`P₂` ⟹ `U ≠ 1`** (mmd L3850, "`M ∈ 𝓜_{𝒫₂}`, i.e. `U ≠ 1`"):
in case `κ ⊆ τ₁` (so `κ(M) = τ₁(M)`), if `E₂E₃ = 1` then `E = E₁ = K`, hence `κ(M)` equals
`π(M) ∖ σ(M)` (every `σ(M)'`-prime of `M` divides `|E| = |E₁|` and lies in `κ` by the prime
action), so `M` is type `P₁`.  The contrapositive: `IsTypeP2 M ⟹ E₂E₃ ≠ 1`. -/
theorem E23_ne_bot_of_isTypeP2_caseTau1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃)
    (hE1prime : ActsPrimeOn (OddOrder.BG.Ch3.S10.Msigma M) E₁)
    (hCE1 : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E₁ : Set G) ≠ ⊥)
    (_hτ3 : ¬ (kappa M ∩ tau3 M).Nonempty) (hP2 : IsTypeP2 M) :
    (E₂ ⊔ E₃ : Subgroup G) ≠ ⊥ := by
  classical
  intro hUbot
  -- `E = E₁` since `E = E₁E₂E₃` and `E₂ = E₃ = ⊥`.
  have hE2bot : E₂ = ⊥ := le_bot_iff.mp (le_sup_left.trans hUbot.le)
  have hE3bot : E₃ = ⊥ := le_bot_iff.mp (le_sup_right.trans hUbot.le)
  have hEeq : E = E₁ := by
    rw [h.eq_sup hG, hE2bot, hE3bot, sup_bot_eq, sup_bot_eq]
  -- `κ(M) = π(M) ∖ σ(M)`, contradicting `IsTypeP2 M`.
  refine absurd ?_ hP2.2
  apply Set.eq_of_subset_of_subset
  · -- `κ(M) ⊆ π(M) ∖ σ(M)`.
    intro p hpκ
    obtain ⟨hpp, hpτ, P, hPelem, hPM, _⟩ := hpκ
    have hPcard : Nat.card ↥P = p := by rw [(mem_elemAbelianOfRank.mp hPelem).2, pow_one]
    have hpσ : p ∉ OddOrder.BG.Ch3.S10.sigma M := by
      rcases hpτ with hp | hp
      · exact tau1_subset_sigma_compl M hp
      · exact tau3_subset_sigma_compl M hp
    exact ⟨Nat.mem_primeFactors.mpr
      ⟨hpp, hPcard ▸ Subgroup.card_dvd_of_le hPM, Nat.card_pos.ne'⟩, hpσ⟩
  · -- `π(M) ∖ σ(M) ⊆ κ(M)`: `p ∣ |M|`, `p ∉ σ` ⟹ `p ∣ |E| = |E₁|` ⟹ `p ∈ κ`.
    intro p hp
    obtain ⟨hpπ, hpσ⟩ := hp
    obtain ⟨hpp, hpdvdM, _⟩ := Nat.mem_primeFactors.mp hpπ
    have : Fact p.Prime := ⟨hpp⟩
    have hpnMσ : ¬ p ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) := fun hdvd =>
      hpσ (OddOrder.BG.Ch3.S10.Msigma_isPiGroup M p
        (Nat.mem_primeFactors.mpr ⟨hpp, hdvd, Nat.card_pos.ne'⟩))
    have hdvdME : p ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) * Nat.card ↥E := by
      rw [h.card_Msigma_mul_card_E]; exact hpdvdM
    have hpE1 : p ∈ (Nat.card ↥E₁).primeFactors :=
      Nat.mem_primeFactors.mpr
        ⟨hpp, hEeq ▸ (hpp.dvd_mul.mp hdvdME).resolve_left hpnMσ, Nat.card_pos.ne'⟩
    exact mem_kappa_of_mem_primeFactors_card_E1 hG h hE1prime hCE1 hpE1

/-- **BG Proposition 14.2(e), second clause `S ⊄ K*`** (mmd L3828, proof L3846).  In a type-`P`
`E`-setup whose `τ₁`-Hall `E₁` lies in the `κ(M)`-subgroup `K` (so `K` is a `τ₁∪τ₃`-group and
`K* = C_{M_σ}(K)`), no Sylow `q`-subgroup `S` of `M_σ` is contained in `K*`.

This is the linchpin of Corollary 15.3(a): with it one shows `C_M(H)` is a `κ(M)'`-group for every
nontrivial Hall subgroup `H` of `M_σ` (if `H ≤ K*`, a Sylow `S ≤ H ≤ K*` of `M_σ` violates this).
It strengthens — and now subsumes — `kstar_ne_msigma_aux` (`K* ≠ M_σ`).

Proof (BG L3846).  **Part A** (`ℳ(K*) ≠ {M}`): pick `p₀ ∈ π(K)` and `X ∈ ℰ_{p₀}¹(K)`; then
`C_{M_σ}(X) ⊇ K* ≠ 1`, so Lemma 13.13 (`mem_sigma_of_tau1_tau3_centralize`), applied to a maximal
`Mi ⊇ N_G(X)`, gives `p₀ ∈ σ(Mi)`; as `p₀ ∈ τ₁∪τ₃ ⊆ σ(M)'` we get `Mi ≠ M`, and
`K* ≤ C_G(X) ≤ N_G(X) ≤ Mi`.  **Part B**: if `S ≤ K*`, take `X_S ∈ ℰ_q¹(S) ⊆ ℰ_q¹(K*)`; since
`E₁ ≤ K`, `X_S ≤ M_σ ⊓ C(E₁)`, so Lemma 13.6 (`maximalContaining_eq_singleton_of_E1`, `P = E₁`)
gives `ℳ(S) = {M}`; but `S ≤ K* ≤ Mi` forces `Mi ∈ ℳ(S) = {M}`, i.e. `Mi = M`, a contradiction. -/
theorem typeP_sylow_not_le_kstar [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ K Kstar : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    (hE1K : E₁ ≤ K) (hKE : K ≤ E) (hE1ne : E₁ ≠ ⊥) (hKne : K ≠ ⊥)
    (hKpi13 : ∀ p ∈ (Nat.card ↥K).primeFactors, p ∈ tau1 M ∪ tau3 M)
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hKstar_ne : Kstar ≠ ⊥)
    {q : ℕ} [Fact q.Prime] {S : Subgroup G} (hSne : S ≠ ⊥)
    (hSle : S ≤ OddOrder.BG.Ch3.S10.Msigma M) (hSq : IsPGroup q ↥S)
    (hSmax : ∀ T : Subgroup G, T ≤ OddOrder.BG.Ch3.S10.Msigma M → IsPGroup q ↥T → S ≤ T → S = T) :
    ¬ S ≤ Kstar := by
  classical
  intro hSK
  -- ## Part A: `ℳ(K*) ≠ {M}` — some maximal `Mi ≠ M` contains `K*`.
  obtain ⟨p₀, hp₀, hp₀dvd⟩ :=
    (Nat.card ↥K).exists_prime_and_dvd (fun hc => hKne (Subgroup.card_eq_one.mp hc))
  have : Fact p₀.Prime := ⟨hp₀⟩
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' p₀ hp₀dvd
  have hXcard : Nat.card ↥(Subgroup.zpowers (w : G)) = p₀ := by
    rw [Nat.card_zpowers]
    exact (orderOf_injective _ K.subtype_injective w).trans hw
  have hXelem : Subgroup.zpowers (w : G) ∈ elemAbelianOfRank G p₀ 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hXcard, by rw [hXcard, pow_one]⟩
  have hXK : Subgroup.zpowers (w : G) ≤ K := Subgroup.zpowers_le.mpr w.2
  have hXne : Subgroup.zpowers (w : G) ≠ ⊥ := ne_bot_of_mem_elemAbelianOfRank_one hXelem
  have hXM : Subgroup.zpowers (w : G) ≤ M := (hXK.trans hKE).trans h.E_le
  have hp₀τ13 : p₀ ∈ tau1 M ∪ tau3 M :=
    hKpi13 p₀ (Nat.mem_primeFactors.mpr ⟨hp₀, hp₀dvd, Nat.card_pos.ne'⟩)
  have hKstar_le_inf : Kstar ≤ OddOrder.BG.Ch3.S10.Msigma M ⊓
      Subgroup.centralizer ((Subgroup.zpowers (w : G)) : Set G) := by
    rw [hKstar]
    exact inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hXK))
  have hCX : OddOrder.BG.Ch3.S10.Msigma M ⊓
      Subgroup.centralizer ((Subgroup.zpowers (w : G)) : Set G) ≠ ⊥ :=
    fun hbot => hKstar_ne (le_bot_iff.mp (hKstar_le_inf.trans hbot.le))
  have hNlt : Subgroup.normalizer ((Subgroup.zpowers (w : G)) : Set G) < ⊤ :=
    normalizer_lt_top_of_le_of_ne_bot hG h.mem_maximal hXM hXne
  obtain ⟨Mi, hMico, hNMi⟩ :=
    (eq_top_or_exists_le_coatom (Subgroup.normalizer ((Subgroup.zpowers (w : G)) : Set
        G))).resolve_left
      hNlt.ne
  have hMimem : Mi ∈ maximalSubgroupsContaining
      (Subgroup.normalizer ((Subgroup.zpowers (w : G)) : Set G)) := ⟨hMico, hNMi⟩
  have hp₀σMi : p₀ ∈ OddOrder.BG.Ch3.S10.sigma Mi :=
    mem_sigma_of_tau1_tau3_centralize hG h hp₀τ13 hXelem ((hXK.trans hKE)) hCX hMimem
  have hMineM : Mi ≠ M := by
    intro hMieq
    have hp₀σM : p₀ ∈ OddOrder.BG.Ch3.S10.sigma M := hMieq ▸ hp₀σMi
    have hp₀nσM : p₀ ∉ OddOrder.BG.Ch3.S10.sigma M :=
      hp₀τ13.elim (fun hh => tau1_subset_sigma_compl M hh) (fun hh => tau3_subset_sigma_compl M hh)
    exact hp₀nσM hp₀σM
  have hKstar_le_Mi : Kstar ≤ Mi :=
    ((hKstar_le_inf.trans inf_le_right).trans (Subgroup.centralizer_le_normalizer _)).trans hNMi
  -- ## Part B: `S ≤ K*` contradicts `ℳ(S) = {M}` (Lemma 13.6).
  -- `q ∣ |S|` (nontrivial `q`-group), so pick `X_S ∈ ℰ_q¹(S)`.
  have hqdvdS : q ∣ Nat.card ↥S := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hSq
    rw [hk]
    refine dvd_pow_self q ?_
    rintro rfl
    rw [pow_zero] at hk
    exact hSne (Subgroup.card_eq_one.mp hk)
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' q hqdvdS
  have hXScard : Nat.card ↥(Subgroup.zpowers (v : G)) = q := by
    rw [Nat.card_zpowers]
    exact (orderOf_injective _ S.subtype_injective v).trans hv
  have hXSelem : Subgroup.zpowers (v : G) ∈ elemAbelianOfRank G q 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hXScard, by rw [hXScard, pow_one]⟩
  have hXS_le_S : Subgroup.zpowers (v : G) ≤ S := Subgroup.zpowers_le.mpr v.2
  have hXS_le_Kstar : Subgroup.zpowers (v : G) ≤ Kstar := hXS_le_S.trans hSK
  -- `X_S ≤ M_σ ⊓ C(E₁)` (`X_S ≤ K* = M_σ ⊓ C(K) ≤ M_σ ⊓ C(E₁)`, since `E₁ ≤ K`).
  have hXC : Subgroup.zpowers (v : G) ≤ OddOrder.BG.Ch3.S10.Msigma M ⊓
      Subgroup.centralizer (E₁ : Set G) := by
    have h1 : Subgroup.zpowers (v : G) ≤
        OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) := hKstar ▸ hXS_le_Kstar
    exact le_inf (h1.trans inf_le_left)
      ((h1.trans inf_le_right).trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hE1K)))
  -- `q ∈ σ(M)` (`X_S ≤ M_σ`).
  have hqσ : q ∈ OddOrder.BG.Ch3.S10.sigma M :=
    OddOrder.BG.Ch3.S10.Msigma_isPiGroup M q (Nat.mem_primeFactors.mpr
      ⟨Fact.out, hqdvdS.trans (Subgroup.card_dvd_of_le hSle), Nat.card_pos.ne'⟩)
  -- Lemma 13.6: `ℳ(S) = {M}`.
  have hMS : maximalSubgroupsContaining S = {M} :=
    (maximalContaining_eq_singleton_of_E1 hG h hqσ (le_refl E₁) hE1ne hXSelem hXC hSle hSq hSmax).2
  -- `S ≤ K* ≤ Mi`, so `Mi ∈ ℳ(S) = {M}`, i.e. `Mi = M`, contradicting `Mi ≠ M`.
  have hMiS : Mi ∈ maximalSubgroupsContaining S := ⟨hMico, hSK.trans hKstar_le_Mi⟩
  rw [hMS, Set.mem_singleton_iff] at hMiS
  exact hMineM hMiS

/-- **BG Proposition 14.2(e), `K* ⊊ M_σ` form** (mmd L3846).  Immediate corollary of
`typeP_sylow_not_le_kstar`: a Sylow `S` of `M_σ` cannot lie in `K*`, so `K* ≠ M_σ` (else every
`S ≤ M_σ = K*`).  Retained as a named lemma for the `typeP_structure` `(e)` conjunct. -/
theorem kstar_ne_msigma_aux [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ K Kstar : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    (hE1K : E₁ ≤ K) (hKE : K ≤ E) (hE1ne : E₁ ≠ ⊥) (hKne : K ≠ ⊥)
    (hKpi13 : ∀ p ∈ (Nat.card ↥K).primeFactors, p ∈ tau1 M ∪ tau3 M)
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hKstar_ne : Kstar ≠ ⊥) :
    Kstar ≠ OddOrder.BG.Ch3.S10.Msigma M := by
  classical
  intro hKMσ
  -- Pick `p ∈ π(M_σ)` and a Sylow `S = Syl_p(M_σ)`; then `S ≤ M_σ = K*`, contradicting
  -- `typeP_sylow_not_le_kstar` (`S ⊄ K*`).
  have hMσne : OddOrder.BG.Ch3.S10.Msigma M ≠ ⊥ :=
    OddOrder.BG.Ch3.S10.Msigma_ne_bot hG h.mem_maximal
  obtain ⟨p, hp, hpdvd⟩ := (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M)).exists_prime_and_dvd
    (fun hc => hMσne (Subgroup.card_eq_one.mp hc))
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hSMσ, hSq, _, hScard⟩ := exists_einvariant_sylow_Msigma hG h p
  have hSmax : ∀ T : Subgroup G, T ≤ OddOrder.BG.Ch3.S10.Msigma M → IsPGroup p ↥T → S ≤ T → S = T :=
    fun T hTM hTq hST => eq_of_le_of_isPGroup_card_eq_factorization hScard hTM hTq hST
  have hSne : S ≠ ⊥ := by
    intro hSbot
    have hpdvdS : p ∣ Nat.card ↥S := by
      rw [hScard]
      exact dvd_pow_self p (hp.factorization_pos_of_dvd Nat.card_pos.ne' hpdvd).ne'
    rw [Subgroup.card_eq_one.mpr hSbot] at hpdvdS
    exact hp.one_lt.ne' (Nat.dvd_one.mp hpdvdS)
  exact typeP_sylow_not_le_kstar hG h hE1K hKE hE1ne hKne hKpi13 hKstar hKstar_ne
    hSne hSMσ hSq hSmax (by rw [hKMσ]; exact hSMσ)

/-- **BG Proposition 14.2** (mmd L3778): structure of a type-`P` maximal subgroup
("nearly everything proved in §13" about `M ∈ 𝓜_𝓟`).

`K` = Hall `κ(M)`-subgroup of `M`, `K* = C_{M_σ}(K)`, `U` = Hall `(κ(M) ∪ σ(M))'`-subgroup.
BG states seven parts (a)–(g).  This bundle captures the prime action `(a)`, `K* ≠ 1` and the
second half of `(c)`, the normalizer identity `N_M(X) = K × K*` `(b1)`, the `(d)` clause
`K* ∩ M^g = 1` for `g ∉ M`, and the type-`P₂` consequences `(g)` (`σ = β`, `|K|` prime,
`M_σ` a `TI`-subgroup).

**Status of the rest (issue 0177 §14 audit, 2026-08-08 — the old "deferred" list was mostly
stale).**  These are proved, just not in this bundle:

* `(b2)` = `LocalStructure.typeP_elemAbelian_le_neighbor_Msigma`
* `(d)`, clause `K ∩ K^g = 1` = `SigmaCovers.typeP_kappaHall_inf_conj_eq_bot`
* `(e)` = `LocalStructure.typeP_sylow_not_le_kstar_of_isHall`
* `(f)` = `TypePDuality.typeP_sigma_subgroup_le_Msigma`

⚠ **Two pieces are genuinely NOT formalized anywhere** (verified by concept-form grep, not by
reading notes):

1. `(a)`, second half — `K` acts **regularly** on some abelian Hall `(κ(M) ∪ σ(M))'`-subgroup
   `U` of `M`, and `U M_σ` is a normal complement of `K` in `M`.  (`U`'s Hall property is an
   *assumed* input `_hU` here, and is unused.)
2. `(g)`, third clause — `M_σ` is **nilpotent** for `M ∈ 𝓜_{𝒫₂}`.  Downstream `AppE_*` files
   currently take this as a hypothesis (`hMσnil`) rather than deriving it.

See `notes/bg/s14_typeP_counting.md` and issue 0177.

**Faithfulness note (2026-06-14):** a spurious `M_σ ≤ N_G(K*)` conjunct was removed — it is
not one of BG's seven parts and is false in general (`K = C_q` acting on a Heisenberg
`M_σ = p^{1+2}` by `a ↦ aʳ, b ↦ b, c ↦ cʳ` gives `K* = ⟨b⟩`, which is **not** normal in
`M_σ` since `a b a⁻¹ = bc ∉ ⟨b⟩`). -/
theorem typeP_structure [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (_hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      (U.subgroupOf M)) :
    ActsPrimeOn (OddOrder.BG.Ch3.S10.Msigma M) K ∧
      Kstar ≠ ⊥ ∧
      (∀ p : ℕ, p.Prime → ∀ X : Subgroup G, X ∈ elemAbelianOfRank G p 1 → X ≤ K →
        Subgroup.normalizer (X : Set G) ⊓ M = K ⊔ Kstar) ∧
      (∀ g : G, g ∉ M → Kstar ⊓ (MulAut.conj g • M) = ⊥) ∧
      (IsTypeP2 M → OddOrder.BG.Ch3.S10.sigma M = OddOrder.BG.Ch3.S10.beta M ∧
        ∃ q : ℕ, q.Prime ∧ Nat.card ↥K = q ∧
          IsTISubset (sigmaSharp M) (Subgroup.normalizer
            ((OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) : Set G))) ∧
      (∀ p : ℕ, p.Prime → ∀ X : Subgroup G, X ∈ elemAbelianOfRank G p 1 → X ≤ Kstar →
        maximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M}) ∧
      Kstar ≠ OddOrder.BG.Ch3.S10.Msigma M := by
  classical
  -- `K` is a `σ(M)'`-subgroup (a Hall `κ(M)`-subgroup, and `κ(M) ⊆ σ(M)'`).
  have hK_pi : Subgroup.IsPiSubgroup ((OddOrder.BG.Ch3.S10.sigma M)ᶜ) K := by
    intro p hp
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hp
    exact kappa_subset_sigmaCompl (hK.1 p hp)
  -- Choose a §12 `E`-setup whose `M_σ`-complement `E` contains `K` (BG: "take `E ⊇ K`").
  obtain ⟨E, E₁, E₂, E₃, hsetup, hKE, hE_pi⟩ :=
    OddOrder.BG.Ch3.S12.exists_subgroupESetup_with_le hG hM hKM hK_pi
  -- BG splits on whether `κ(M) ∩ τ₃(M) = ∅` (i.e. `E₃ ≠ 1` and `E₃` non-regular vs `κ ⊆ τ₁`).
  by_cases hτ3 : (kappa M ∩ tau3 M).Nonempty
  · -- Case `κ(M) ∩ τ₃(M) ≠ ∅`: `E₃` acts non-regularly on `M_σ` (the `κ`-witness conjugates
    -- into `E₃`), so Corollary 13.11 gives `E = E₁ ⊔ E₃`, `E` prime on `M_σ`, and every
    -- `X ∈ ℰ¹(E)` normal in `E`; then `K = E`, and the conjuncts follow.
    obtain ⟨p, hpmem⟩ := hτ3
    rw [Set.mem_inter_iff] at hpmem
    obtain ⟨hpκ, hpτ3⟩ := hpmem
    have hp : p.Prime := Nat.prime_of_mem_primeFactors ((mem_tau3_iff M p).mp hpτ3).2.1
    obtain ⟨hE3ne, hreg⟩ := E3_not_regular_of_mem_kappa_tau3 hG hsetup hp hpκ hpτ3
    obtain ⟨hE1ne, hEeq, hEprime, hEnorm⟩ := E3_not_regular_consequences hG hsetup hE3ne hreg
    -- Extract an `E₃`-witness `x` with `C_{M_σ}(x) ≠ 1` from non-regularity.
    obtain ⟨x, hxE3, hxne, hxC⟩ : ∃ x ∈ E₃, x ≠ 1 ∧
        OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ := by
      by_contra hcon
      push Not at hcon
      exact hreg fun y hy hy1 => hcon y hy hy1
    -- `π(E) ⊆ κ(M)`, so `E` is a `κ(M)`-subgroup; the Hall `κ(M)`-subgroup `K ≤ E` forces `K = E`.
    have hEpi : Ch03.Subgroup.IsPiGroup (kappa M) (E.subgroupOf M) := by
      intro q hq
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsetup.E_le).toEquiv] at hq
      exact mem_kappa_of_mem_primeFactors_card_E hG hsetup hEprime hxE3 hxne hxC hq
    have hEdvdK : Nat.card ↥E ∣ Nat.card ↥K := by
      have hd := hK.card_dvd_of_isPiGroup hEpi
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsetup.E_le).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hd
    have hKEeq : K = E :=
      Subgroup.eq_of_le_of_card_ge hKE (Nat.dvd_antisymm hEdvdK (Subgroup.card_dvd_of_le hKE)).le
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- (a) prime action: immediate from `K = E` and Corollary 13.11.
      rw [hKEeq]; exact hEprime
    · -- `K^* = C_{M_σ}(K) = C_{M_σ}(E) ≠ 1` (prime action + the non-regular witness).
      rw [hKstar, hKEeq]
      exact Msigma_inf_centralizer_E_ne_bot_of_actsPrime_nonregular hEprime hsetup.E₃_le hreg
    · -- (b1) `N_M(X) = K ⊔ K^*` for rank-one `X ≤ K`.  `⊇`: `K = E ≤ N_G(X)` by Corollary 13.11
      -- (`hEnorm`), and `K^* = C_{M_σ}(K) ≤ C_G(X) ≤ N_G(X)`, `K^* ≤ M_σ ≤ M`.  `⊆` (BG "clear",
      -- needs the `M = M_σ ⋊ E` semidirect structure) is deferred.
      intro p hp X hXrank hXK
      have : Fact p.Prime := ⟨hp⟩
      refine le_antisymm ?_ ?_
      · -- ⊆: decompose `n = s·e` (`s ∈ M_σ`, `e ∈ E`) in `↥M`; for `g ∈ X#`, `s·(ege⁻¹)·s⁻¹ =
        -- ngn⁻¹ ∈ X ≤ E`, so `[s, ege⁻¹] ∈ M_σ ∩ E = 1`, i.e. `s` centralizes `ege⁻¹ ∈ E#`.
        -- Prime action then gives `s ∈ C_{M_σ}(E) = K*`, and `e ∈ E = K`.
        intro n hn
        rw [Subgroup.mem_inf] at hn
        obtain ⟨hnX, hnM⟩ := hn
        have hMσnorm : ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).Normal := by
          rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
        have hsuptop : (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M ⊔ E.subgroupOf M = ⊤ := by
          rw [← Subgroup.subgroupOf_sup (OddOrder.BG.Ch3.S10.Msigma_le M) hsetup.E_le,
            hsetup.E_compl_sup, Subgroup.subgroupOf_self]
        obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_left.mp
          (hsuptop ▸ Subgroup.mem_top (⟨n, hnM⟩ : ↥M))
        have hs : (a : G) ∈ OddOrder.BG.Ch3.S10.Msigma M := Subgroup.mem_subgroupOf.mp ha
        have he : (b : G) ∈ E := Subgroup.mem_subgroupOf.mp hb
        have hse : (a : G) * (b : G) = n := by
          have h := congrArg (Subtype.val) hab; simpa using h
        -- A nonidentity `g ∈ X` and `y' = e g e⁻¹ ∈ E#`.
        obtain ⟨⟨g, hgX⟩, hg1⟩ :=
          Subgroup.ne_bot_iff_exists_ne_one.mp (ne_bot_of_mem_elemAbelianOfRank_one hXrank)
        have hg1' : g ≠ 1 := fun h => hg1 (Subtype.ext h)
        have hgE : g ∈ E := (hXK.trans hKEeq.le) hgX
        have hy'E : (b : G) * g * (b : G)⁻¹ ∈ E := E.mul_mem (E.mul_mem he hgE) (E.inv_mem he)
        have hy'1 : (b : G) * g * (b : G)⁻¹ ≠ 1 := by
          rw [show (b : G) * g * (b : G)⁻¹ = MulAut.conj (b : G) g from (MulAut.conj_apply _
              _).symm]
          exact fun hc => hg1' ((MulAut.conj (b : G)).map_eq_one_iff.mp hc)
        -- `s · y' · s⁻¹ = n g n⁻¹ ∈ X ≤ E`.
        have hsy' : (a : G) * ((b : G) * g * (b : G)⁻¹) * (a : G)⁻¹ = n * g * n⁻¹ := by
          rw [← hse]; group
        have hngn : n * g * n⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hnX g).mp hgX
        -- `[s, y'] ∈ M_σ ∩ E = 1`, so `s` centralizes `y'`.
        have hsy'E : (a : G) * ((b : G) * g * (b : G)⁻¹) * (a : G)⁻¹ ∈ E :=
          hsy' ▸ (hXK.trans hKEeq.le) hngn
        have hy'N : (b : G) * g * (b : G)⁻¹ ∈
            Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma M) :=
          le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) M (hsetup.E_le hy'E)
        have hcommMσ : (a : G) * ((b : G) * g * (b : G)⁻¹) * (a : G)⁻¹ *
            ((b : G) * g * (b : G)⁻¹)⁻¹ ∈ OddOrder.BG.Ch3.S10.Msigma M := by
          have h1 : ((b : G) * g * (b : G)⁻¹) * (a : G)⁻¹ * ((b : G) * g * (b : G)⁻¹)⁻¹ ∈
              OddOrder.BG.Ch3.S10.Msigma M :=
            (Subgroup.mem_normalizer_iff.mp hy'N (a : G)⁻¹).mp
              ((OddOrder.BG.Ch3.S10.Msigma M).inv_mem hs)
          have heq : (a : G) * ((b : G) * g * (b : G)⁻¹) * (a : G)⁻¹ *
              ((b : G) * g * (b : G)⁻¹)⁻¹ =
              (a : G) * (((b : G) * g * (b : G)⁻¹) * (a : G)⁻¹ *
                ((b : G) * g * (b : G)⁻¹)⁻¹) := by group
          rw [heq]; exact (OddOrder.BG.Ch3.S10.Msigma M).mul_mem hs h1
        have hcomm1 : (a : G) * ((b : G) * g * (b : G)⁻¹) * (a : G)⁻¹ *
            ((b : G) * g * (b : G)⁻¹)⁻¹ = 1 := by
          have hmem : _ ∈ OddOrder.BG.Ch3.S10.Msigma M ⊓ E :=
            Subgroup.mem_inf.mpr ⟨hcommMσ, E.mul_mem hsy'E (E.inv_mem hy'E)⟩
          rw [hsetup.E_compl_inf] at hmem; exact Subgroup.mem_bot.mp hmem
        -- `s ∈ C_{M_σ}(y') = C_{M_σ}(E) = K*`, `e ∈ E = K`, so `n = s·e ∈ K ⊔ K*`.
        have hscent : (a : G) ∈ Subgroup.centralizer ({(b : G) * g * (b : G)⁻¹} : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro z hz
          rw [Set.mem_singleton_iff.mp hz]
          exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hcomm1)).symm
        have hsKstar : (a : G) ∈ Kstar := by
          rw [hKstar, hKEeq, ← fixedBy_def, ← hEprime _ hy'E hy'1, fixedByElement_def]
          exact Subgroup.mem_inf.mpr ⟨hs, hscent⟩
        rw [← hse]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hsKstar)
          (Subgroup.mem_sup_left (hKEeq ▸ he))
      · refine sup_le ?_ ?_
        · rw [hKEeq]
          exact le_inf (hEnorm p hp X hXrank (hXK.trans hKEeq.le)) (hKEeq ▸ hKM)
        · rw [hKstar]
          exact le_inf
            (inf_le_right.trans ((Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hXK)).trans
              (Subgroup.centralizer_le_normalizer _)))
            (inf_le_left.trans (OddOrder.BG.Ch3.S10.Msigma_le M))
    · -- (d) `K^* ∩ M^g = 1` for `g ∉ M`: a rank-one `X ≤ K^* ∩ M^g` has `C_G(X) ⊆ M` by (c),
      -- and `X ≤ M^g` with Theorem 10.1(e) forces `g ∈ M`.
      intro g hgM
      by_contra hne
      obtain ⟨q, hq, hqdvd⟩ :=
        (Nat.card ↥(Kstar ⊓ (MulAut.conj g • M))).exists_prime_and_dvd
          (fun hc => hne (Subgroup.card_eq_one.mp hc))
      have : Fact q.Prime := ⟨hq⟩
      obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' q hqdvd
      have hXcard : Nat.card ↥(Subgroup.zpowers (w : G)) = q := by
        rw [Nat.card_zpowers]
        exact (orderOf_injective _ (Kstar ⊓ (MulAut.conj g • M)).subtype_injective w).trans hw
      have hXelem : Subgroup.zpowers (w : G) ∈ elemAbelianOfRank G q 1 :=
        ⟨Subgroup.IsElementaryAbelian.of_card_prime hXcard, by rw [hXcard, pow_one]⟩
      have hXle : Subgroup.zpowers (w : G) ≤ Kstar ⊓ (MulAut.conj g • M) :=
        Subgroup.zpowers_le.mpr w.2
      have hKstarE : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E : Set G) := by
        rw [hKstar, hKEeq]
      have hXK : Subgroup.zpowers (w : G) ≤
          OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E : Set G) :=
        hKstarE ▸ (hXle.trans inf_le_left)
      -- (c): `C_G(X) ⊆ M`.
      have h𝓜 := maximalContaining_centralizer_of_le_Msigma_centralizer_E hG hsetup hE1ne hXelem hXK
      have hCM : Subgroup.centralizer ((Subgroup.zpowers (w : G)) : Set G) ≤ M :=
        (mem_maximalSubgroupsContaining.mp (by rw [h𝓜]; exact Set.mem_singleton M)).2
      -- `X ≤ M_σ ≤ M`, `q ∈ σ(M)`, `X` a `q`-group.
      have hXMσ : Subgroup.zpowers (w : G) ≤ OddOrder.BG.Ch3.S10.Msigma M := hXK.trans inf_le_left
      have hXM : Subgroup.zpowers (w : G) ≤ M := hXMσ.trans (OddOrder.BG.Ch3.S10.Msigma_le M)
      have hqσ : q ∈ OddOrder.BG.Ch3.S10.sigma M :=
        OddOrder.BG.Ch3.S10.Msigma_isPiGroup M q (Nat.mem_primeFactors.mpr
          ⟨hq, hXcard ▸ Subgroup.card_dvd_of_le hXMσ, Nat.card_pos.ne'⟩)
      have hXbot : Subgroup.zpowers (w : G) ≠ ⊥ := ne_bot_of_mem_elemAbelianOfRank_one hXelem
      have hXp : IsPGroup q ↥(Subgroup.zpowers (w : G)) := hXelem.1.isPGroup
      -- `X ≤ M^g` gives `conj g⁻¹ • X ≤ M`; Theorem 10.1(e) yields `g⁻¹ ∈ M`.
      have hXgM : Subgroup.zpowers (w : G) ≤ MulAut.conj g • M := hXle.trans inf_le_right
      have hconj : MulAut.conj g⁻¹ • Subgroup.zpowers (w : G) ≤ M := by
        have h1 : MulAut.conj g⁻¹ • Subgroup.zpowers (w : G) ≤
            MulAut.conj g⁻¹ • (MulAut.conj g • M) :=
          (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := MulAut.conj g⁻¹)).mpr hXgM
        rwa [smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul] at h1
      have hg' : g⁻¹ ∈ M :=
        (OddOrder.BG.Ch3.S10.fusion_control_of_mem_sigma hG hM hqσ hXbot hXp).2.2.2.2
          hXM hCM g⁻¹ hconj
      exact hgM (by simpa using M.inv_mem hg')
    · -- (g) In the `κ ∩ τ₃` case `K = E`, so `κ(M) = π(M) ∖ σ(M)`, i.e. `M` is type `P₁`;
      -- this contradicts `IsTypeP2 M` (whose defining clause is `κ(M) ≠ π(M) ∖ σ(M)`).
      intro hP2
      refine absurd ?_ hP2.2
      apply Set.eq_of_subset_of_subset
      · -- `κ(M) ⊆ π(M) ∖ σ(M)`: each `p ∈ κ` is a prime dividing `|M|` (witness `P ≤ M`) and `∉ σ`.
        intro p hpκ
        obtain ⟨hpp, hpτ, P, hPelem, hPM, _⟩ := hpκ
        have hPcard : Nat.card ↥P = p := by rw [(mem_elemAbelianOfRank.mp hPelem).2, pow_one]
        have hpσ : p ∉ OddOrder.BG.Ch3.S10.sigma M := by
          rcases hpτ with h | h
          · exact tau1_subset_sigma_compl M h
          · exact tau3_subset_sigma_compl M h
        exact ⟨Nat.mem_primeFactors.mpr
            ⟨hpp, hPcard ▸ Subgroup.card_dvd_of_le hPM, Nat.card_pos.ne'⟩, hpσ⟩
      · -- `π(M) ∖ σ(M) ⊆ κ(M)`: `p ∣ |M|`, `p ∉ σ` ⟹ `p ∣ |E|` ⟹ `p ∈ κ` (by `mem_kappa…`).
        intro p hp
        obtain ⟨hpπ, hpσ⟩ := hp
        obtain ⟨hpp, hpdvdM, _⟩ := Nat.mem_primeFactors.mp hpπ
        have : Fact p.Prime := ⟨hpp⟩
        have hpnMσ : ¬ p ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) := fun hdvd =>
          hpσ (OddOrder.BG.Ch3.S10.Msigma_isPiGroup M p
            (Nat.mem_primeFactors.mpr ⟨hpp, hdvd, Nat.card_pos.ne'⟩))
        have hdvdME : p ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) * Nat.card ↥E := by
          rw [hsetup.card_Msigma_mul_card_E]; exact hpdvdM
        have hpE : p ∈ (Nat.card ↥E).primeFactors :=
          Nat.mem_primeFactors.mpr
            ⟨hpp, (hpp.dvd_mul.mp hdvdME).resolve_left hpnMσ, Nat.card_pos.ne'⟩
        exact mem_kappa_of_mem_primeFactors_card_E hG hsetup hEprime hxE3 hxne hxC hpE
    · -- (c) `ℳ(C_G(X)) = {M}` for `X ∈ ℰ¹(K*)`: `K* = C_{M_σ}(K) = C_{M_σ}(E)` (`K = E`),
      -- so the `C(E)`-form Corollary 12.14 helper (`…_centralizer_E`) applies directly.
      intro p hp X hXelem hXKstar
      have : Fact p.Prime := ⟨hp⟩
      exact maximalContaining_centralizer_of_le_Msigma_centralizer_E hG hsetup hE1ne hXelem
        (hKEeq ▸ hKstar ▸ hXKstar)
    · -- (e-core) `K* ⊊ M_σ` (BG Prop 14.2(e)): apply `kstar_ne_msigma_aux` with `E₁ ≤ K = E`.
      have hE1K : E₁ ≤ K := by rw [hKEeq]; exact hsetup.E₁_le
      have hKstar_ne : Kstar ≠ ⊥ := by
        rw [hKstar, hKEeq]
        exact Msigma_inf_centralizer_E_ne_bot_of_actsPrime_nonregular hEprime hsetup.E₃_le hreg
      refine kstar_ne_msigma_aux hG hsetup hE1K (le_of_eq hKEeq) hE1ne
        (fun hKbot => hE1ne (le_bot_iff.mp (hE1K.trans hKbot.le))) (fun q hq => ?_) hKstar hKstar_ne
      exact kappa_subset_tau1_union_tau3 (hK.1 q (by
        rwa [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hq))
  · -- Case `κ(M) ⊆ τ₁(M)`: `κ = τ₁`, and `K` is `M`-conjugate to `E₁` (both Hall `κ(M)`).
    -- Conjugate the `E`-setup by `w` (`conj w • E₁ = K`) and read the conjuncts off the new setup
    -- via the `E₁`-lemmas (Theorem 13.5 etc.), exactly as in case `τ₃` with `E₁` in place of `E`.
    have hMsolv : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hsetup.mem_maximal
    have hκτ1 : ∀ p ∈ kappa M, p ∈ tau1 M := fun p hpκ =>
      (kappa_subset_tau1_union_tau3 hpκ).resolve_right
        (fun hpτ3 => hτ3 ⟨p, Set.mem_inter hpκ hpτ3⟩)
    obtain ⟨p₀, hp₀κ⟩ := hP
    -- `E₁ ≠ 1`, non-regular, prime on `M_σ`, `C_{M_σ}(E₁) ≠ 1`.
    obtain ⟨hE1ne, hE1nonreg⟩ := E1_not_regular_of_mem_kappa_tau1 hG hsetup
      (prime_of_mem_kappa hp₀κ) hp₀κ (hκτ1 p₀ hp₀κ)
    have hE1prime : ActsPrimeOn (OddOrder.BG.Ch3.S10.Msigma M) E₁ := E1_actsPrime hG hsetup hE1ne
    have hCE1 : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E₁ : Set G) ≠ ⊥ :=
      Msigma_inf_centralizer_E_ne_bot_of_actsPrime_nonregular hE1prime (le_refl E₁) hE1nonreg
    -- `E₁` is a Hall `κ(M)`-subgroup of `E` (π(E₁) ⊆ κ by coverage; index avoids `κ ⊆ τ₁`).
    have hE1HallκE : Ch03.IsHallSubgroup (kappa M) (E₁.subgroupOf E) :=
      ⟨fun p hp => mem_kappa_of_mem_primeFactors_card_E1 hG hsetup hE1prime hCE1
          (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsetup.E₁_le).toEquiv] at hp),
        fun p hp hpκ => hsetup.E₁_hall.2 p hp (hκτ1 p hpκ)⟩
    have hE1Hallκ : Ch03.IsHallSubgroup (kappa M) (E₁.subgroupOf M) :=
      hallPiece_isHall_in_M hG hsetup hsetup.E₁_le hE1HallκE kappa_subset_sigmaCompl
    -- WLOG `conj w • E₁ = K`; conjugate the setup so its new `E₁` is `K`.
    obtain ⟨w, hwM, hw⟩ := OddOrder.BG.Ch1.S06.exists_conj_eq_of_isHall_subgroupOf hMsolv
      (hsetup.E₁_le.trans hsetup.E_le) hKM hE1Hallκ hK
    have h' := SubgroupESetup.conj' hsetup hwM
    rw [hw] at h'
    -- Read off `K = (h').E₁` facts.
    obtain ⟨hKne, hKnonreg⟩ := E1_not_regular_of_mem_kappa_tau1 hG h'
      (prime_of_mem_kappa hp₀κ) hp₀κ (hκτ1 p₀ hp₀κ)
    have hKprime : ActsPrimeOn (OddOrder.BG.Ch3.S10.Msigma M) K := E1_actsPrime hG h' hKne
    refine ⟨hKprime, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- (K* ≠ 1) `= C_{M_σ}(K) ≠ 1`.
      rw [hKstar]
      exact Msigma_inf_centralizer_E_ne_bot_of_actsPrime_nonregular hKprime (le_refl K) hKnonreg
    · -- (b1) `N_M(X) = K ⊔ K*` for rank-one `X ≤ K`.  Here `K = E₁' ⊊ E'`, so the case-`τ₃`
      -- argument is twisted: decompose `n = a·b` (`a ∈ M_σ`, `b ∈ E'`); `[a, bgb⁻¹] = 1` gives
      -- `ngn⁻¹ = bgb⁻¹`, so `s' := b⁻¹n` centralizes `g`, hence `s' ∈ C_{M_σ}(K) = K*` (prime
      -- action), `n = b·s'`, and `b = n·s'⁻¹ ∈ N_G(X) ⊓ E' ≤ K` by the Frobenius normalizer lemma.
      intro p hp X hXrank hXK
      have : Fact p.Prime := ⟨hp⟩
      have hKstar_ne : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) ≠ ⊥ :=
        Msigma_inf_centralizer_E_ne_bot_of_actsPrime_nonregular hKprime (le_refl K) hKnonreg
      have hKcentX : K ≤ Subgroup.centralizer (X : Set G) := by
        let : CommGroup ↥K := (subgroupE_basic hG h').2.2.2.1.1.commGroup
        intro k hk
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact congrArg Subtype.val (mul_comm (⟨y, hXK hy⟩ : ↥K) (⟨k, hk⟩ : ↥K))
      refine le_antisymm ?_ ?_
      · -- ⊆
        intro n hn
        rw [Subgroup.mem_inf] at hn
        obtain ⟨hnX, hnM⟩ := hn
        have hMσnorm : ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).Normal := by
          rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
        have hsuptop : (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M ⊔
            (MulAut.conj w • E).subgroupOf M = ⊤ := by
          rw [← Subgroup.subgroupOf_sup (OddOrder.BG.Ch3.S10.Msigma_le M) h'.E_le,
            h'.E_compl_sup, Subgroup.subgroupOf_self]
        obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_left.mp
          (hsuptop ▸ Subgroup.mem_top (⟨n, hnM⟩ : ↥M))
        have hs : (a : G) ∈ OddOrder.BG.Ch3.S10.Msigma M := Subgroup.mem_subgroupOf.mp ha
        have he : (b : G) ∈ MulAut.conj w • E := Subgroup.mem_subgroupOf.mp hb
        have hbM : (b : G) ∈ M := h'.E_le he
        have hse : (a : G) * (b : G) = n := by have hh := congrArg Subtype.val hab; simpa using hh
        obtain ⟨⟨g, hgX⟩, hg1⟩ :=
          Subgroup.ne_bot_iff_exists_ne_one.mp (ne_bot_of_mem_elemAbelianOfRank_one hXrank)
        have hg1' : g ≠ 1 := fun hc => hg1 (Subtype.ext hc)
        have hgK : g ∈ K := hXK hgX
        have hgE' : g ∈ MulAut.conj w • E := h'.E₁_le hgK
        have hy'E : (b : G) * g * (b : G)⁻¹ ∈ MulAut.conj w • E :=
          (MulAut.conj w • E).mul_mem ((MulAut.conj w • E).mul_mem he hgE')
            ((MulAut.conj w • E).inv_mem he)
        have hngn : n * g * n⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hnX g).mp hgX
        have hsy' : (a : G) * ((b : G) * g * (b : G)⁻¹) * (a : G)⁻¹ = n * g * n⁻¹ := by
          rw [← hse]; group
        have hsy'E : (a : G) * ((b : G) * g * (b : G)⁻¹) * (a : G)⁻¹ ∈ MulAut.conj w • E :=
          hsy' ▸ (hXK.trans h'.E₁_le) hngn
        have hy'N : (b : G) * g * (b : G)⁻¹ ∈
            Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma M) :=
          le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) M (h'.E_le hy'E)
        have hcommMσ : (a : G) * ((b : G) * g * (b : G)⁻¹) * (a : G)⁻¹ *
            ((b : G) * g * (b : G)⁻¹)⁻¹ ∈ OddOrder.BG.Ch3.S10.Msigma M := by
          have h1 : ((b : G) * g * (b : G)⁻¹) * (a : G)⁻¹ * ((b : G) * g * (b : G)⁻¹)⁻¹ ∈
              OddOrder.BG.Ch3.S10.Msigma M :=
            (Subgroup.mem_normalizer_iff.mp hy'N (a : G)⁻¹).mp
              ((OddOrder.BG.Ch3.S10.Msigma M).inv_mem hs)
          have heq : (a : G) * ((b : G) * g * (b : G)⁻¹) * (a : G)⁻¹ *
              ((b : G) * g * (b : G)⁻¹)⁻¹ =
              (a : G) * (((b : G) * g * (b : G)⁻¹) * (a : G)⁻¹ *
                ((b : G) * g * (b : G)⁻¹)⁻¹) := by group
          rw [heq]; exact (OddOrder.BG.Ch3.S10.Msigma M).mul_mem hs h1
        have hcomm1 : (a : G) * ((b : G) * g * (b : G)⁻¹) * (a : G)⁻¹ *
            ((b : G) * g * (b : G)⁻¹)⁻¹ = 1 := by
          have hmem : _ ∈ OddOrder.BG.Ch3.S10.Msigma M ⊓ (MulAut.conj w • E) :=
            Subgroup.mem_inf.mpr ⟨hcommMσ, (MulAut.conj w • E).mul_mem hsy'E
              ((MulAut.conj w • E).inv_mem hy'E)⟩
          rw [h'.E_compl_inf] at hmem; exact Subgroup.mem_bot.mp hmem
        -- `n g n⁻¹ = b g b⁻¹` (the `M_σ`-part `a` centralizes `b g b⁻¹`).
        have hngn_eq : n * g * n⁻¹ = (b : G) * g * (b : G)⁻¹ :=
          hsy'.symm.trans (mul_inv_eq_one.mp hcomm1)
        -- `s' := b⁻¹ · n ∈ M_σ` centralizes `g`, so `s' ∈ C_{M_σ}(K) = K*`.
        have hs'Mσ : (b : G)⁻¹ * n ∈ OddOrder.BG.Ch3.S10.Msigma M := by
          have hbinvN : (b : G)⁻¹ ∈ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma M) :=
            Subgroup.inv_mem _ (le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) M hbM)
          have heq2 : (b : G)⁻¹ * n = (b : G)⁻¹ * (a : G) * ((b : G)⁻¹)⁻¹ := by rw [← hse]; group
          rw [heq2]
          exact (Subgroup.mem_normalizer_iff.mp hbinvN (a : G)).mp hs
        have hs'cent : (b : G)⁻¹ * n ∈ Subgroup.centralizer ({g} : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro z hz; rw [Set.mem_singleton_iff.mp hz]
          -- `g * (b⁻¹n) = (b⁻¹n) * g`, i.e. `b⁻¹ n centralizes g`, from `ngn⁻¹ = bgb⁻¹`.
          have hkey : (b : G)⁻¹ * n * g * ((b : G)⁻¹ * n)⁻¹ = g := by
            have hrw : (b : G)⁻¹ * n * g * ((b : G)⁻¹ * n)⁻¹
                = (b : G)⁻¹ * (n * g * n⁻¹) * (b : G) := by group
            rw [hrw, hngn_eq]; group
          exact (mul_inv_eq_iff_eq_mul.mp hkey).symm
        have hs'Kstar : (b : G)⁻¹ * n ∈ Kstar := by
          rw [hKstar, ← fixedBy_def, ← hKprime g hgK hg1', fixedByElement_def]
          exact Subgroup.mem_inf.mpr ⟨hs'Mσ, hs'cent⟩
        -- `b = n · s'⁻¹ ∈ N_G(X) ⊓ E' ≤ K`.
        have hbN : (b : G) ∈ Subgroup.normalizer (X : Set G) := by
          have hs'N : ((b : G)⁻¹ * n)⁻¹ ∈ Subgroup.normalizer (X : Set G) :=
            (Subgroup.normalizer (X : Set G)).inv_mem
              ((hKstar ▸ inf_le_right.trans
                ((Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hXK)).trans
                  (Subgroup.centralizer_le_normalizer _))) hs'Kstar)
          have hbeq : (b : G) = n * ((b : G)⁻¹ * n)⁻¹ := by group
          rw [hbeq]; exact (Subgroup.normalizer (X : Set G)).mul_mem hnX hs'N
        have hbK : (b : G) ∈ K :=
          normalizer_inf_E_le_E1_of_caseTau1 hG h' hKne hKstar_ne hτ3 hXrank hXK
            (Subgroup.mem_inf.mpr ⟨hbN, he⟩)
        -- `n = b · s' ∈ K ⊔ K*`.
        have hnbs' : n = (b : G) * ((b : G)⁻¹ * n) := by group
        rw [hnbs']
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hbK) (Subgroup.mem_sup_right hs'Kstar)
      · refine sup_le (le_inf (hKcentX.trans (Subgroup.centralizer_le_normalizer _)) hKM) ?_
        rw [hKstar]
        exact le_inf
          (inf_le_right.trans ((Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hXK)).trans
            (Subgroup.centralizer_le_normalizer _)))
          (inf_le_left.trans (OddOrder.BG.Ch3.S10.Msigma_le M))
    · -- (d) `K* ∩ M^g = 1` for `g ∉ M` (mirror of case `τ₃`, using the new setup `h'` whose
      -- `E₁ = K` and the `C(E₁)`-form of (c)).
      intro g hgM
      by_contra hne
      obtain ⟨q, hq, hqdvd⟩ :=
        (Nat.card ↥(Kstar ⊓ (MulAut.conj g • M))).exists_prime_and_dvd
          (fun hc => hne (Subgroup.card_eq_one.mp hc))
      have : Fact q.Prime := ⟨hq⟩
      obtain ⟨w', hw'⟩ := exists_prime_orderOf_dvd_card' q hqdvd
      have hXcard : Nat.card ↥(Subgroup.zpowers (w' : G)) = q := by
        rw [Nat.card_zpowers]
        exact (orderOf_injective _ (Kstar ⊓ (MulAut.conj g • M)).subtype_injective w').trans hw'
      have hXelem : Subgroup.zpowers (w' : G) ∈ elemAbelianOfRank G q 1 :=
        ⟨Subgroup.IsElementaryAbelian.of_card_prime hXcard, by rw [hXcard, pow_one]⟩
      have hXle : Subgroup.zpowers (w' : G) ≤ Kstar ⊓ (MulAut.conj g • M) :=
        Subgroup.zpowers_le.mpr w'.2
      have hXC : Subgroup.zpowers (w' : G) ≤
          OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) :=
        hKstar ▸ (hXle.trans inf_le_left)
      have h𝓜 := maximalContaining_centralizer_of_le_Msigma_centralizer_E1 hG h' hKne hXelem hXC
      have hCM : Subgroup.centralizer ((Subgroup.zpowers (w' : G)) : Set G) ≤ M :=
        (mem_maximalSubgroupsContaining.mp (by rw [h𝓜]; exact Set.mem_singleton M)).2
      have hXMσ : Subgroup.zpowers (w' : G) ≤ OddOrder.BG.Ch3.S10.Msigma M := hXC.trans inf_le_left
      have hXM : Subgroup.zpowers (w' : G) ≤ M := hXMσ.trans (OddOrder.BG.Ch3.S10.Msigma_le M)
      have hqσ : q ∈ OddOrder.BG.Ch3.S10.sigma M :=
        OddOrder.BG.Ch3.S10.Msigma_isPiGroup M q (Nat.mem_primeFactors.mpr
          ⟨hq, hXcard ▸ Subgroup.card_dvd_of_le hXMσ, Nat.card_pos.ne'⟩)
      have hXbot : Subgroup.zpowers (w' : G) ≠ ⊥ := ne_bot_of_mem_elemAbelianOfRank_one hXelem
      have hXp : IsPGroup q ↥(Subgroup.zpowers (w' : G)) := hXelem.1.isPGroup
      have hXgM : Subgroup.zpowers (w' : G) ≤ MulAut.conj g • M := hXle.trans inf_le_right
      have hconj : MulAut.conj g⁻¹ • Subgroup.zpowers (w' : G) ≤ M := by
        have h1 : MulAut.conj g⁻¹ • Subgroup.zpowers (w' : G) ≤
            MulAut.conj g⁻¹ • (MulAut.conj g • M) :=
          (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := MulAut.conj g⁻¹)).mpr hXgM
        rwa [smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul] at h1
      have hg' : g⁻¹ ∈ M :=
        (OddOrder.BG.Ch3.S10.fusion_control_of_mem_sigma hG hM hqσ hXbot hXp).2.2.2.2
          hXM hCM g⁻¹ hconj
      exact hgM (by simpa using M.inv_mem hg')
    · -- (g) type-`P₂` ⟹ `σ = β`, `|K|` prime, `M_σ` nilpotent TI.  `IsTypeP2 M` forces
      -- `U = E₂E₃ ≠ 1` (`E23_ne_bot_of_isTypeP2_caseTau1`); the Frobenius core
      -- (`sigma_eq_beta_and_prime_card_E1_of_caseTau1`) gives `σ = β` and `|K|` prime via
      -- Theorem 3.10(a); the TI clause follows from `σ = β`
      -- (`isTISubset_sigmaSharp_of_sigma_eq_beta`).
      intro hP2
      have hKstar_ne : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) ≠ ⊥ :=
        Msigma_inf_centralizer_E_ne_bot_of_actsPrime_nonregular hKprime (le_refl K) hKnonreg
      have hUne := E23_ne_bot_of_isTypeP2_caseTau1 hG h' hKprime hKstar_ne hτ3 hP2
      obtain ⟨hσβ, q, hq, hqcard⟩ :=
        sigma_eq_beta_and_prime_card_E1_of_caseTau1 hG h' hKne hKstar_ne hτ3 hUne
      exact ⟨hσβ, q, hq, hqcard, isTISubset_sigmaSharp_of_sigma_eq_beta hG hM hσβ⟩
    · -- (c) `ℳ(C_G(X)) = {M}` for `X ∈ ℰ¹(K*)`: `K* = C_{M_σ}(K) = C_{M_σ}(E₁')` (`K = E₁'`),
      -- so the `C(E₁)`-form Corollary 12.14 helper (`…_centralizer_E1`) applies directly.
      intro p hp X hXelem hXKstar
      have : Fact p.Prime := ⟨hp⟩
      exact maximalContaining_centralizer_of_le_Msigma_centralizer_E1 hG h' hKne hXelem
        (hKstar ▸ hXKstar)
    · -- (e-core) `K* ⊊ M_σ` (BG Prop 14.2(e)): apply `kstar_ne_msigma_aux` with `E₁' = K`.
      have hKstar_ne : Kstar ≠ ⊥ := by
        rw [hKstar]
        exact Msigma_inf_centralizer_E_ne_bot_of_actsPrime_nonregular hKprime (le_refl K) hKnonreg
      refine kstar_ne_msigma_aux hG h' (le_refl K) h'.E₁_le hKne hKne (fun q hq => ?_) hKstar
          hKstar_ne
      exact kappa_subset_tau1_union_tau3 (hK.1 q (by
        rwa [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hq))

end OddOrder.BG.Ch4.S14


