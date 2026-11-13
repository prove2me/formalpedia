-- Prove2me | Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_ECore
-- name    : OddOrder_BG_Ch3_MaximalSubgroups_S12_ECore
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T07:16:02.846401+00:00
-- url     : https://prove2.me/theorems/f07e25e2-74fc-4823-89b2-4431db72c96c
-- title:
--   BG §12: the subgroup $E$, definitions and proved core
-- statement:
--   The definition layer and proved core of §12 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*: the prime sets $\tau_1,\tau_2,\tau_3$, the setup structure for the subgroup $E$ (a complement of $M_\sigma$ in $M$), and the proved results Lemma 12.1(a)–(g), Lemma 12.2(a), Lemma 12.17 and a building block of Lemma 12.18.
--
--   Main declarations: `tau1`; `tau2`; `tau3`; `E12` (`E₁E₂` in BG §12, represented as the subgroup join); and 9 more.
--
--   The bundle also proves 43 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch3_MaximalSubgroups/S12_ECore.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch3_MaximalSubgroups/S12_ECore.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_Setup
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S10_HallStructure
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S10_LocalLemmas
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S10_BetaRadical
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S11_ExceptionalMaximal
import Definitions.Def_OddOrder_GroupTheory_MaximalSubgroup
import Definitions.Def_OddOrder_GroupTheory_ElementaryAbelianFamily
import Definitions.Def_OddOrder_GroupTheory_NarrowPGroup
import Definitions.Def_OddOrder_GroupTheory_PRank
import Definitions.Def_OddOrder_Isaacs_Ch03_SplitExtensions_Main
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_FrobeniusGroup

namespace OddOrder.BG.Ch3.S12

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.BG.Ch1.S06 (actionCommutator_conj_map_subtype fixedPointsOfMulAut_conj_map_subtype)

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **BG `τ₁(M)`** (mmd L3029): `{p ∈ σ(M)' | p ∉ π(M') ∧ r_p(M)=1}`。 -/
def tau1 (M : Subgroup G) : Set ℕ :=
  {p | p ∉ S10.sigma M ∧ p ∉ (Nat.card ↥(derivedInG M)).primeFactors ∧ pRank ↥M p = 1}

/-- **BG `τ₂(M)`** (mmd L3029): `{p ∈ σ(M)' | r_p(M)=2}`。 -/
def tau2 (M : Subgroup G) : Set ℕ :=
  {p | p ∉ S10.sigma M ∧ pRank ↥M p = 2}

/-- **BG `τ₃(M)`** (mmd L3029): `{p ∈ σ(M)' | p ∈ π(M') ∧ r_p(M)=1}`。 -/
def tau3 (M : Subgroup G) : Set ℕ :=
  {p | p ∉ S10.sigma M ∧ p ∈ (Nat.card ↥(derivedInG M)).primeFactors ∧ pRank ↥M p = 1}

@[simp] theorem mem_tau1_iff (M : Subgroup G) (p : ℕ) :
    p ∈ tau1 M ↔
      p ∉ S10.sigma M ∧ p ∉ (Nat.card ↥(derivedInG M)).primeFactors ∧ pRank ↥M p = 1 :=
  Iff.rfl

@[simp] theorem mem_tau2_iff (M : Subgroup G) (p : ℕ) :
    p ∈ tau2 M ↔ p ∉ S10.sigma M ∧ pRank ↥M p = 2 :=
  Iff.rfl

@[simp] theorem mem_tau3_iff (M : Subgroup G) (p : ℕ) :
    p ∈ tau3 M ↔
      p ∉ S10.sigma M ∧ p ∈ (Nat.card ↥(derivedInG M)).primeFactors ∧ pRank ↥M p = 1 :=
  Iff.rfl

theorem tau1_subset_sigma_compl (M : Subgroup G) : tau1 M ⊆ (S10.sigma M)ᶜ :=
  fun _ hp => hp.1

theorem tau2_subset_sigma_compl (M : Subgroup G) : tau2 M ⊆ (S10.sigma M)ᶜ :=
  fun _ hp => hp.1

theorem tau3_subset_sigma_compl (M : Subgroup G) : tau3 M ⊆ (S10.sigma M)ᶜ :=
  fun _ hp => hp.1

theorem tau1_not_mem_derived_primeFactors {M : Subgroup G} {p : ℕ} (hp : p ∈ tau1 M) :
    p ∉ (Nat.card ↥(derivedInG M)).primeFactors :=
  hp.2.1

theorem tau3_mem_derived_primeFactors {M : Subgroup G} {p : ℕ} (hp : p ∈ tau3 M) :
    p ∈ (Nat.card ↥(derivedInG M)).primeFactors :=
  hp.2.1

theorem tau1_pRank_eq_one {M : Subgroup G} {p : ℕ} (hp : p ∈ tau1 M) :
    pRank ↥M p = 1 :=
  hp.2.2

theorem tau2_pRank_eq_two {M : Subgroup G} {p : ℕ} (hp : p ∈ tau2 M) :
    pRank ↥M p = 2 :=
  hp.2

theorem tau3_pRank_eq_one {M : Subgroup G} {p : ℕ} (hp : p ∈ tau3 M) :
    pRank ↥M p = 1 :=
  hp.2.2

theorem not_mem_tau3_of_mem_tau1 {M : Subgroup G} {p : ℕ} (hp : p ∈ tau1 M) :
    p ∉ tau3 M :=
  fun hp3 => hp.2.1 hp3.2.1

/-- A prime divisor of `|H|` forces `pRank H p ≥ 1` (Cauchy: an order-`p` element
generates an elementary abelian subgroup of order `p`). -/
theorem one_le_pRank_of_mem_primeFactors {H : Type*} [Group H] [Finite H] {p : ℕ}
    (hp : p ∈ (Nat.card H).primeFactors) : 1 ≤ pRank H p := by
  obtain ⟨hprime, hdvd, -⟩ := Nat.mem_primeFactors.mp hp
  have : Fact p.Prime := ⟨hprime⟩
  obtain ⟨x, hx⟩ := Ch01.cauchy hdvd
  have hcard : Nat.card ↥(Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hx]
  have helem : (Subgroup.zpowers x).IsElementaryAbelian p := by
    constructor
    · rintro ⟨a, ha⟩ ⟨b, hb⟩
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hb
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← hm, ← hn, ← zpow_add, ← zpow_add, add_comm]
    · intro a
      have h1 : orderOf a ∣ p := hcard ▸ orderOf_dvd_natCard a
      exact orderOf_dvd_iff_pow_eq_one.mp h1
  have hle := le_pRank (Subgroup.zpowers x) helem
  rw [hcard] at hle
  have hlog : Nat.log p p = 1 := by
    nth_rewrite 2 [show p = p ^ 1 from (pow_one p).symm]
    exact Nat.log_pow hprime.one_lt 1
  rwa [hlog] at hle

/-- `⁅H, H⁆ ≤ H`: self-commutators stay inside the subgroup. -/
private theorem commutator_self_le {Γ : Type*} [Group Γ] (H : Subgroup Γ) : ⁅H, H⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  rw [commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem hg₁ hg₂) (H.inv_mem hg₁)) (H.inv_mem hg₂)

/-- `E₁E₂` in BG §12, represented as the subgroup join. -/
def E12 (E₁ E₂ : Subgroup G) : Subgroup G :=
  E₁ ⊔ E₂

/-- **BG §12 setup**: `E` は `M_σ` の `M` 内補群 (`M_σ ⊓ E = 1`, `M_σ ⊔ E = M`)、`E₁/E₂/E₃` は
`E` の Hall `τ₁/τ₂/τ₃(M)`-部分群。

原文 (mmd L3029) は **`E₁₂` を `E` の Hall `τ₁(M)∪τ₂(M)`-部分群として固定し、`E₁`,`E₂` を
その内部の Hall** に取る。この入れ子を field `E₁₂_hall` (`E₁ ⊔ E₂` が Hall `τ₁∪τ₂`) で表現する。
`E₁`,`E₂` を `E` の独立な Hall として取るだけでは `E₁ ⊔ E₂` は Hall `τ₁∪τ₂` にならず
(`E₁` だけ共役でずれた取り方が可能)、Lemma 12.1(e) の `E₂ ⊴ E₁E₂` が反例を持つ
(notes/bg/s12_subgroup_e.md 2026-06-10 節)。 -/
structure SubgroupESetup (M E E₁ E₂ E₃ : Subgroup G) : Prop where
  mem_maximal : M ∈ maximalSubgroups G
  E_le : E ≤ M
  E_compl_inf : S10.Msigma M ⊓ E = ⊥
  E_compl_sup : S10.Msigma M ⊔ E = M
  E₁_le : E₁ ≤ E
  E₂_le : E₂ ≤ E
  E₃_le : E₃ ≤ E
  E₁_hall : Ch03.IsHallSubgroup (tau1 M) (E₁.subgroupOf E)
  E₂_hall : Ch03.IsHallSubgroup (tau2 M) (E₂.subgroupOf E)
  E₃_hall : Ch03.IsHallSubgroup (tau3 M) (E₃.subgroupOf E)
  E₁₂_hall : Ch03.IsHallSubgroup (tau1 M ∪ tau2 M) ((E₁ ⊔ E₂).subgroupOf E)

namespace SubgroupESetup

variable {M E E₁ E₂ E₃ : Subgroup G}

theorem E1_le_M (h : SubgroupESetup M E E₁ E₂ E₃) : E₁ ≤ M :=
  h.E₁_le.trans h.E_le

theorem E2_le_M (h : SubgroupESetup M E E₁ E₂ E₃) : E₂ ≤ M :=
  h.E₂_le.trans h.E_le

theorem E3_le_M (h : SubgroupESetup M E E₁ E₂ E₃) : E₃ ≤ M :=
  h.E₃_le.trans h.E_le

theorem E12_le_E (h : SubgroupESetup M E E₁ E₂ E₃) : E12 E₁ E₂ ≤ E :=
  sup_le h.E₁_le h.E₂_le

section Basic

variable [Finite G]

omit [Finite G] in
/-- `M_σ` and `E` are complements inside `↥M` (internal form of `M = M_σ E`,
`M_σ ∩ E = 1`; `M_σ ⊴ M` makes the disjoint join a genuine complement). -/
theorem isComplement'_subgroupOf (h : SubgroupESetup M E E₁ E₂ E₃) :
    ((S10.Msigma M).subgroupOf M).IsComplement' (E.subgroupOf M) := by
  have : ((S10.Msigma M).subgroupOf M).Normal := by
    rw [S10.Msigma_subgroupOf]; infer_instance
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
  · rw [disjoint_iff]
    have hinf : (S10.Msigma M).subgroupOf M ⊓ E.subgroupOf M
        = (S10.Msigma M ⊓ E).subgroupOf M := rfl
    rw [hinf, h.E_compl_inf, Subgroup.bot_subgroupOf]
  · rw [← Subgroup.normal_mul, ← Subgroup.subgroupOf_sup (S10.Msigma_le M) h.E_le,
      h.E_compl_sup, Subgroup.subgroupOf_self, Subgroup.coe_top]

omit [Finite G] in
/-- `|M_σ| · |E| = |M|`. -/
theorem card_Msigma_mul_card_E (h : SubgroupESetup M E E₁ E₂ E₃) :
    Nat.card ↥(S10.Msigma M) * Nat.card ↥E = Nat.card ↥M := by
  have hc := h.isComplement'_subgroupOf.card_mul_card
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (S10.Msigma_le M)).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E_le).toEquiv] at hc

/-- `E` is a `σ(M)'`-group: `|E|` equals the index of the Hall subgroup `M_σ` in `M`. -/
theorem isPiGroup_sigma_compl (hG : IsMinimalSimpleOdd G) (h : SubgroupESetup M E E₁ E₂ E₃) :
    Ch03.Subgroup.IsPiGroup (S10.sigma M)ᶜ E := by
  intro p hp
  have hidx : ((S10.Msigma M).subgroupOf M).index = Nat.card ↥E := by
    rw [h.isComplement'_subgroupOf.symm.index_eq_card,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E_le).toEquiv]
  have hHall := S10.Msigma_subgroupOf_isHall_of_isHall
    (S10.isHall_Msigma_Malpha hG h.mem_maximal).1
  exact hHall.2 p (by rwa [hidx])

/-- No prime divisor of `|E|` lies in `σ(M)`. -/
theorem not_mem_sigma_of_mem_primeFactors (hG : IsMinimalSimpleOdd G)
    (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ}
    (hp : p ∈ (Nat.card ↥E).primeFactors) : p ∉ S10.sigma M :=
  h.isPiGroup_sigma_compl hG p hp

/-- Prime divisors of `|E|` have `r_p(M) ≤ 2` (they avoid `α(M) ⊆ σ(M)`). -/
theorem pRank_M_le_two (hG : IsMinimalSimpleOdd G) (h : SubgroupESetup M E E₁ E₂ E₃)
    {p : ℕ} (hp : p ∈ (Nat.card ↥E).primeFactors) : pRank ↥M p ≤ 2 := by
  have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  by_contra hcon
  have hpM : p ∈ (Nat.card ↥M).primeFactors := by
    rw [Nat.mem_primeFactors] at hp ⊢
    exact ⟨hprime, hp.2.1.trans (Subgroup.card_dvd_of_le h.E_le), Nat.card_pos.ne'⟩
  exact h.not_mem_sigma_of_mem_primeFactors hG hp
    (S10.alpha_subset_sigma hG h.mem_maximal
      ((S10.mem_alpha_iff M p).mpr ⟨hpM, by omega⟩))

/-- `r_p(E) ≤ 2` for every prime `p`. -/
theorem pRank_le_two (hG : IsMinimalSimpleOdd G) (h : SubgroupESetup M E E₁ E₂ E₃)
    {p : ℕ} (hp : p.Prime) : pRank ↥E p ≤ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases hpE : p ∈ (Nat.card ↥E).primeFactors
  · exact le_trans (pRank_le_of_injective (Subgroup.inclusion_injective h.E_le))
      (h.pRank_M_le_two hG hpE)
  · by_contra hcon
    exact hpE (Ch2.S09.mem_primeFactors_card_of_pos_pRank (by omega))

/-- `r(E) ≤ 2` (BG: `π(E) ∩ α(M) = ∅`, mmd L3032). -/
theorem rank_le_two (hG : IsMinimalSimpleOdd G) (h : SubgroupESetup M E E₁ E₂ E₃) :
    rank ↥E ≤ 2 :=
  rank_le_iff.mpr fun _ hp => h.pRank_le_two hG hp

/-- **BG (12.1)** (mmd L3032): the prime divisors of `|E|` are partitioned by
`τ₁(M) ∪ τ₂(M) ∪ τ₃(M)`. -/
theorem mem_tau_union_of_mem_primeFactors (hG : IsMinimalSimpleOdd G)
    (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ}
    (hp : p ∈ (Nat.card ↥E).primeFactors) :
    p ∈ tau1 M ∪ tau2 M ∪ tau3 M := by
  have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have : Fact p.Prime := ⟨hprime⟩
  have hσ : p ∉ S10.sigma M := h.not_mem_sigma_of_mem_primeFactors hG hp
  have h1M : 1 ≤ pRank ↥M p :=
    (one_le_pRank_of_mem_primeFactors hp).trans
      (pRank_le_of_injective (Subgroup.inclusion_injective h.E_le))
  have h2M : pRank ↥M p ≤ 2 := h.pRank_M_le_two hG hp
  by_cases hr2 : pRank ↥M p = 2
  · exact Or.inl (Or.inr ⟨hσ, hr2⟩)
  · have hr1 : pRank ↥M p = 1 := by omega
    by_cases hM' : p ∈ (Nat.card ↥(derivedInG M)).primeFactors
    · exact Or.inr ⟨hσ, hM', hr1⟩
    · exact Or.inl (Or.inl ⟨hσ, hM', hr1⟩)

omit [Finite G] in
/-- **BG (12.1) 直前の `E ∩ M' = E'`、`≤` 方向** (mmd L3032): the complement meets the
derived subgroup of `M` exactly in its own derived subgroup. Proof: pass to
`M/M_σ`; the complement maps isomorphically onto the quotient, whose commutator
subgroup is the image of both `commutator M` and `⁅E, E⁆`. -/
theorem inf_derivedInG_le_derivedInG (h : SubgroupESetup M E E₁ E₂ E₃) :
    E ⊓ derivedInG M ≤ derivedInG E := by
  classical
  intro x hx
  have hxM : x ∈ M := h.E_le hx.1
  set Nσ : Subgroup ↥M := (S10.Msigma M).subgroupOf M with hNσ
  have : Nσ.Normal := by rw [hNσ, S10.Msigma_subgroupOf]; infer_instance
  set π : ↥M →* ↥M ⧸ Nσ := QuotientGroup.mk' Nσ with hπ
  -- the complement surjects onto the quotient
  have hEtop : (E.subgroupOf M).map π = ⊤ := by
    have h1 : Nσ ⊔ E.subgroupOf M = ⊤ := h.isComplement'_subgroupOf.sup_eq_top
    have h2 := congrArg (Subgroup.map π) h1
    have hNbot : Nσ.map π = ⊥ := by
      rw [eq_bot_iff]
      rintro y ⟨n, hn, rfl⟩
      rw [Subgroup.mem_bot, hπ, ← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      exact hn
    rw [Subgroup.map_sup, hNbot, bot_sup_eq] at h2
    rw [h2, ← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective Nσ)
  -- `commutator ↥M` and `⁅E', E'⁆` have the same image in the quotient
  have hcq : Subgroup.map π (commutator ↥M)
      = Subgroup.map π ⁅E.subgroupOf M, E.subgroupOf M⁆ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_commutator, hEtop,
      ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective Nσ)]
  -- lift `x` to `commutator ↥M`
  have hx' : (⟨x, hxM⟩ : ↥M) ∈ commutator ↥M := by
    obtain ⟨c, hc, hcx⟩ := hx.2
    have hxc : (⟨x, hxM⟩ : ↥M) = c := Subtype.ext hcx.symm
    rwa [hxc]
  have hmem : π ⟨x, hxM⟩ ∈ Subgroup.map π ⁅E.subgroupOf M, E.subgroupOf M⁆ := by
    rw [← hcq]
    exact ⟨_, hx', rfl⟩
  obtain ⟨c, hc, hcx⟩ := hmem
  -- the difference lies in `N_σ ⊓ E = ⊥`
  have heq : (⟨x, hxM⟩ : ↥M) = c := by
    have hker : (⟨x, hxM⟩ : ↥M) * c⁻¹ ∈ Nσ := by
      have : π ((⟨x, hxM⟩ : ↥M) * c⁻¹) = 1 := by
        rw [map_mul, map_inv, hcx, mul_inv_cancel]
      rwa [← QuotientGroup.ker_mk' Nσ, MonoidHom.mem_ker]
    have hcE : c ∈ E.subgroupOf M := commutator_self_le (E.subgroupOf M) hc
    have hEmem : (⟨x, hxM⟩ : ↥M) * c⁻¹ ∈ E.subgroupOf M :=
      mul_mem (Subgroup.mem_subgroupOf.mpr hx.1) (inv_mem hcE)
    have hbot : (⟨x, hxM⟩ : ↥M) * c⁻¹ ∈ Nσ ⊓ E.subgroupOf M := ⟨hker, hEmem⟩
    rw [disjoint_iff.mp h.isComplement'_subgroupOf.disjoint, Subgroup.mem_bot] at hbot
    exact mul_inv_eq_one.mp hbot
  -- push back to the ambient group
  have hfinal : x ∈ (⁅E.subgroupOf M, E.subgroupOf M⁆).map M.subtype :=
    ⟨c, hc, by rw [← heq]; rfl⟩
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le h.E_le] at hfinal
  have hd : derivedInG E = ⁅E, E⁆ := Subgroup.map_subtype_commutator E
  rwa [hd]

/-- For `p ∈ τ₃(M)`, the prime `p` divides `|E'|` (mmd L3032: `p ∈ π(E')`):
`M' ≤ M_σ (E ⊓ M')` and `p ∤ |M_σ|`, so `p` survives into `E ⊓ M' ≤ E'`. -/
theorem dvd_card_derived_of_mem_tau3 (hG : IsMinimalSimpleOdd G)
    (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} (hprime : p.Prime) (hp : p ∈ tau3 M) :
    p ∣ Nat.card ↥(derivedInG E) := by
  classical
  -- the derived subgroup factorizes through `M_σ` and `E ⊓ M'`
  have hfact : commutator ↥M ≤
      (S10.Msigma M).subgroupOf M ⊔ ((E ⊓ derivedInG M).subgroupOf M) := by
    intro x hxcomm
    obtain ⟨⟨s, e⟩, hse, -⟩ := h.isComplement'_subgroupOf.existsUnique x
    have hxse : (s : ↥M) * (e : ↥M) = x := hse
    have hsM' : (s : ↥M) ∈ commutator ↥M := by
      have hσle : (S10.Msigma M).subgroupOf M ≤ (derivedInG M).subgroupOf M :=
        Subgroup.subgroupOf_mono M (S10.Msigma_le_derived hG h.mem_maximal)
      have hD : (derivedInG M).subgroupOf M = commutator ↥M := by
        rw [derivedInG, Subgroup.subgroupOf,
          Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective M)]
      exact hD ▸ hσle s.2
    have heE : (e : ↥M) ∈ (E ⊓ derivedInG M).subgroupOf M := by
      refine Subgroup.mem_subgroupOf.mpr ⟨?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.mp e.2
      · -- `e = s⁻¹ x ∈ commutator`, then push along the subtype
        have hecomm : (e : ↥M) ∈ commutator ↥M := by
          have he : (e : ↥M) = (s : ↥M)⁻¹ * x := by
            rw [← hxse]; group
          rw [he]
          exact mul_mem (inv_mem hsM') hxcomm
        exact (⟨_, hecomm, rfl⟩ : ((e : ↥M) : G) ∈ (commutator ↥M).map M.subtype)
    rw [← hxse]
    exact mul_mem (Subgroup.mem_sup_left s.2) (Subgroup.mem_sup_right heE)
  -- count: `p ∣ |M'|`, `p ∤ |M_σ|`, hence `p ∣ |E ⊓ M'|`
  have hpM' : p ∣ Nat.card ↥(commutator ↥M) := by
    have hcardeq : Nat.card ↥(derivedInG M) = Nat.card ↥(commutator ↥M) :=
      (Nat.card_congr (Subgroup.equivMapOfInjective (commutator ↥M) M.subtype
        (Subgroup.subtype_injective M)).toEquiv).symm
    have := Nat.dvd_of_mem_primeFactors hp.2.1
    rwa [hcardeq] at this
  have : ((S10.Msigma M).subgroupOf M).Normal := by
    rw [S10.Msigma_subgroupOf]; infer_instance
  have hsupcard : Nat.card ↥((S10.Msigma M).subgroupOf M ⊔ (E ⊓ derivedInG M).subgroupOf M)
      ∣ Nat.card ↥((S10.Msigma M).subgroupOf M) *
        Nat.card ↥((E ⊓ derivedInG M).subgroupOf M) := by
    have hmul := Subgroup.card_HK_mul_card_inf_eq_card_mul_card
      ((S10.Msigma M).subgroupOf M) ((E ⊓ derivedInG M).subgroupOf M)
    rw [← Subgroup.normal_mul] at hmul
    exact ⟨_, hmul.symm⟩
  have hdvd1 : p ∣ Nat.card ↥((S10.Msigma M).subgroupOf M) *
      Nat.card ↥((E ⊓ derivedInG M).subgroupOf M) :=
    dvd_trans (hpM'.trans (Subgroup.card_dvd_of_le hfact)) hsupcard
  have hpσ : ¬ p ∣ Nat.card ↥((S10.Msigma M).subgroupOf M) := by
    intro hcon
    have hcard : Nat.card ↥((S10.Msigma M).subgroupOf M) = Nat.card ↥(S10.Msigma M) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (S10.Msigma_le M)).toEquiv
    rw [hcard] at hcon
    exact hp.1 (S10.Msigma_isPiGroup M p (Nat.mem_primeFactors.mpr
      ⟨hprime, hcon, Nat.card_pos.ne'⟩))
  have hdvd2 : p ∣ Nat.card ↥((E ⊓ derivedInG M).subgroupOf M) :=
    (hprime.dvd_mul.mp hdvd1).resolve_left hpσ
  have hcard2 : Nat.card ↥((E ⊓ derivedInG M).subgroupOf M)
      = Nat.card ↥(E ⊓ derivedInG M) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans h.E_le)).toEquiv
  rw [hcard2] at hdvd2
  exact hdvd2.trans (Subgroup.card_dvd_of_le (h.inf_derivedInG_le_derivedInG))

omit [Finite G] in
/-- `E₁` is a `τ₁(M)`-group. -/
theorem isPiGroup_tau1 (h : SubgroupESetup M E E₁ E₂ E₃) :
    Ch03.Subgroup.IsPiGroup (tau1 M) E₁ := fun p hp =>
  h.E₁_hall.1 p (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₁_le).toEquiv])

omit [Finite G] in
/-- `E₂` is a `τ₂(M)`-group. -/
theorem isPiGroup_tau2 (h : SubgroupESetup M E E₁ E₂ E₃) :
    Ch03.Subgroup.IsPiGroup (tau2 M) E₂ := fun p hp =>
  h.E₂_hall.1 p (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₂_le).toEquiv])

omit [Finite G] in
/-- `E₃` is a `τ₃(M)`-group. -/
theorem isPiGroup_tau3 (h : SubgroupESetup M E E₁ E₂ E₃) :
    Ch03.Subgroup.IsPiGroup (tau3 M) E₃ := fun p hp =>
  h.E₃_hall.1 p (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₃_le).toEquiv])

end Basic

end SubgroupESetup

/-- An odd finite nilpotent group with `pRank ≤ 1` at every prime is cyclic: each Sylow
subgroup is cyclic (converse of BG Lemma 4.5 at odd primes, trivial Sylow at `2`), so the
group is a nilpotent Z-group. Packages the `E₁`/`E₃` cyclicity argument of Lemma 12.1(d). -/
theorem isCyclic_of_odd_of_isNilpotent_of_forall_pRank_le_one {H : Type*} [Group H] [Finite H]
    [Group.IsNilpotent H] (hodd : Odd (Nat.card H))
    (hrank : ∀ p : ℕ, p.Prime → pRank H p ≤ 1) : IsCyclic H := by
  have : _root_.IsZGroup H := by
    rw [isZGroup_iff]
    intro r hr R
    have : Fact r.Prime := ⟨hr⟩
    rcases eq_or_ne r 2 with rfl | hrne
    · -- `|H|` is odd, so the Sylow `2`-subgroup is trivial.
      have h2 : ¬ 2 ∣ Nat.card H := by
        rw [Nat.odd_iff] at hodd
        omega
      have hR1 : Nat.card ↥(R : Subgroup H) = 1 := by
        obtain ⟨k, hk⟩ := R.isPGroup'.exists_card_eq
        rcases Nat.eq_zero_or_pos k with rfl | hkpos
        · simpa using hk
        · exact absurd ((dvd_pow_self 2 hkpos.ne').trans
            (hk ▸ (R : Subgroup H).card_subgroup_dvd_card)) h2
      have : Subsingleton ↥(R : Subgroup H) := (Nat.card_eq_one_iff_unique.mp hR1).1
      infer_instance
    · exact S10.isCyclic_of_pRank_le_one R.isPGroup' (hr.odd_of_ne_two hrne)
        (le_trans (pRank_le_of_injective (Subgroup.subtype_injective _)) (hrank r hr))
  infer_instance

/-- **BG Lemma 12.1(g)** (mmd L3060, = Lemma 10.4(c) at the `τ₂` interface): for a prime
`p ∈ τ₂(M)` and `A ∈ ℰ_p²(M)` with `A ≤ M`, the subgroup `A` is maximal elementary
abelian in `G` and `p` is not an ideal prime. Direct application of `alpha_criterion`. -/
theorem isMaximalElementaryAbelian_of_mem_tau2 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ} (hprime : p.Prime)
    (hp : p ∈ tau2 M) {A : Subgroup G} (hAM : A ≤ M) (hA : A ∈ elemAbelianOfRank G p 2) :
    IsMaximalElementaryAbelian p A ∧ ¬ S10.idealPrime p G := by
  obtain ⟨hideal, hmax⟩ := (S10.alpha_criterion hG hM).2 p hprime hp.1 hp.2
  exact ⟨hmax A hAM hA, hideal⟩

/-- **BG Lemma 12.1(a)** (mmd L3037): `E'` is nilpotent.

原文は Thm 10.2 の「`M'/M_σ` nilpotent」から導くが、repo は商型を経由せず
Thm 4.20(a) (`derived_le_fitting_of_rank_fitting_le_two`) を `E` に直接適用する:
`E` は `σ(M)'`-群ゆえ `r(E) ≤ 2` (`SubgroupESetup.rank_le_two`)、従って
`E' ≤ F(E)` は冪零部分群。 -/
theorem SubgroupESetup.derived_isNilpotent [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) :
    Group.IsNilpotent ↥(derivedInG E) := by
  by_cases hE : E = ⊥
  · have hbot : derivedInG E = ⊥ := by
      rw [hE]
      exact le_bot_iff.mp (Subgroup.map_subtype_le _)
    rw [hbot]
    infer_instance
  · have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups h.mem_maximal
    have : Group.IsSolvable ↥E :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective h.E_le)
    have : Nontrivial ↥E := (Subgroup.nontrivial_iff_ne_bot _).mpr hE
    have hodd : Odd (Nat.card ↥E) :=
      hG.odd.of_dvd_nat
        ((Subgroup.card_dvd_of_le h.E_le).trans (Subgroup.card_subgroup_dvd_card M))
    have hrankF : rank ↥(Ch01.fitting ↥E) ≤ 2 :=
      le_trans (rank_le_of_injective (Subgroup.subtype_injective (Ch01.fitting ↥E)))
        (h.rank_le_two hG)
    have hderived : commutator ↥E ≤ Ch01.fitting ↥E :=
      Ch1.S05.derived_le_fitting_of_rank_fitting_le_two hodd hrankF
    have : Group.IsNilpotent ↥(commutator ↥E) :=
      Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hderived)
    exact Group.nilpotent_of_mulEquiv
      (Subgroup.equivMapOfInjective (commutator ↥E) E.subtype (Subgroup.subtype_injective E))

/-- The normalizer in `↥E` of a Sylow `p`-subgroup `P` (local shorthand for the
Lemma 12.1 internals). -/
private abbrev sylowNormalizerE {G : Type*} [Group G] (E : Subgroup G) {p : ℕ}
    (P : Sylow p ↥E) : Subgroup ↥E :=
  Subgroup.normalizer ((P : Subgroup ↥E) : Set ↥E)

/-- `P` viewed as a (normal) Sylow subgroup of its own normalizer (local shorthand). -/
private abbrev sylowSelfE {G : Type*} [Group G] (E : Subgroup G) {p : ℕ}
    (P : Sylow p ↥E) : Subgroup ↥(sylowNormalizerE E P) :=
  (P.subtype P.le_normalizer : Subgroup ↥(sylowNormalizerE E P))

/-- **Per-prime core of Lemma 12.1(b)/(f)** (mmd L3041-3055): for `p ∈ τ₃(M)` and a Sylow
`p`-subgroup `P` of `E`, the ambient image of `P` lies in `E'` and meets `C_G(E)` trivially.

BG's Frattini argument is reorganized around Burnside: let `W = N_E(P)` and let `K` be a
complement of `P` in `W` (Schur–Zassenhaus). By the cyclic-`P` dichotomy
(`Sylow.commutator_eq_bot_or_commutator_eq_self`), either `⁅K, P⁆ = ⊥` — then `W = PK`
centralizes `P`, Burnside yields a normal `p`-complement `N ⊇ E'`, contradicting
`p ∣ |E'|` (`dvd_card_derived_of_mem_tau3`) — or `⁅K, P⁆ = P`, which forces `P ≤ E'`,
and Prop 1.6(d) (via the conjugation bridges) gives `C_P(K) = 1`, hence `C_G(E) ⊓ P = ⊥`.

De-privatized (user-approved 2026-06-12, issue 8001) so BG §13 Lemma 13.1(a) can cite it via the
`τ₃` complement of an arbitrary maximal `M*`. -/
theorem sylow_le_derived_of_mem_tau3 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau3 M) (P : Sylow p ↥E) :
    (P : Subgroup ↥E).map E.subtype ≤ derivedInG E ∧
    Subgroup.centralizer (E : Set G) ⊓ (P : Subgroup ↥E).map E.subtype = ⊥ := by
  classical
  have hprime : p.Prime := Fact.out
  have hpodd : Odd p := by
    refine hprime.odd_of_ne_two ?_
    rintro rfl
    have h2 : (2 : ℕ) ∣ Nat.card G :=
      (Nat.dvd_of_mem_primeFactors hp.2.1).trans
        (Subgroup.card_subgroup_dvd_card (derivedInG M))
    have hodd := hG.odd
    rw [Nat.odd_iff] at hodd
    omega
  -- `P` is cyclic (`r_p(M) = 1` on `τ₃`)
  have hPcyc : IsCyclic ↥(P : Subgroup ↥E) := by
    refine S10.isCyclic_of_pRank_le_one P.isPGroup' hpodd ?_
    refine le_trans (pRank_le_of_injective (Subgroup.subtype_injective _)) ?_
    refine le_trans (pRank_le_of_injective (Subgroup.inclusion_injective h.E_le)) ?_
    exact le_of_eq hp.2.2
  -- Sylow `p`-subgroup `Q` of the normalizer `W`, with its complement `K`
  have hQnorm : (P.subtype P.le_normalizer).Normal := P.normal_in_normalizer
  have hQcyc : IsCyclic ↥(P.subtype P.le_normalizer : Subgroup
      ↥(sylowNormalizerE E P)) := by
    rw [P.coe_subtype]
    exact isCyclic_of_surjective _ (Subgroup.subgroupOfEquivOfLe P.le_normalizer).symm.surjective
  obtain ⟨K, hK⟩ :=
    Subgroup.exists_left_complement'_of_coprime (P.subtype P.le_normalizer).card_coprime_index
  rcases Sylow.commutator_eq_bot_or_commutator_eq_self (P.subtype P.le_normalizer) hK
    with hbot | hself
  · -- `⁅K, Q⁆ = ⊥`: Burnside contradiction with `p ∣ |E'|`
    exfalso
    have hKcent : K ≤ Subgroup.centralizer
        ((P.subtype P.le_normalizer :
          Subgroup ↥(sylowNormalizerE E P)) :
          Set ↥(sylowNormalizerE E P)) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    have hQcent : (P.subtype P.le_normalizer :
        Subgroup ↥(sylowNormalizerE E P))
        ≤ Subgroup.centralizer
          ((P.subtype P.le_normalizer :
            Subgroup ↥(sylowNormalizerE E P)) :
            Set ↥(sylowNormalizerE E P)) :=
      Subgroup.le_centralizer _
    have htop : sylowNormalizerE E P
        ≤ Subgroup.centralizer ((P : Subgroup ↥E) : Set ↥E) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hyW : y ∈ sylowNormalizerE E P := P.le_normalizer hy
      have hyQ : (⟨y, hyW⟩ : ↥(sylowNormalizerE E P))
          ∈ sylowSelfE E P :=
        Subgroup.mem_subgroupOf.mpr hy
      have hxcent : (⟨x, hx⟩ : ↥(sylowNormalizerE E P))
          ∈ Subgroup.centralizer (sylowSelfE E P : Set ↥(sylowNormalizerE E P)) := by
        have hmem : (⟨x, hx⟩ : ↥(sylowNormalizerE E P))
            ∈ K ⊔ sylowSelfE E P := by
          rw [hK.sup_eq_top]
          exact Subgroup.mem_top _
        exact sup_le hKcent hQcent hmem
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hxcent ⟨y, hyW⟩ hyQ)
    obtain ⟨N, hNnorm, hNcompl⟩ :=
      OddOrder.Isaacs.Ch05.hasNormalPComplement_of_sylow_normalizer_le_centralizer P htop
    have := hNnorm
    have hcompl := hNcompl P
    -- `E' ≤ N` (the quotient is the abelian Sylow `P`)
    have hE'N : commutator ↥E ≤ N := by
      have hPab : ⁅(P : Subgroup ↥E), (P : Subgroup ↥E)⁆ = ⊥ :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer _)
      have hmap : Subgroup.map (QuotientGroup.mk' N) (commutator ↥E) = ⊥ := by
        rw [commutator_def, Subgroup.map_commutator]
        have hNbot : Subgroup.map (QuotientGroup.mk' N) N = ⊥ := by
          rw [eq_bot_iff]
          rintro y ⟨n, hn, rfl⟩
          rw [Subgroup.mem_bot, ← MonoidHom.mem_ker, QuotientGroup.ker_mk']
          exact hn
        have htop2 : Subgroup.map (QuotientGroup.mk' N) (⊤ : Subgroup ↥E)
            = Subgroup.map (QuotientGroup.mk' N) (P : Subgroup ↥E) := by
          conv_lhs => rw [← hcompl.sup_eq_top]
          rw [Subgroup.map_sup, hNbot, bot_sup_eq]
        rw [htop2, ← Subgroup.map_commutator, hPab, Subgroup.map_bot]
      intro z hz
      have hz1 : QuotientGroup.mk' N z ∈ (⊥ : Subgroup (↥E ⧸ N)) := hmap ▸ ⟨z, hz, rfl⟩
      rw [Subgroup.mem_bot] at hz1
      rwa [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker]
    -- `p` divides both of the coprime orders `|P|`, `|N|`: contradiction
    have hpE' : p ∣ Nat.card ↥(derivedInG E) := h.dvd_card_derived_of_mem_tau3 hG hprime hp
    have hcardeq : Nat.card ↥(derivedInG E) = Nat.card ↥(commutator ↥E) :=
      (Nat.card_congr (Subgroup.equivMapOfInjective (commutator ↥E) E.subtype
        (Subgroup.subtype_injective E)).toEquiv).symm
    have hpN : p ∣ Nat.card ↥N :=
      (hcardeq ▸ hpE').trans (Subgroup.card_dvd_of_le hE'N)
    have hcop : Nat.Coprime (Nat.card ↥(P : Subgroup ↥E)) (Nat.card ↥N) := by
      have hidx := P.card_coprime_index
      rwa [hcompl.index_eq_card] at hidx
    have hpP : p ∣ Nat.card ↥(P : Subgroup ↥E) := by
      have hpdvdE : p ∣ Nat.card ↥E :=
        hpE'.trans (Subgroup.card_dvd_of_le (Subgroup.map_subtype_le _))
      rw [P.card_eq_multiplicity]
      exact dvd_pow_self p (hprime.factorization_pos_of_dvd Nat.card_pos.ne' hpdvdE).ne'
    have hdvd1 : p ∣ Nat.gcd (Nat.card ↥(P : Subgroup ↥E)) (Nat.card ↥N) :=
      Nat.dvd_gcd hpP hpN
    rw [hcop] at hdvd1
    exact hprime.one_lt.ne' (Nat.dvd_one.mp hdvd1)
  · -- `⁅K, Q⁆ = Q`: `P ≤ E'` and `C_P(K) = ⊥`
    -- push the commutator identity to `↥E`
    have hmapQ : (P.subtype P.le_normalizer :
        Subgroup ↥(sylowNormalizerE E P)).map
          (sylowNormalizerE E P).subtype
        = (P : Subgroup ↥E) := by
      rw [P.coe_subtype]
      exact Subgroup.map_subgroupOf_eq_of_le P.le_normalizer
    have hmapped : ⁅K.map (sylowNormalizerE E P).subtype,
        (P : Subgroup ↥E)⁆ = (P : Subgroup ↥E) := by
      have hc := congrArg
        (Subgroup.map (sylowNormalizerE E P).subtype) hself
      rwa [Subgroup.map_commutator, hmapQ] at hc
    constructor
    · -- `P ≤ E'`
      have hd : derivedInG E = ⁅E, E⁆ := Subgroup.map_subtype_commutator E
      calc (P : Subgroup ↥E).map E.subtype
          = (⁅K.map (sylowNormalizerE E P).subtype,
              (P : Subgroup ↥E)⁆).map E.subtype := by rw [hmapped]
        _ = ⁅(K.map (sylowNormalizerE E P).subtype).map E.subtype,
              ((P : Subgroup ↥E)).map E.subtype⁆ :=
            Subgroup.map_commutator _ _ _
        _ ≤ ⁅E, E⁆ :=
            Subgroup.commutator_mono (Subgroup.map_subtype_le _) (Subgroup.map_subtype_le _)
        _ = derivedInG E := hd.symm
    · -- `C_G(E) ⊓ P = ⊥` via Prop 1.6(d)
      have hKnormQ : K ≤ Subgroup.normalizer
          (sylowSelfE E P :
            Set ↥(sylowNormalizerE E P)) := by
        have heq : Subgroup.normalizer
            (sylowSelfE E P :
              Set ↥(sylowNormalizerE E P)) = ⊤ :=
          Subgroup.normalizer_eq_top_iff.mpr hQnorm
        rw [heq]
        exact le_top
      -- `actionCommutator φ = ⊤`
      have hac : Ch04.actionCommutator
          ((Subgroup.normalizerMonoidHom (sylowSelfE E P)).comp
            (Subgroup.inclusion hKnormQ)) = ⊤ := by
        apply Subgroup.map_injective
          (Subgroup.subtype_injective (sylowSelfE E P))
        rw [actionCommutator_conj_map_subtype hKnormQ]
        rw [show Subgroup.map (sylowSelfE E P).subtype ⊤
            = sylowSelfE E P from by
          rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]]
        rw [Subgroup.commutator_comm]
        exact hself
      -- Prop 1.6(d): fixed points form a complement of `⊤`, hence are trivial
      let : CommGroup ↥(sylowSelfE E P) :=
        { (inferInstance : Group ↥(sylowSelfE E P)) with
          mul_comm := fun a b => by
            have hcentral : sylowSelfE E P
                ≤ Subgroup.centralizer (sylowSelfE E P :
                  Set ↥(sylowNormalizerE E P)) :=
              Subgroup.le_centralizer _
            exact Subtype.ext
              (Subgroup.mem_centralizer_iff.mp (hcentral a.2) _ b.2).symm }
      have hcop : Nat.Coprime (Nat.card ↥K)
          (Nat.card ↥(sylowSelfE E P)) := by
        have hidx := (P.subtype P.le_normalizer).card_coprime_index
        rw [hK.index_eq_card] at hidx
        exact hidx.symm
      have h16d := OddOrder.BG.Ch1.S01.fixedPoints_isComplement_actionCommutator_of_abelian
        (φ := (Subgroup.normalizerMonoidHom (sylowSelfE E P)).comp
          (Subgroup.inclusion hKnormQ)) hcop
      rw [hac] at h16d
      have hfpbot : Subgroup.fixedPointsOfMulAut
          ((Subgroup.normalizerMonoidHom (sylowSelfE E P)).comp
            (Subgroup.inclusion hKnormQ)) = ⊥ :=
        Subgroup.isComplement'_top_right.mp h16d
      have hcentbot : Subgroup.centralizer (K :
          Set ↥(sylowNormalizerE E P))
          ⊓ sylowSelfE E P = ⊥ := by
        rw [← fixedPointsOfMulAut_conj_map_subtype hKnormQ, hfpbot, Subgroup.map_bot]
      -- transfer to the ambient group
      rw [eq_bot_iff]
      rintro x ⟨hxc, hxP⟩
      obtain ⟨xE, hxE, rfl⟩ := hxP
      have hxW : xE ∈ sylowNormalizerE E P := P.le_normalizer hxE
      have hxQ : (⟨xE, hxW⟩ : ↥(sylowNormalizerE E P))
          ∈ sylowSelfE E P :=
        Subgroup.mem_subgroupOf.mpr hxE
      have hxcent : (⟨xE, hxW⟩ : ↥(sylowNormalizerE E P))
          ∈ Subgroup.centralizer (K :
            Set ↥(sylowNormalizerE E P)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        have hgcomm : ((k : ↥E) : G) * (xE : G) = (xE : G) * ((k : ↥E) : G) :=
          Subgroup.mem_centralizer_iff.mp hxc _ (k : ↥E).2
        exact Subtype.ext (Subtype.ext hgcomm)
      have hbotmem : (⟨xE, hxW⟩ : ↥(sylowNormalizerE E P))
          ∈ Subgroup.centralizer (K :
            Set ↥(sylowNormalizerE E P))
            ⊓ sylowSelfE E P := ⟨hxcent, hxQ⟩
      rw [hcentbot, Subgroup.mem_bot] at hbotmem
      have hxE1 : xE = 1 := congrArg Subtype.val hbotmem
      rw [Subgroup.mem_bot, hxE1]
      rfl

/-- **BG Lemma 12.1(b), first half** (mmd L3041-3052): `E₃ ≤ E'`. Each Sylow subgroup of
`E` at a `τ₃`-prime lies in `E'` (`sylow_le_derived_of_mem_tau3`), so `[E : E']` is coprime
to `|E₃|` and the `τ₃`-Hall subgroup is absorbed. -/
theorem SubgroupESetup.E3_le_derived [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) :
    E₃ ≤ derivedInG E := by
  classical
  have hcop : Nat.Coprime (Nat.card ↥(E₃.subgroupOf E)) (commutator ↥E).index := by
    rw [Nat.coprime_comm]
    by_contra hncop
    obtain ⟨p, hprime, hp1, hp2⟩ := Nat.Prime.not_coprime_iff_dvd.mp hncop
    have : Fact p.Prime := ⟨hprime⟩
    have hcardE₃ : Nat.card ↥(E₃.subgroupOf E) = Nat.card ↥E₃ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₃_le).toEquiv
    have hpτ₃ : p ∈ tau3 M := h.isPiGroup_tau3 p (Nat.mem_primeFactors.mpr
      ⟨hprime, hcardE₃ ▸ hp2, Nat.card_pos.ne'⟩)
    -- a Sylow `p`-subgroup of `E` lies in `E'`, so `p` cannot divide the index
    obtain ⟨P⟩ : Nonempty (Sylow p ↥E) := inferInstance
    have hPle := (sylow_le_derived_of_mem_tau3 hG h hpτ₃ P).1
    have hPcomm : (P : Subgroup ↥E) ≤ commutator ↥E := by
      have hD : (derivedInG E).subgroupOf E = commutator ↥E := by
        rw [derivedInG, Subgroup.subgroupOf,
          Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective E)]
      rw [← hD]
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr (hPle ⟨x, hx, rfl⟩)
    -- factorization bookkeeping: the full `p`-part sits inside `commutator ↥E`
    have hPdvd : p ^ (Nat.card ↥E).factorization p ∣ Nat.card ↥(commutator ↥E) := by
      have hPP := Subgroup.card_dvd_of_le hPcomm
      rwa [P.card_eq_multiplicity] at hPP
    have hfull : p ^ ((Nat.card ↥E).factorization p + 1) ∣ Nat.card ↥E := by
      calc p ^ ((Nat.card ↥E).factorization p + 1)
          = p ^ (Nat.card ↥E).factorization p * p := by ring
      _ ∣ Nat.card ↥(commutator ↥E) * (commutator ↥E).index :=
          mul_dvd_mul hPdvd hp1
      _ = Nat.card ↥E := Subgroup.card_mul_index (commutator ↥E)
    exact Nat.pow_succ_factorization_not_dvd Nat.card_pos.ne' hprime hfull
  have hle := S10.le_of_coprime_card_index (K := commutator ↥E) (Q := E₃.subgroupOf E) hcop
  intro x hx
  exact ⟨_, hle (Subgroup.mem_subgroupOf.mpr hx : (⟨x, h.E₃_le hx⟩ : ↥E) ∈ _), rfl⟩

/-- **BG Lemma 12.1(b), second half** (mmd L3052): `E₃ ⊴ E`. Since `E'` is nilpotent,
`E₃ = O_{τ₃}(E')`, which `E` normalizes because it normalizes `E'`. -/
theorem SubgroupESetup.E3_normal [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) :
    E ≤ Subgroup.normalizer ((E₃ : Subgroup G) : Set G) := by
  classical
  have hnilp : Group.IsNilpotent ↥(derivedInG E) := h.derived_isNilpotent hG
  have hE₃D : E₃ ≤ derivedInG E := h.E3_le_derived hG
  have hcoreHall : Ch03.IsHallSubgroup (tau3 M) (Ch03.oPiCore (tau3 M) ↥(derivedInG E)) :=
    S10.oPiCore_isHall_of_isNilpotent (tau3 M)
  have hE₃core : E₃ ≤ opiCoreInG (tau3 M) (derivedInG E) := by
    have hsub : E₃.subgroupOf (derivedInG E) ≤ Ch03.oPiCore (tau3 M) ↥(derivedInG E) :=
      S10.isPiGroup_le_of_normal_isHallSubgroup hcoreHall
        (Ch03.Subgroup.IsPiGroup.subgroupOf hE₃D h.isPiGroup_tau3)
    intro x hx
    exact ⟨⟨x, hE₃D hx⟩, hsub (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hcorele : Nat.card ↥(opiCoreInG (tau3 M) (derivedInG E)) ≤ Nat.card ↥E₃ := by
    have hcorepi : Ch03.Subgroup.IsPiGroup (tau3 M)
        ((opiCoreInG (tau3 M) (derivedInG E)).subgroupOf E) := by
      refine Ch03.Subgroup.IsPiGroup.subgroupOf
        ((opiCoreInG_le _ _).trans (Subgroup.map_subtype_le _)) ?_
      intro r hr
      have hcard : Nat.card ↥(opiCoreInG (tau3 M) (derivedInG E))
          = Nat.card ↥(Ch03.oPiCore (tau3 M) ↥(derivedInG E)) :=
        (Nat.card_congr (Subgroup.equivMapOfInjective _ _
          (Subgroup.subtype_injective (derivedInG E))).toEquiv).symm
      exact Ch03.oPiCore.isPiGroup (tau3 M) r (hcard ▸ hr)
    have hdvd := h.E₃_hall.card_dvd_of_isPiGroup hcorepi
    have hcard1 : Nat.card ↥((opiCoreInG (tau3 M) (derivedInG E)).subgroupOf E)
        = Nat.card ↥(opiCoreInG (tau3 M) (derivedInG E)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        ((opiCoreInG_le _ _).trans (Subgroup.map_subtype_le _))).toEquiv
    have hcard2 : Nat.card ↥(E₃.subgroupOf E) = Nat.card ↥E₃ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₃_le).toEquiv
    rw [hcard1, hcard2] at hdvd
    exact Nat.le_of_dvd Nat.card_pos hdvd
  have heq : E₃ = opiCoreInG (tau3 M) (derivedInG E) :=
    Subgroup.eq_of_le_of_card_ge hE₃core hcorele
  rw [heq]
  exact le_normalizer_opiCoreInG_of_le_normalizer (tau3 M) (S10.le_normalizer_derivedInG E)

/-- **BG Lemma 12.1(d), `E₃` half** (mmd L3052): `E₃` is cyclic (it sits inside the
nilpotent `E'` with all `p`-ranks `≤ 1`). -/
theorem SubgroupESetup.E3_isCyclic [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) :
    IsCyclic ↥E₃ := by
  have hnilp : Group.IsNilpotent ↥(derivedInG E) := h.derived_isNilpotent hG
  have : Group.IsNilpotent ↥E₃ :=
    Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe (h.E3_le_derived hG))
  have hodd : Odd (Nat.card ↥E₃) :=
    hG.odd.of_dvd_nat
      ((Subgroup.card_dvd_of_le h.E3_le_M).trans (Subgroup.card_subgroup_dvd_card M))
  refine isCyclic_of_odd_of_isNilpotent_of_forall_pRank_le_one hodd fun p hp => ?_
  have : Fact p.Prime := ⟨hp⟩
  by_cases hpE : p ∈ (Nat.card ↥E₃).primeFactors
  · have hp3 : p ∈ tau3 M := h.isPiGroup_tau3 p hpE
    exact le_trans (pRank_le_of_injective (Subgroup.inclusion_injective h.E3_le_M))
      (le_of_eq hp3.2.2)
  · by_contra hcon
    exact hpE (Ch2.S09.mem_primeFactors_card_of_pos_pRank (by omega))

/-- **BG Lemma 12.1(f)** (mmd L3055): `C_{E₃}(E) = 1`. Any nontrivial element of
`C_G(E) ⊓ E₃` would yield a nontrivial `p`-subgroup (`p ∈ τ₃`) inside some Sylow
`p`-subgroup of `E`, contradicting `C_G(E) ⊓ P = ⊥` from the per-prime core. -/
theorem SubgroupESetup.centralizer_inf_E3_eq_bot [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) :
    Subgroup.centralizer (E : Set G) ⊓ E₃ = ⊥ := by
  classical
  rw [← Subgroup.card_eq_one]
  by_contra hne
  obtain ⟨p, hprime, hdvd⟩ := Nat.exists_prime_and_dvd hne
  have : Fact p.Prime := ⟨hprime⟩
  have hpE₃ : p ∈ (Nat.card ↥E₃).primeFactors := Nat.mem_primeFactors.mpr
    ⟨hprime, hdvd.trans (Subgroup.card_dvd_of_le inf_le_right), Nat.card_pos.ne'⟩
  have hpτ₃ : p ∈ tau3 M := h.isPiGroup_tau3 p hpE₃
  -- a nontrivial Sylow `p`-subgroup `Y` of `Z := C_G(E) ⊓ E₃`
  obtain ⟨Y⟩ : Nonempty (Sylow p ↥(Subgroup.centralizer (E : Set G) ⊓ E₃)) := inferInstance
  have hYne : Nat.card
      ↥(Y : Subgroup ↥(Subgroup.centralizer (E : Set G) ⊓ E₃)) ≠ 1 := by
    rw [Y.card_eq_multiplicity]
    intro hone
    have hpos := hprime.factorization_pos_of_dvd Nat.card_pos.ne' hdvd
    rcases Nat.pow_eq_one.mp hone with h1 | h0
    · exact hprime.one_lt.ne' h1
    · omega
  -- realize `Y` inside a Sylow `p`-subgroup of `E`
  have hYG_le_Z : (Y : Subgroup ↥(Subgroup.centralizer (E : Set G) ⊓ E₃)).map
      (Subgroup.centralizer (E : Set G) ⊓ E₃).subtype ≤ Subgroup.centralizer (E : Set G) ⊓ E₃ :=
    Subgroup.map_subtype_le _
  have hYG_le_E : (Y : Subgroup ↥(Subgroup.centralizer (E : Set G) ⊓ E₃)).map
      (Subgroup.centralizer (E : Set G) ⊓ E₃).subtype ≤ E :=
    hYG_le_Z.trans (inf_le_right.trans h.E₃_le)
  have hYG_pgroup : IsPGroup p ↥((Y : Subgroup ↥(Subgroup.centralizer (E : Set G) ⊓ E₃)).map
      (Subgroup.centralizer (E : Set G) ⊓ E₃).subtype) :=
    Y.isPGroup'.map _
  have hYE_pgroup : IsPGroup p ↥(((Y : Subgroup ↥(Subgroup.centralizer (E : Set G) ⊓ E₃)).map
      (Subgroup.centralizer (E : Set G) ⊓ E₃).subtype).subgroupOf E) :=
    hYG_pgroup.of_injective (Subgroup.subgroupOfEquivOfLe hYG_le_E).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hYG_le_E).injective
  obtain ⟨P, hYP⟩ := hYE_pgroup.exists_le_sylow
  have hPbot := (sylow_le_derived_of_mem_tau3 hG h hpτ₃ P).2
  -- `Y ≤ C_G(E) ⊓ P = ⊥`
  have hYbot : (Y : Subgroup ↥(Subgroup.centralizer (E : Set G) ⊓ E₃)).map
      (Subgroup.centralizer (E : Set G) ⊓ E₃).subtype = ⊥ := by
    rw [eq_bot_iff, ← hPbot]
    intro x hx
    refine ⟨(hYG_le_Z hx).1, ?_⟩
    exact ⟨⟨x, hYG_le_E hx⟩, hYP (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hmap : Nat.card ↥((Y : Subgroup ↥(Subgroup.centralizer (E : Set G) ⊓ E₃)).map
      (Subgroup.centralizer (E : Set G) ⊓ E₃).subtype)
      = Nat.card ↥(Y : Subgroup ↥(Subgroup.centralizer (E : Set G) ⊓ E₃)) :=
    Subgroup.card_map_of_injective
      (Subgroup.subtype_injective (Subgroup.centralizer (E : Set G) ⊓ E₃))
  rw [hYbot, Subgroup.card_bot] at hmap
  exact hYne hmap.symm

/-- **BG Lemma 12.1(d), `E₁` half** (mmd L3040-3041): `E₁` is cyclic.

`E₁' ≤ E₁ ⊓ M' = 1` (`τ₁(M)` avoids `π(M')`), so `E₁` is abelian; each Sylow subgroup is
cyclic by the converse of Lemma 4.5 since `r_p(M) = 1` on `τ₁(M)`. -/
theorem SubgroupESetup.E1_isCyclic [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) :
    IsCyclic ↥E₁ := by
  -- `E₁ ⊓ M' = ⊥`: a common prime divisor would lie in `τ₁(M) ∩ π(M') = ∅`.
  have hinf : E₁ ⊓ derivedInG M = ⊥ := by
    rw [← Subgroup.card_eq_one]
    by_contra hne
    obtain ⟨p, hprime, hdvd⟩ := Nat.exists_prime_and_dvd hne
    have hp1 : p ∈ tau1 M := h.isPiGroup_tau1 p (Nat.mem_primeFactors.mpr
      ⟨hprime, hdvd.trans (Subgroup.card_dvd_of_le inf_le_left), Nat.card_pos.ne'⟩)
    exact hp1.2.1 (Nat.mem_primeFactors.mpr
      ⟨hprime, hdvd.trans (Subgroup.card_dvd_of_le inf_le_right), Nat.card_pos.ne'⟩)
  -- `⁅E₁, E₁⁆ = ⊥`, so `E₁` is abelian.
  have hcomm : ⁅E₁, E₁⁆ = ⊥ := by
    have hle1 : ⁅E₁, E₁⁆ ≤ E₁ := by
      rw [Subgroup.commutator_le]
      intro g₁ hg₁ g₂ hg₂
      rw [commutatorElement_def]
      exact E₁.mul_mem (E₁.mul_mem (E₁.mul_mem hg₁ hg₂) (E₁.inv_mem hg₁)) (E₁.inv_mem hg₂)
    have hle2 : ⁅E₁, E₁⁆ ≤ derivedInG M := by
      have hd : derivedInG M = ⁅(M : Subgroup G), M⁆ := Subgroup.map_subtype_commutator M
      rw [hd]
      exact Subgroup.commutator_mono h.E1_le_M h.E1_le_M
    rw [← le_bot_iff, ← hinf]
    exact le_inf hle1 hle2
  have hab : ∀ a b : ↥E₁, a * b = b * a := by
    intro a b
    have hcentral : E₁ ≤ Subgroup.centralizer (E₁ : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hcentral a.2) (b : G) b.2).symm
  let : CommGroup ↥E₁ := { (inferInstance : Group ↥E₁) with mul_comm := hab }
  have hodd : Odd (Nat.card ↥E₁) :=
    hG.odd.of_dvd_nat
      ((Subgroup.card_dvd_of_le (h.E1_le_M)).trans (Subgroup.card_subgroup_dvd_card M))
  refine isCyclic_of_odd_of_isNilpotent_of_forall_pRank_le_one hodd fun p hp => ?_
  have : Fact p.Prime := ⟨hp⟩
  by_cases hpE : p ∈ (Nat.card ↥E₁).primeFactors
  · have hp1 : p ∈ tau1 M := h.isPiGroup_tau1 p hpE
    exact le_trans (pRank_le_of_injective (Subgroup.inclusion_injective h.E1_le_M))
      (le_of_eq hp1.2.2)
  · by_contra hcon
    exact hpE (Ch2.S09.mem_primeFactors_card_of_pos_pRank (by omega))

/-- A subgroup containing the commutator subgroup is normal. -/
private theorem normal_of_commutator_le {Γ : Type*} [Group Γ] {H : Subgroup Γ}
    (h : commutator Γ ≤ H) : H.Normal := by
  refine ⟨fun x hx g => ?_⟩
  have hcm := Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top x)
  rw [commutatorElement_def] at hcm
  have hc : g * x * g⁻¹ * x⁻¹ ∈ H := h hcm
  have hgx : g * x * g⁻¹ = g * x * g⁻¹ * x⁻¹ * x := by group
  rw [hgx]
  exact H.mul_mem hc hx

/-- `E'` is a `τ₂(M) ∪ τ₃(M)`-group: its primes avoid `τ₁(M)` since they divide `|M'|`. -/
theorem SubgroupESetup.isPiGroup_tau23_derived [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) :
    Ch03.Subgroup.IsPiGroup (tau2 M ∪ tau3 M) (derivedInG E) := by
  intro p hp
  have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpE : p ∈ (Nat.card ↥E).primeFactors := by
    rw [Nat.mem_primeFactors] at hp ⊢
    exact ⟨hprime, hp.2.1.trans (Subgroup.card_dvd_of_le (Subgroup.map_subtype_le _)),
      Nat.card_pos.ne'⟩
  have hpM' : p ∈ (Nat.card ↥(derivedInG M)).primeFactors := by
    have hled : derivedInG E ≤ derivedInG M := by
      have hdE : derivedInG E = ⁅E, E⁆ := Subgroup.map_subtype_commutator E
      have hdM : derivedInG M = ⁅(M : Subgroup G), M⁆ := Subgroup.map_subtype_commutator M
      rw [hdE, hdM]
      exact Subgroup.commutator_mono h.E_le h.E_le
    rw [Nat.mem_primeFactors] at hp ⊢
    exact ⟨hprime, hp.2.1.trans (Subgroup.card_dvd_of_le hled), Nat.card_pos.ne'⟩
  rcases h.mem_tau_union_of_mem_primeFactors hG hpE with h12 | h3
  · rcases h12 with h1 | h2
    · exact absurd hpM' h1.2.1
    · exact Or.inl h2
  · exact Or.inr h3

/-- **BG Lemma 12.1(e), normality clause** (mmd L3052): `E₂E₃ ⊴ E`. The join `E₂ ⊔ E₃` is
a Hall `τ₂ ∪ τ₃`-subgroup of `E` containing the normal `τ₂∪τ₃`-subgroup `E'`, hence
contains the commutator subgroup and is normal. -/
theorem SubgroupESetup.E23_normal [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) :
    E ≤ Subgroup.normalizer ((E₂ ⊔ E₃ : Subgroup G) : Set G) := by
  classical
  have hE₃norm : ((E₃.subgroupOf E)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.E₃_le).mpr (h.E3_normal hG)
  -- `(E₂ ⊔ E₃).subgroupOf E` is a Hall `τ₂ ∪ τ₃`-subgroup of `↥E`
  have hsgsup : (E₂ ⊔ E₃).subgroupOf E = E₂.subgroupOf E ⊔ E₃.subgroupOf E :=
    Subgroup.subgroupOf_sup h.E₂_le h.E₃_le
  have hHall : Ch03.IsHallSubgroup (tau2 M ∪ tau3 M) ((E₂ ⊔ E₃).subgroupOf E) := by
    constructor
    · -- π-part: `|E₂' ⊔ E₃'| ∣ |E₂| ⬝ |E₃|`
      intro p hp
      have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hdvd : Nat.card ↥((E₂ ⊔ E₃).subgroupOf E)
          ∣ Nat.card ↥(E₂.subgroupOf E) * Nat.card ↥(E₃.subgroupOf E) := by
        rw [hsgsup]
        have hmul := Subgroup.card_HK_mul_card_inf_eq_card_mul_card
          (E₂.subgroupOf E) (E₃.subgroupOf E)
        rw [← Subgroup.mul_normal] at hmul
        exact ⟨_, hmul.symm⟩
      have hpd : p ∣ Nat.card ↥(E₂.subgroupOf E) * Nat.card ↥(E₃.subgroupOf E) :=
        (Nat.dvd_of_mem_primeFactors hp).trans hdvd
      rcases hprime.dvd_mul.mp hpd with h2 | h3
      · exact Or.inl (h.E₂_hall.1 p (Nat.mem_primeFactors.mpr ⟨hprime, h2, Nat.card_pos.ne'⟩))
      · exact Or.inr (h.E₃_hall.1 p (Nat.mem_primeFactors.mpr ⟨hprime, h3, Nat.card_pos.ne'⟩))
    · -- index part: the index divides both Hall indices
      intro p hp
      rw [Set.mem_union]
      push Not
      constructor
      · refine h.E₂_hall.2 p ?_
        have hidx : ((E₂ ⊔ E₃).subgroupOf E).index ∣ (E₂.subgroupOf E).index :=
          Subgroup.index_dvd_of_le (hsgsup ▸ le_sup_left)
        rw [Nat.mem_primeFactors] at hp ⊢
        exact ⟨hp.1, hp.2.1.trans hidx, Subgroup.index_ne_zero_of_finite⟩
      · refine h.E₃_hall.2 p ?_
        have hidx : ((E₂ ⊔ E₃).subgroupOf E).index ∣ (E₃.subgroupOf E).index :=
          Subgroup.index_dvd_of_le (hsgsup ▸ le_sup_right)
        rw [Nat.mem_primeFactors] at hp ⊢
        exact ⟨hp.1, hp.2.1.trans hidx, Subgroup.index_ne_zero_of_finite⟩
  -- `commutator ↥E` is a normal `τ₂∪τ₃`-subgroup, hence sits inside the Hall subgroup
  have hcommpi : Ch03.Subgroup.IsPiGroup (tau2 M ∪ tau3 M) (commutator ↥E) := by
    intro p hp
    have hcardeq : Nat.card ↥(commutator ↥E) = Nat.card ↥(derivedInG E) :=
      Nat.card_congr (Subgroup.equivMapOfInjective (commutator ↥E) E.subtype
        (Subgroup.subtype_injective E)).toEquiv
    exact h.isPiGroup_tau23_derived hG p (hcardeq ▸ hp)
  have hcomm_le : commutator ↥E ≤ (E₂ ⊔ E₃).subgroupOf E :=
    Ch03.Subgroup.IsPiGroup.normal_le_hall hcommpi hHall
  have : ((E₂ ⊔ E₃).subgroupOf E).Normal := normal_of_commutator_le hcomm_le
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (sup_le h.E₂_le h.E₃_le)).mp
    inferInstance

/-- **BG Lemma 12.1(e), product clause** (mmd L3052): `E = E₁E₂E₃`. The join contains a
Hall subgroup at every prime of `π(E)`, so its index in `E` is `1`. -/
theorem SubgroupESetup.eq_sup [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) :
    E = E₁ ⊔ E₂ ⊔ E₃ := by
  classical
  refine le_antisymm ?_ (sup_le (sup_le h.E₁_le h.E₂_le) h.E₃_le)
  have hidx1 : ((E₁ ⊔ E₂ ⊔ E₃).subgroupOf E).index = 1 := by
    by_contra hne
    have hne0 : ((E₁ ⊔ E₂ ⊔ E₃).subgroupOf E).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    obtain ⟨p, hprime, hdvd⟩ := Nat.exists_prime_and_dvd hne
    have : Fact p.Prime := ⟨hprime⟩
    have hsg : (E₁ ⊔ E₂ ⊔ E₃).subgroupOf E
        = E₁.subgroupOf E ⊔ E₂.subgroupOf E ⊔ E₃.subgroupOf E := by
      rw [Subgroup.subgroupOf_sup (sup_le h.E₁_le h.E₂_le) h.E₃_le,
        Subgroup.subgroupOf_sup h.E₁_le h.E₂_le]
    have hpE : p ∈ (Nat.card ↥E).primeFactors := by
      rw [Nat.mem_primeFactors]
      refine ⟨hprime, hdvd.trans (Subgroup.index_dvd_card _), Nat.card_pos.ne'⟩
    rcases h.mem_tau_union_of_mem_primeFactors hG hpE with h12 | h3
    · rcases h12 with h1 | h2
      · exact h.E₁_hall.2 p (Nat.mem_primeFactors.mpr ⟨hprime,
          hdvd.trans (Subgroup.index_dvd_of_le (hsg ▸ le_sup_of_le_left le_sup_left)),
          Subgroup.index_ne_zero_of_finite⟩) h1
      · exact h.E₂_hall.2 p (Nat.mem_primeFactors.mpr ⟨hprime,
          hdvd.trans (Subgroup.index_dvd_of_le (hsg ▸ le_sup_of_le_left le_sup_right)),
          Subgroup.index_ne_zero_of_finite⟩) h2
    · exact h.E₃_hall.2 p (Nat.mem_primeFactors.mpr ⟨hprime,
        hdvd.trans (Subgroup.index_dvd_of_le (hsg ▸ le_sup_right)),
        Subgroup.index_ne_zero_of_finite⟩) h3
  have htop : (E₁ ⊔ E₂ ⊔ E₃).subgroupOf E = ⊤ := Subgroup.index_eq_one.mp hidx1
  intro x hx
  have := htop ▸ Subgroup.mem_top (⟨x, hx⟩ : ↥E)
  exact Subgroup.mem_subgroupOf.mp this

/-- **BG Lemma 12.1(e), `E₂ ⊴ E₁₂` clause** (mmd L3052): `E₂` is normal in the Hall
`τ₁∪τ₂`-subgroup `E₁E₂`. Its commutator subgroup is a normal `τ₂`-subgroup (its primes lie
in `(τ₁∪τ₂) ∩ (τ₂∪τ₃) = τ₂`), hence sits inside the Hall `τ₂`-subgroup `E₂`. -/
theorem SubgroupESetup.E2_normal_in_E12 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) :
    (E₁ ⊔ E₂ : Subgroup G) ≤ Subgroup.normalizer ((E₂ : Subgroup G) : Set G) := by
  classical
  set J : Subgroup G := E₁ ⊔ E₂ with hJ
  have hJE : J ≤ E := sup_le h.E₁_le h.E₂_le
  have hE₂J : E₂ ≤ J := le_sup_right
  -- `commutator ↥J` is a `τ₂`-group
  have hcommtau2 : Ch03.Subgroup.IsPiGroup (tau2 M) (commutator ↥J) := by
    intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    -- `p ∈ τ₁ ∪ τ₂` (inside `J`, a Hall `τ₁∪τ₂`-subgroup)
    have hcardJ : Nat.card ↥(commutator ↥J) ∣ Nat.card ↥(J.subgroupOf E) := by
      have h1 : Nat.card ↥(commutator ↥J) ∣ Nat.card ↥J :=
        Subgroup.card_subgroup_dvd_card (commutator ↥J)
      have h2 : Nat.card ↥(J.subgroupOf E) = Nat.card ↥J :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJE).toEquiv
      rwa [h2]
    have hp12 : p ∈ tau1 M ∪ tau2 M := h.E₁₂_hall.1 p (Nat.mem_primeFactors.mpr
      ⟨hprime, (Nat.dvd_of_mem_primeFactors hp).trans hcardJ, Nat.card_pos.ne'⟩)
    -- `p ∈ τ₂ ∪ τ₃` (the commutator maps into `E'`)
    have hled : (commutator ↥J).map J.subtype ≤ derivedInG E := by
      have hdJ : (commutator ↥J).map J.subtype = ⁅J, J⁆ := Subgroup.map_subtype_commutator J
      have hdE : derivedInG E = ⁅E, E⁆ := Subgroup.map_subtype_commutator E
      rw [hdJ, hdE]
      exact Subgroup.commutator_mono hJE hJE
    have hp23 : p ∈ tau2 M ∪ tau3 M := by
      refine h.isPiGroup_tau23_derived hG p (Nat.mem_primeFactors.mpr ⟨hprime, ?_,
        Nat.card_pos.ne'⟩)
      have hcardmap : Nat.card ↥((commutator ↥J).map J.subtype) = Nat.card ↥(commutator ↥J) :=
        Subgroup.card_map_of_injective (Subgroup.subtype_injective J)
      exact ((Nat.dvd_of_mem_primeFactors hp).trans (hcardmap ▸ dvd_rfl)).trans
        (Subgroup.card_dvd_of_le hled)
    rcases hp12 with h1 | h2
    · rcases hp23 with h2' | h3'
      · exact h2'
      · exact absurd h3'.2.1 h1.2.1
    · exact h2
  -- `E₂` is a Hall `τ₂`-subgroup of `J`
  have hHallJ : Ch03.IsHallSubgroup (tau2 M) (E₂.subgroupOf J) := by
    constructor
    · intro p hp
      have hcard : Nat.card ↥(E₂.subgroupOf J) = Nat.card ↥(E₂.subgroupOf E) := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₂J).toEquiv,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₂_le).toEquiv]
      exact h.E₂_hall.1 p (hcard ▸ hp)
    · intro p hp
      refine h.E₂_hall.2 p ?_
      have hidx : (E₂.subgroupOf J).index ∣ (E₂.subgroupOf E).index :=
        ⟨(J.subgroupOf E).index, (Subgroup.relIndex_mul_relIndex E₂ J E hE₂J hJE).symm⟩
      rw [Nat.mem_primeFactors] at hp ⊢
      exact ⟨hp.1, hp.2.1.trans hidx, Subgroup.index_ne_zero_of_finite⟩
  have hcomm_le : commutator ↥J ≤ E₂.subgroupOf J :=
    Ch03.Subgroup.IsPiGroup.normal_le_hall hcommtau2 hHallJ
  have : (E₂.subgroupOf J).Normal := normal_of_commutator_le hcomm_le
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hE₂J).mp inferInstance

/-- The complement `E` is nontrivial: `M_σ ≤ M' ⊊ M` for the solvable nontrivial `M`. -/
theorem SubgroupESetup.E_ne_bot [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) :
    E ≠ ⊥ := by
  intro hbot
  have hMσ : S10.Msigma M = M := by
    have := h.E_compl_sup
    rwa [hbot, sup_bot_eq] at this
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups h.mem_maximal
  have : Nontrivial ↥M := by
    refine (Subgroup.nontrivial_iff_ne_bot M).mpr fun hM => ?_
    exact S10.Msigma_ne_bot hG h.mem_maximal (hMσ.trans hM)
  have hcomm : commutator ↥M = ⊤ := by
    have hled : M ≤ derivedInG M := by
      have hl := S10.Msigma_le_derived hG h.mem_maximal
      rwa [hMσ] at hl
    have hD : (derivedInG M).subgroupOf M = commutator ↥M := by
      rw [derivedInG, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective M)]
    rw [← hD, eq_top_iff]
    intro x _
    exact Subgroup.mem_subgroupOf.mpr (hled x.2)
  exact absurd hcomm (Group.IsSolvable.commutator_lt_top_of_nontrivial ↥M).ne

/-- **BG Lemma 12.1(c)** (mmd L3053): if `E₂ = 1` then `E₁ ≠ 1` (otherwise `E = E₃ ≤ E'`
would make the nontrivial solvable `E` perfect). -/
theorem SubgroupESetup.E1_ne_bot_of_E2_eq_bot [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) (h2 : E₂ = ⊥) :
    E₁ ≠ ⊥ := by
  intro h1
  have hE3 : E = E₃ := by
    have := h.eq_sup hG
    rwa [h1, h2, bot_sup_eq, bot_sup_eq] at this
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups h.mem_maximal
  have : Group.IsSolvable ↥E :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective h.E_le)
  have : Nontrivial ↥E := (Subgroup.nontrivial_iff_ne_bot E).mpr (h.E_ne_bot hG)
  have hled : E ≤ derivedInG E := hE3 ▸ (hE3 ▸ h.E3_le_derived hG)
  have hcomm : commutator ↥E = ⊤ := by
    have hD : (derivedInG E).subgroupOf E = commutator ↥E := by
      rw [derivedInG, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective E)]
    rw [← hD, eq_top_iff]
    intro x _
    exact Subgroup.mem_subgroupOf.mpr (hled x.2)
  exact absurd hcomm (Group.IsSolvable.commutator_lt_top_of_nontrivial ↥E).ne

/-- **BG Lemma 12.1** (mmd L3035): §12 setup のもと、
(a) `E'` nilpotent; (b) `E₃ ⊆ E'` かつ `E₃ ⊴ E`; (c) `E₂=1 → E₁≠1`; (d) `E₁`,`E₃` cyclic;
(e) `E=E₁E₂E₃`, `E₂E₃⊴E`, `E₂⊴E₁₂`; (f) `C_{E₃}(E)=1`;
(g) 素数 `p∈τ₂(M)`, `A∈ℰ_p²(M)` ⇒ `A∈ℰ_p*(G)` かつ `p` は ideal でない (⇒ `p∉β(G)`)。
((g) の `p.Prime` は原典の暗黙仮定 (τ₂ ⊆ π(M)); repo の `tau2` は素数性を含まないため明示。) -/
theorem subgroupE_basic [Finite G] (hG : IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃) :
    Group.IsNilpotent ↥(derivedInG E) ∧
    (E₃ ≤ derivedInG E ∧ E ≤ Subgroup.normalizer ((E₃ : Subgroup G) : Set G)) ∧
    (E₂ = ⊥ → E₁ ≠ ⊥) ∧
    (IsCyclic ↥E₁ ∧ IsCyclic ↥E₃) ∧
    (E = E₁ ⊔ E₂ ⊔ E₃ ∧
      E ≤ Subgroup.normalizer ((E₂ ⊔ E₃ : Subgroup G) : Set G) ∧
      (E₁ ⊔ E₂ : Subgroup G) ≤ Subgroup.normalizer ((E₂ : Subgroup G) : Set G)) ∧
    Subgroup.centralizer (E : Set G) ⊓ E₃ = ⊥ ∧
    (∀ p : ℕ, p.Prime → p ∈ tau2 M → ∀ A : Subgroup G, A ≤ M → A ∈ elemAbelianOfRank G p 2 →
      IsMaximalElementaryAbelian p A ∧ ¬ S10.idealPrime p G) :=
  ⟨h.derived_isNilpotent hG,
   ⟨h.E3_le_derived hG, h.E3_normal hG⟩,
   h.E1_ne_bot_of_E2_eq_bot hG,
   ⟨h.E1_isCyclic hG, h.E3_isCyclic hG⟩,
   ⟨h.eq_sup hG, h.E23_normal hG, h.E2_normal_in_E12 hG⟩,
   h.centralizer_inf_E3_eq_bot hG,
   fun _ hprime hp _ hAM hA =>
     isMaximalElementaryAbelian_of_mem_tau2 hG h.mem_maximal hprime hp hAM hA⟩

/-- **BG Lemma 12.2(a)** (mmd L3062): `X` を `M` の非自明 `p`-部分群、`M* ∈ ℳ(N_G(X))` とすると
`p ∈ σ(M*) ∪ τ₂(M*)`。(原典 (b) の τ₁∪τ₃ 非共役は後続。) -/
theorem prime_mem_sigma_or_tau2 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (_hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime]
    {X : Subgroup G} (_hXM : X ≤ M) (hXne : X ≠ ⊥) (hXp : IsPGroup p ↥X)
    {Mstar : Subgroup G}
    (hMstar : Mstar ∈ maximalSubgroupsContaining (Subgroup.normalizer (X : Set G))) :
    p ∈ S10.sigma Mstar ∨ p ∈ tau2 Mstar := by
  classical
  -- Unpack `M* ∈ ℳ(N_G(X))`: `M*` is maximal and `N_G(X) ≤ M*`, hence `X ≤ M*`.
  obtain ⟨hMstarCoatom, hNX⟩ := mem_maximalSubgroupsContaining.mp hMstar
  have hMstarMax : Mstar ∈ maximalSubgroups G := mem_maximalSubgroups.mpr hMstarCoatom
  have hXMstar : X ≤ Mstar := le_trans Subgroup.le_normalizer hNX
  -- `p ∈ π(M*)` because `1 ≠ X ≤ M*` is a `p`-group.
  have hpdvdMstar : p ∣ Nat.card ↥Mstar := by
    obtain ⟨n, hn⟩ := hXp.exists_card_eq
    have hX1 : Nat.card ↥X ≠ 1 := fun h => hXne (Subgroup.card_eq_one.mp h)
    have hn0 : n ≠ 0 := by rintro rfl; rw [pow_zero] at hn; exact hX1 hn
    exact dvd_trans (hn ▸ dvd_pow_self p hn0) (Subgroup.card_dvd_of_le hXMstar)
  have hpπ : p ∈ (Nat.card ↥Mstar).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Fact.out, hpdvdMstar, Nat.card_pos.ne'⟩
  have hodd : Odd p :=
    hG.odd.of_dvd_nat (dvd_trans hpdvdMstar (Subgroup.card_subgroup_dvd_card Mstar))
  by_cases hpσ : p ∈ S10.sigma Mstar
  · exact Or.inl hpσ
  · -- `p ∉ σ(M*)`: show `p ∈ τ₂(M*)`, i.e. `r_p(M*) = 2`.
    right
    rw [mem_tau2_iff]
    refine ⟨hpσ, ?_⟩
    -- `r_p(M*) ≤ 2` since `p ∉ σ(M*) ⊇ α(M*)`.
    have hpα : p ∉ S10.alpha Mstar := fun h => hpσ (S10.alpha_subset_sigma hG hMstarMax h)
    have hr_le : pRank ↥Mstar p ≤ 2 := by
      by_contra h
      exact hpα ((S10.mem_alpha_iff Mstar p).mpr ⟨hpπ, by omega⟩)
    rcases Nat.lt_or_ge (pRank ↥Mstar p) 2 with hlt | hge
    · -- `r_p(M*) = 1` forces a cyclic Sylow `P` of `M*` with `X` characteristic in `P`,
      -- so `N_G(P) ≤ N_G(X) ≤ M*`, giving `p ∈ σ(M*)` — contrary to assumption.
      exfalso
      have hr1 : pRank ↥Mstar p ≤ 1 := by omega
      have hXMpg : IsPGroup p ↥(X.subgroupOf Mstar) :=
        hXp.of_equiv (Subgroup.subgroupOfEquivOfLe hXMstar).symm
      obtain ⟨PM, hXPM⟩ := hXMpg.exists_le_sylow
      set P : Subgroup G := (PM : Subgroup ↥Mstar).map Mstar.subtype with hPdef
      have hXP : X ≤ P := by
        rw [hPdef, ← Subgroup.map_subgroupOf_eq_of_le hXMstar]
        exact Subgroup.map_mono hXPM
      have hPpg : IsPGroup p ↥P := by
        obtain ⟨k, hk⟩ := PM.isPGroup'.exists_card_eq
        refine IsPGroup.of_card (n := k) ?_
        rw [hPdef, ← Nat.card_congr (Subgroup.equivMapOfInjective (PM : Subgroup ↥Mstar)
          Mstar.subtype Mstar.subtype_injective).toEquiv]
        exact hk
      have hPrank : pRank ↥P p = pRank ↥Mstar p := by
        have e : ↥(PM : Subgroup ↥Mstar) ≃* ↥P := by
          rw [hPdef]
          exact Subgroup.equivMapOfInjective (PM : Subgroup ↥Mstar) Mstar.subtype
            Mstar.subtype_injective
        have h1 : pRank ↥P p ≤ pRank ↥(PM : Subgroup ↥Mstar) p :=
          pRank_le_of_injective (f := e.symm.toMonoidHom) e.symm.injective
        have h2 : pRank ↥(PM : Subgroup ↥Mstar) p ≤ pRank ↥P p :=
          pRank_le_of_injective (f := e.toMonoidHom) e.injective
        have h3 : pRank ↥(PM : Subgroup ↥Mstar) p = pRank ↥Mstar p := pRank_sylow_eq PM
        omega
      have hPr1 : pRank ↥P p ≤ 1 := by rw [hPrank]; exact hr1
      have : IsCyclic ↥P := S10.isCyclic_of_pRank_le_one hPpg hodd hPr1
      have : (X.subgroupOf P).Characteristic :=
        Ch04.characteristic_of_subgroup_of_isCyclic (X.subgroupOf P)
      have hNPX : Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (X : Set G) := by
        have h := OddOrder.BG.AppB.normalizer_le_normalizer_map_of_characteristic
          (K := P) (W := X.subgroupOf P)
        rwa [Subgroup.map_subgroupOf_eq_of_le hXP] at h
      exact hpσ ((S10.mem_sigma_iff Mstar p).mpr ⟨hpπ, PM, le_trans hNPX hNX⟩)
    · omega

end OddOrder.BG.Ch3.S12


