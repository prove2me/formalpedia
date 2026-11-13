-- Prove2me | Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S13_PrimeAction
-- name    : OddOrder_BG_Ch3_MaximalSubgroups_S13_PrimeAction
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T08:52:41.093476+00:00
-- url     : https://prove2.me/theorems/85b3f03f-ffde-4d3f-b1bd-64609fe50144
-- title:
--   BG §13: prime action
-- statement:
--   Formalizes Chapter III §13 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem* on how the complement $E$ of $M_\sigma$ in $M$ acts on $M_\sigma$: Lemmas 13.1, 13.6, 13.7, 13.8, Corollaries 13.2, 13.3, 13.11 and Theorems 13.4, 13.5, 13.9, 13.10 (as split across files), with the central concepts of acting in a prime manner and acting regularly.
--
--   Main declarations: `fixedBy` ($C_N(X)$, the elements of $N$ centralizing $X$); `fixedByElement` ($C_N(g)$); `ActsPrimeOn` ('$X$ acts in a prime manner on $N$': the conjugation action satisfies $C_N(g)=C_N(X)$ for all $g\in X^\#$); `ActsRegularlyOn` ('$X$ acts regularly on $N$': $C_N(g)=1$ for all $g\in X^\#$); and 1 more.
--
--   The bundle also proves 28 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch3_MaximalSubgroups/S13_PrimeAction.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch3_MaximalSubgroups/S13_PrimeAction.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_E
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_Corollary1214
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S13_Lemma131
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S13_Corollary132
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S13_Theorem134

namespace OddOrder.BG.Ch3.S13

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.BG.Ch3.S12

open scoped Pointwise

variable {G : Type*} [Group G]

/-- `C_N(X)` in BG §13: elements of `N` centralizing the subgroup `X`. -/
def fixedBy (N X : Subgroup G) : Subgroup G :=
  N ⊓ Subgroup.centralizer (X : Set G)

/-- `C_N(g)` in BG §13: elements of `N` centralizing the element `g`. -/
def fixedByElement (N : Subgroup G) (g : G) : Subgroup G :=
  N ⊓ Subgroup.centralizer ({g} : Set G)

/-- **BG "X acts in a prime manner on N"** (mmd L3486): `X` の `N` への共役作用が
`C_N(g) = C_N(X)` を満たす (全 `g ∈ X#`)。ここで `C_N(·) = N ⊓ C_G(·)`。
同値な形 `C_N(P) ⊆ C_N(X)` (∀P∈ℰ¹(X)) も原典にある。 -/
def ActsPrimeOn (N X : Subgroup G) : Prop :=
  ∀ g ∈ X, g ≠ 1 →
    fixedByElement N g = fixedBy N X

/-- **BG "X acts regularly on N"** (mmd L3494): `C_N(g) = 1` を満たす (全 `g ∈ X#`)。 -/
def ActsRegularlyOn (N X : Subgroup G) : Prop :=
  ∀ g ∈ X, g ≠ 1 → fixedByElement N g = ⊥

@[simp] theorem fixedBy_def (N X : Subgroup G) :
    fixedBy N X = N ⊓ Subgroup.centralizer (X : Set G) :=
  rfl

@[simp] theorem fixedByElement_def (N : Subgroup G) (g : G) :
    fixedByElement N g = N ⊓ Subgroup.centralizer ({g} : Set G) :=
  rfl

@[simp] theorem actsPrimeOn_iff (N X : Subgroup G) :
    ActsPrimeOn N X ↔ ∀ g ∈ X, g ≠ 1 → fixedByElement N g = fixedBy N X :=
  Iff.rfl

@[simp] theorem actsRegularlyOn_iff (N X : Subgroup G) :
    ActsRegularlyOn N X ↔ ∀ g ∈ X, g ≠ 1 → fixedByElement N g = ⊥ :=
  Iff.rfl

theorem fixedBy_le_fixedByElement {N X : Subgroup G} {g : G} (hg : g ∈ X) :
    fixedBy N X ≤ fixedByElement N g := by
  refine inf_le_inf_left N ?_
  refine Subgroup.centralizer_le ?_
  intro x hx
  rcases Set.mem_singleton_iff.mp hx with rfl
  exact hg

/-- For a prime action of `E₁` on `N`, a nonidentity subgroup `P ≤ E₁` has the same fixed subgroup
`C_N(P) = C_N(E₁)` (`fixedBy N P = fixedBy N E₁`). Used in Lemma 13.6 to upgrade `X ≤ C_N(P)` to
`X ≤ C_N(E₁)`. -/
theorem fixedBy_eq_of_le_of_ne_bot {N E₁ : Subgroup G} (hprime : ActsPrimeOn N E₁)
    {P : Subgroup G} (hPE1 : P ≤ E₁) (hPne : P ≠ ⊥) :
    fixedBy N P = fixedBy N E₁ := by
  obtain ⟨g, hgP, hg1⟩ : ∃ g ∈ P, g ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hPne (by rw [eq_bot_iff]; intro x hx; rw [Subgroup.mem_bot]; exact hcon x hx)
  refine le_antisymm ?_
    (inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hPE1)))
  calc fixedBy N P ≤ fixedByElement N g := fixedBy_le_fixedByElement hgP
    _ = fixedBy N E₁ := hprime g (hPE1 hgP) hg1

theorem actsRegularlyOn_bot_left (X : Subgroup G) : ActsRegularlyOn (⊥ : Subgroup G) X := by
  simp [ActsRegularlyOn, fixedByElement]

/-- **Core of BG Corollary 13.3(a)**: an abelian `p`-subgroup `P ≤ M` with `p ∈ τ₁(M) ∪ τ₃(M)`
acts in a prime manner on `M_σ`. For `g ∈ P#`, pick `M* ∈ ℳ(N_G(⟨g⟩))`; then `P ≤ M ⊓ M*`
(`P` abelian centralizes `g`), so Corollary 13.2(a) makes `P` centralize `M_σ ⊓ M*`, while
`C_{M_σ}(g) ≤ M_σ ⊓ M*` (since `C(g) ⊆ M*`); hence `C_{M_σ}(g) = C_{M_σ}(P)`. -/
theorem actsPrimeOn_Msigma_of_mem_tau13 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau1 M ∪ tau3 M) {P : Subgroup G} (hPM : P ≤ M) (hPab : IsMulCommutative ↥P)
    (hPp : IsPGroup p ↥P) : ActsPrimeOn (S10.Msigma M) P := by
  classical
  intro g hgP hg1
  have hMcoatom : IsCoatom M := mem_maximalSubgroups.mp h.mem_maximal
  -- `Z := ⟨g⟩`, a nontrivial `p`-subgroup of `M`.
  have hZle : Subgroup.zpowers g ≤ P := by rw [Subgroup.zpowers_le]; exact hgP
  have hZM : Subgroup.zpowers g ≤ M := hZle.trans hPM
  have hZne : Subgroup.zpowers g ≠ ⊥ := fun hb => hg1 (Subgroup.zpowers_eq_bot.mp hb)
  have hZp : IsPGroup p ↥(Subgroup.zpowers g) := hPp.to_le hZle
  -- `N_G(Z) ≠ ⊤`, so some coatom `M*` lies above it.
  have hNZne : Subgroup.normalizer (Subgroup.zpowers g : Set G) ≠ ⊤ := by
    intro htop
    have : (Subgroup.zpowers g).Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases hG.simple.eq_bot_or_eq_top_of_normal (Subgroup.zpowers g) inferInstance with hb | ht
    · exact hZne hb
    · exact hMcoatom.1 (top_le_iff.mp (ht ▸ hZM))
  obtain ⟨Mstar, hMstarCo, hNZM⟩ :=
    (eq_top_or_exists_le_coatom (Subgroup.normalizer (Subgroup.zpowers g : Set G))).resolve_left
      hNZne
  have hMstarMem : Mstar ∈
      maximalSubgroupsContaining (Subgroup.normalizer (Subgroup.zpowers g : Set G)) :=
    mem_maximalSubgroupsContaining.mpr ⟨hMstarCo, hNZM⟩
  -- `C({g}) ≤ C(Z) ≤ N(Z) ≤ M*` (centralizing `g` ⟹ centralizing `⟨g⟩`).
  have hCg_CZ : Subgroup.centralizer ({g} : Set G)
      ≤ Subgroup.centralizer (Subgroup.zpowers g : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hcomm : Commute x g := (hx g rfl).symm
    exact ((hcomm.zpow_right k).eq).symm
  have hCg_Mstar : Subgroup.centralizer ({g} : Set G) ≤ Mstar :=
    hCg_CZ.trans ((Subgroup.centralizer_le_normalizer _).trans hNZM)
  -- `P ≤ M ⊓ M*` (P abelian ∋ g, so `P ≤ C(P) ≤ C(Z) ≤ N(Z) ≤ M*`).
  have hPCZ : P ≤ Subgroup.centralizer (Subgroup.zpowers g : Set G) :=
    (Subgroup.le_centralizer_iff_isMulCommutative.mpr hPab).trans
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hZle))
  have hPMstar : P ≤ Mstar :=
    hPCZ.trans ((Subgroup.centralizer_le_normalizer _).trans hNZM)
  -- Corollary 13.2(a): `P` centralizes `M_σ ⊓ M*`.
  have hPcent : P ≤ Subgroup.centralizer ((S10.Msigma M ⊓ Mstar : Subgroup G) : Set G) :=
    (tau13_pSubgroup_centralizes hG h hp hZM hZne hZp hMstarMem).1 P (le_inf hPM hPMstar) hPp
  have hMMcP : (S10.Msigma M ⊓ Mstar : Subgroup G) ≤ Subgroup.centralizer (P : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hPcent
  -- conclude: `M_σ ⊓ C(g) ≤ M_σ ⊓ M* ≤ C(P)`, so `C_{M_σ}(g) = C_{M_σ}(P)`.
  refine le_antisymm ?_ (fixedBy_le_fixedByElement hgP)
  rw [fixedByElement_def, fixedBy_def]
  exact le_inf inf_le_left ((inf_le_inf_left _ hCg_Mstar).trans hMMcP)

/-- A nontrivial cyclic Sylow `p`-subgroup `P` of `E` has `p ∈ τ₁(M) ∪ τ₃(M)`: as `P` is a Sylow
`p` of `E` and `p ∤ |M_σ|` (since `p ∈ π(E) ⊆ σ(M)'`), `P` is a Sylow `p` of `M`, so
`r_p(M) = r_p(P) ≤ 1`; with `p ∉ σ(M)` this places `p` in `τ₁ ∪ τ₃` (which is
`{p ∉ σ(M), r_p(M)=1}`).
Excludes `τ₂` (which needs `r_p(M)=2`) and supplies the `τ₁ ∪ τ₃` hypothesis of the core lemma. -/
theorem mem_tau1_union_tau3_of_isCyclic_sylow_E [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    {P : Subgroup G} (hPE : P ≤ E) (hPp : IsPGroup p ↥P) (hPcyc : IsCyclic ↥P) (hPne : P ≠ ⊥)
    (hPmax : ∀ T : Subgroup G, T ≤ E → IsPGroup p ↥T → P ≤ T → P = T) :
    p ∈ tau1 M ∪ tau3 M := by
  classical
  -- `p ∈ π(P) ⊆ π(E) ⊆ π(M)`.
  have hpdvdP : p ∣ Nat.card ↥P := by
    obtain ⟨k, hk⟩ := hPp.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl; rw [pow_zero] at hk; exact hPne (Subgroup.card_eq_one.mp hk)
    exact hk ▸ dvd_pow_self p hk0
  have hpdvdE : p ∣ Nat.card ↥E := hpdvdP.trans (Subgroup.card_dvd_of_le hPE)
  have hpπE : p ∈ (Nat.card ↥E).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Fact.out, hpdvdE, Nat.card_pos.ne'⟩
  have hpσ : p ∉ S10.sigma M := h.not_mem_sigma_of_mem_primeFactors hG hpπE
  have hpπM : p ∈ (Nat.card ↥M).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Fact.out, hpdvdE.trans (Subgroup.card_dvd_of_le h.E_le),
      Nat.card_pos.ne'⟩
  -- `P.subgroupOf E` is a Sylow `p` of `↥E`, so `|P| = p ^ (|E|).factorization p`.
  have hPEpg : IsPGroup p ↥(P.subgroupOf E) := by
    obtain ⟨k, hk⟩ := hPp.exists_card_eq
    exact IsPGroup.of_card
      (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPE).toEquiv]; exact hk)
  obtain ⟨SylE, hSylE⟩ := hPEpg.exists_le_sylow
  have hPeqSyl : P = (SylE : Subgroup ↥E).map E.subtype := by
    refine hPmax _ (Subgroup.map_subtype_le _) (SylE.isPGroup'.map E.subtype) ?_
    rw [← Subgroup.map_subgroupOf_eq_of_le hPE]; exact Subgroup.map_mono hSylE
  have hPcardEq : Nat.card ↥P = p ^ (Nat.card ↥E).factorization p := by
    rw [hPeqSyl, Subgroup.card_map_of_injective E.subtype_injective]
    exact SylE.card_eq_multiplicity
  -- `|M|.factorization p = |E|.factorization p` (since `p ∤ |M_σ|`).
  have hpMσ : ¬ p ∣ Nat.card ↥(S10.Msigma M) := fun hd =>
    hpσ (S10.Msigma_isPiGroup M p (Nat.mem_primeFactors.mpr ⟨Fact.out, hd, Nat.card_pos.ne'⟩))
  have hfactEq : (Nat.card ↥M).factorization p = (Nat.card ↥E).factorization p := by
    rw [← h.card_Msigma_mul_card_E,
      Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hpMσ, zero_add]
  -- `P.subgroupOf M` is a Sylow `p` of `↥M`; hence `r_p(M) = r_p(P) ≤ 1`.
  have hPMcardEq : Nat.card ↥(P.subgroupOf M) = p ^ (Nat.card ↥M).factorization p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hPE.trans h.E_le)).toEquiv, hPcardEq, hfactEq]
  let SylM : Sylow p ↥M := Sylow.ofCard (P.subgroupOf M) hPMcardEq
  have hcyc : IsCyclic ↥(P.subgroupOf M) :=
    isCyclic_of_surjective _ (Subgroup.subgroupOfEquivOfLe (hPE.trans h.E_le)).symm.surjective
  have hpr : pRank ↥(P.subgroupOf M) p ≤ 1 := by
    by_contra hc
    obtain ⟨A, _, hAnc⟩ :=
      exists_isElementaryAbelian_not_isCyclic_of_two_le_pRank
        (G := ↥(P.subgroupOf M)) (p := p) (by omega)
    exact hAnc inferInstance
  have hpRankM : pRank ↥M p ≤ 1 :=
    (pRank_sylow_eq SylM).symm.trans_le hpr
  have hpRank1 : pRank ↥M p = 1 :=
    le_antisymm hpRankM (one_le_pRank_of_mem_primeFactors hpπM)
  -- assemble `τ₁ ∪ τ₃`.
  by_cases hM' : p ∈ (Nat.card ↥(derivedInG M)).primeFactors
  · exact Or.inr ((mem_tau3_iff M p).mpr ⟨hpσ, hM', hpRank1⟩)
  · exact Or.inl ((mem_tau1_iff M p).mpr ⟨hpσ, hM', hpRank1⟩)

/-- **BG Corollary 13.3** (mmd L3526): (a) `E` の非自明 cyclic Sylow 部分群は `M_σ` に prime 作用;
(b) `E₃` は `M_σ` に prime 作用。 -/
theorem cyclicSylow_actsPrime [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) :
    (∀ p : ℕ, p.Prime → ∀ P : Subgroup G, P ≤ E → IsPGroup p ↥P → IsCyclic ↥P → P ≠ ⊥ →
      (∀ T : Subgroup G, T ≤ E → IsPGroup p ↥T → P ≤ T → P = T) →
      ActsPrimeOn (S10.Msigma M) P) ∧
    ActsPrimeOn (S10.Msigma M) E₃ := by
  refine ⟨fun p hp_prime P hPE hPp hPcyc hPne hPmax => ?_, ?_⟩
  · -- (a): cyclic Sylow `P` has `p ∈ τ₁ ∪ τ₃`, then the core lemma applies (`P` abelian).
    have : Fact p.Prime := ⟨hp_prime⟩
    have := hPcyc
    let : CommGroup ↥P := IsCyclic.commGroup
    have : IsMulCommutative ↥P := ⟨⟨mul_comm⟩⟩
    exact actsPrimeOn_Msigma_of_mem_tau13 hG h
      (mem_tau1_union_tau3_of_isCyclic_sylow_E hG h hPE hPp hPcyc hPne hPmax)
      (hPE.trans h.E_le) inferInstance hPp
  · -- (b) `E₃` acts in a prime manner on `M_σ`.
    have hE3cyc : IsCyclic ↥E₃ := h.E3_isCyclic hG
    intro g hgE3 hg1
    refine le_antisymm ?_ (fixedBy_le_fixedByElement hgE3)
    -- pick a prime `p ∣ ord(g)` and the order-`p` element `x := g ^ (ord g / p) ∈ ⟨g⟩ ⊆ E₃`.
    have hord1 : orderOf g ≠ 1 := fun hh => hg1 (orderOf_eq_one_iff.mp hh)
    obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd hord1
    have : Fact p.Prime := ⟨hp_prime⟩
    set x : G := g ^ (orderOf g / p) with hx_def
    have hxE3 : x ∈ E₃ := pow_mem hgE3 _
    have hxp1 : x ^ p = 1 := by
      rw [hx_def, ← pow_mul, Nat.div_mul_cancel hp_dvd, pow_orderOf_eq_one]
    have hx1 : x ≠ 1 := by
      intro hh
      have hdvd := orderOf_dvd_of_pow_eq_one hh
      have hpos : 0 < orderOf g / p :=
        Nat.div_pos (Nat.le_of_dvd (orderOf_pos g) hp_dvd) hp_prime.pos
      have hlt : orderOf g / p < orderOf g :=
        Nat.div_lt_self (orderOf_pos g) hp_prime.one_lt
      exact absurd (Nat.le_of_dvd hpos hdvd) (by omega)
    have hx_ord : orderOf x = p := by
      rcases (Nat.dvd_prime hp_prime).mp (orderOf_dvd_of_pow_eq_one hxp1) with hh | hh
      · exact absurd (orderOf_eq_one_iff.mp hh) hx1
      · exact hh
    -- `⟨x⟩` is characteristic in cyclic `E₃`, hence `E`-normal.
    have hZle : Subgroup.zpowers x ≤ E₃ := Subgroup.zpowers_le.mpr hxE3
    have : ((Subgroup.zpowers x).subgroupOf E₃).Characteristic :=
      Ch04.characteristic_of_subgroup_of_isCyclic _
    have hENx : E ≤ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
      intro e he
      have hmem := OddOrder.BG.Ch1.S03f.mem_normalizer_map_subtype_of_characteristic (W := E₃)
        (C := (Subgroup.zpowers x).subgroupOf E₃) (h.E3_normal hG he)
      rwa [Subgroup.map_subgroupOf_eq_of_le hZle] at hmem
    -- `M* ∈ ℳ(N_G(⟨x⟩))`, so `E ⊆ M*` and `E₃ ⊆ E' ⊆ M*'`.
    have hxne : Subgroup.zpowers x ≠ ⊥ := by rw [Ne, Subgroup.zpowers_eq_bot]; exact hx1
    have hxM : Subgroup.zpowers x ≤ M := hZle.trans h.E3_le_M
    have hNxne : Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) ≠ ⊤ := by
      intro htop
      have : (Subgroup.zpowers x).Normal := Subgroup.normalizer_eq_top_iff.mp htop
      rcases hG.simple.eq_bot_or_eq_top_of_normal (Subgroup.zpowers x) inferInstance with hb | ht
      · exact hxne hb
      · exact (mem_maximalSubgroups.mp h.mem_maximal).1 (top_le_iff.mp (ht ▸ hxM))
    obtain ⟨Mstar, hMstarCo, hNxM⟩ :=
      (eq_top_or_exists_le_coatom
        (Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G))).resolve_left hNxne
    have hMstarMem : Mstar ∈ maximalSubgroupsContaining
        (Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G)) :=
      mem_maximalSubgroupsContaining.mpr ⟨hMstarCo, hNxM⟩
    have hEMstar : E ≤ Mstar := hENx.trans hNxM
    -- `p ∈ τ₃(M)`; `IsPiSubgroup (τ₁ M*)ᶜ E₃`.
    have hpπE3 : p ∈ (Nat.card ↥E₃).primeFactors := by
      refine Nat.mem_primeFactors.mpr ⟨hp_prime, ?_, Nat.card_pos.ne'⟩
      have hzc : Nat.card ↥(Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hx_ord]
      rw [← hzc]; exact Subgroup.card_dvd_of_le hZle
    have hpτ3 : p ∈ tau3 M := h.isPiGroup_tau3 p hpπE3
    have hE3M'star : E₃ ≤ derivedInG Mstar :=
      (h.E3_le_derived hG).trans (derivedInG_le_derivedInG hEMstar)
    have hE3pi : Subgroup.IsPiSubgroup ((tau1 Mstar)ᶜ) E₃ := by
      intro q hq
      rw [Set.mem_compl_iff, mem_tau1_iff]
      rintro ⟨_, hqM', _⟩
      exact hqM' (Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hq).1,
        (Nat.mem_primeFactors.mp hq).2.1.trans (Subgroup.card_dvd_of_le hE3M'star),
        Nat.card_pos.ne'⟩)
    -- Corollary 13.2(b): `E₃` centralizes `M_σ ⊓ M*`.
    have hxp : IsPGroup p ↥(Subgroup.zpowers x) :=
      IsPGroup.of_card (by rw [Nat.card_zpowers, hx_ord, pow_one])
    have hE3cent : E₃ ≤ Subgroup.centralizer ((S10.Msigma M ⊓ Mstar : Subgroup G) : Set G) :=
      (tau13_pSubgroup_centralizes hG h (Or.inr hpτ3) hxM hxne hxp hMstarMem).2.1 E₃
        (le_inf h.E₃_le (h.E₃_le.trans hEMstar)) hE3pi
    have hMMcE3 : (S10.Msigma M ⊓ Mstar : Subgroup G) ≤ Subgroup.centralizer (E₃ : Set G) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hE3cent
    -- `C({x}) ⊆ N(⟨x⟩) ⊆ M*`, and `C({g}) ⊆ C({x})` (since `x ∈ ⟨g⟩`).
    have hCx_Mstar : Subgroup.centralizer ({x} : Set G) ≤ Mstar := by
      refine le_trans ?_ ((Subgroup.centralizer_le_normalizer _).trans hNxM)
      intro y hy
      rw [Subgroup.mem_centralizer_iff] at hy ⊢
      intro z hz
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      have hc : Commute y x := (hy x rfl).symm
      exact ((hc.zpow_right k).eq).symm
    have hCgCx : Subgroup.centralizer ({g} : Set G) ≤ Subgroup.centralizer ({x} : Set G) := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff] at hy ⊢
      intro z hz
      rw [Set.mem_singleton_iff] at hz; subst hz
      have hc : Commute y g := (hy g rfl).symm
      exact ((hc.pow_right (orderOf g / p)).eq).symm
    -- assemble: `M_σ ⊓ C(g) ≤ M_σ ⊓ C(x) ≤ M_σ ⊓ M* ≤ C(E₃)`.
    rw [fixedByElement_def, fixedBy_def]
    refine le_inf inf_le_left ?_
    calc S10.Msigma M ⊓ Subgroup.centralizer ({g} : Set G)
        ≤ S10.Msigma M ⊓ Subgroup.centralizer ({x} : Set G) := inf_le_inf_left _ hCgCx
      _ ≤ S10.Msigma M ⊓ Mstar := inf_le_inf_left _ hCx_Mstar
      _ ≤ Subgroup.centralizer (E₃ : Set G) := hMMcE3

/-- **BG Theorem 13.5** (mmd L3570): `E₁ ≠ 1` なら `E₁` は `M_σ` に prime 作用。

`E₁` is cyclic (Lemma 12.1(d)). The crux is a *cross-prime* fact: for any prime-order element
`x ∈ E₁`, `C_{M_σ}(x) = C_{M_σ}(E₁)`. `C_{M_σ}(E₁) ⊆ C_{M_σ}(x)` is free; for the reverse,
`le_centralizer_of_forall_prime_isPGroup` reduces `E₁ ≤ C(C_{M_σ}(x))` to: every prime-power
subgroup `R ≤ E₁` is centralized by `C_{M_σ}(x)`. Picking an order-`r` element `y ∈ R`,
Theorem 13.4 (with `⟨x⟩ ∈ ℰ_p¹(E)` and `⟨y⟩ ∈ ℰ_r¹(C_E(⟨x⟩))`, valid since `E₁` is abelian) gives
`C_{M_σ}(x) ⊆ C_{M_σ}(y) = C_{M_σ}(R)` (last equality is `R`'s prime action, Corollary 13.3(a)
core),
so `C_{M_σ}(x) ≤ C(R)`. A general `g ∈ E₁#` reduces to its prime-power `x = g^{ord g / p}` via
`C(g) ⊆ C(x)`. No explicit Sylow decomposition of `E₁` is needed: the prime-power induction in
`le_centralizer_of_forall_prime_isPGroup` carries it. -/
theorem E1_actsPrime [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) (_hE1 : E₁ ≠ ⊥) :
    ActsPrimeOn (S10.Msigma M) E₁ := by
  classical
  have hcyc : IsCyclic ↥E₁ := h.E1_isCyclic hG
  let : CommGroup ↥E₁ := IsCyclic.commGroup
  -- `C({z}) = C(⟨z⟩)`: centralizing an element is the same as centralizing the cyclic subgroup.
  have hcent_zpowers : ∀ z : G,
      Subgroup.centralizer ({z} : Set G)
        = Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
    intro z
    apply le_antisymm
    · intro w hw
      rw [Subgroup.mem_centralizer_iff] at hw ⊢
      intro u hu
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      have hcm : Commute z w := hw z rfl
      exact ((hcm.symm.zpow_right k).eq).symm
    · exact Subgroup.centralizer_le (by
        intro u hu; rw [Set.mem_singleton_iff] at hu; rw [hu]; exact Subgroup.mem_zpowers z)
  -- Elements of `E₁` commute (E₁ abelian).
  have hE1comm : ∀ a ∈ E₁, ∀ b ∈ E₁, Commute a b := by
    intro a ha b hb
    exact Subtype.ext_iff.mp (mul_comm (⟨a, ha⟩ : ↥E₁) ⟨b, hb⟩)
  -- `⟨z⟩ ∈ ℰ_s¹` for a prime-order element `z`.
  have hzp_mem : ∀ (s : ℕ) (z : G), s.Prime → orderOf z = s →
      Subgroup.zpowers z ∈ elemAbelianOfRank G s 1 := by
    intro s z hs hzord
    have : Fact s.Prime := ⟨hs⟩
    refine mem_elemAbelianOfRank.mpr ⟨?_, ?_⟩
    · exact Subgroup.IsElementaryAbelian.of_card_prime (by rw [Nat.card_zpowers]; exact hzord)
    · rw [pow_one, Nat.card_zpowers]; exact hzord
  -- Sub-claim A: a prime-order element `x ∈ E₁` has `C_{M_σ}(x) = C_{M_σ}(E₁)`.
  have key : ∀ (p : ℕ) (x : G), x ∈ E₁ → p.Prime → orderOf x = p →
      fixedByElement (S10.Msigma M) x = fixedBy (S10.Msigma M) E₁ := by
    intro p x hxE1 hp hxord
    have : Fact p.Prime := ⟨hp⟩
    have hxmem : Subgroup.zpowers x ∈ elemAbelianOfRank G p 1 := hzp_mem p x hp hxord
    have hxE : (Subgroup.zpowers x : Subgroup G) ≤ E :=
      (Subgroup.zpowers_le.mpr hxE1).trans h.E₁_le
    have hpπE1 : p ∈ (Nat.card ↥E₁).primeFactors := by
      refine Nat.mem_primeFactors.mpr ⟨hp, ?_, Nat.card_pos.ne'⟩
      rw [← hxord, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hxE1)
    have hpτ1 : p ∈ tau1 M := h.isPiGroup_tau1 p hpπE1
    refine le_antisymm ?_ (fixedBy_le_fixedByElement hxE1)
    -- `C_{M_σ}(x) ≤ C_{M_σ}(E₁)`; reduce to `C_{M_σ}(x) ≤ C(↑E₁)`.
    rw [fixedBy_def]
    refine le_inf (by rw [fixedByElement_def]; exact inf_le_left) ?_
    rw [← Subgroup.le_centralizer_iff]
    apply le_centralizer_of_forall_prime_isPGroup
    intro r hr R hRE1 hRr
    rcases eq_or_ne R ⊥ with rfl | hRne
    · exact bot_le
    · have : Fact r.Prime := ⟨hr⟩
      rw [← Subgroup.le_centralizer_iff]
      -- `R` is abelian (≤ E₁) and nontrivial; extract an order-`r` element `y ∈ R`.
      have hRab : IsMulCommutative ↥R := ⟨⟨fun a b => Subtype.ext (by
        simp only [Subgroup.coe_mul]; exact hE1comm (a : G) (hRE1 a.2) (b : G) (hRE1 b.2))⟩⟩
      obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hRne
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hRr) a
      have hak0 : k ≠ 0 := by
        rintro rfl; rw [pow_zero] at hk; exact ha1 (orderOf_eq_one_iff.mp hk)
      have haR : (a : G) ∈ R := a.2
      have haord : orderOf (a : G) = r ^ k := by rw [Subgroup.orderOf_coe]; exact hk
      have hrdvd : r ∣ orderOf (a : G) := by rw [haord]; exact dvd_pow_self r hak0
      have hyr1 : ((a : G) ^ (orderOf (a : G) / r)) ^ r = 1 := by
        rw [← pow_mul, Nat.div_mul_cancel hrdvd, pow_orderOf_eq_one]
      have hy1 : (a : G) ^ (orderOf (a : G) / r) ≠ 1 := by
        intro hh
        have hdvd := orderOf_dvd_of_pow_eq_one hh
        have hpos : 0 < orderOf (a : G) / r :=
          Nat.div_pos (Nat.le_of_dvd (orderOf_pos _) hrdvd) hr.pos
        have hlt : orderOf (a : G) / r < orderOf (a : G) :=
          Nat.div_lt_self (orderOf_pos _) hr.one_lt
        exact absurd (Nat.le_of_dvd hpos hdvd) (by omega)
      have hyord : orderOf ((a : G) ^ (orderOf (a : G) / r)) = r := by
        rcases (Nat.dvd_prime hr).mp (orderOf_dvd_of_pow_eq_one hyr1) with hh | hh
        · exact absurd (orderOf_eq_one_iff.mp hh) hy1
        · exact hh
      have hyR : (a : G) ^ (orderOf (a : G) / r) ∈ R := pow_mem haR _
      set y : G := (a : G) ^ (orderOf (a : G) / r) with hydef
      have hyE1 : y ∈ E₁ := hRE1 hyR
      have hyE : y ∈ E := h.E₁_le hyE1
      -- `⟨y⟩ ∈ ℰ_r¹`, `r ∈ π(E)`, `r ∈ τ₁(M)`.
      have hymem : Subgroup.zpowers y ∈ elemAbelianOfRank G r 1 := hzp_mem r y hr hyord
      have hrπE : r ∈ (Nat.card ↥E).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hr, hyord ▸ E.orderOf_dvd_natCard hyE, Nat.card_pos.ne'⟩
      have hrτ1 : r ∈ tau1 M :=
        h.isPiGroup_tau1 r (Nat.mem_primeFactors.mpr
          ⟨hr, hyord ▸ E₁.orderOf_dvd_natCard hyE1, Nat.card_pos.ne'⟩)
      -- `⟨y⟩ ≤ E ⊓ C(↑⟨x⟩)` (y commutes with x).
      have hyRC : (Subgroup.zpowers y : Subgroup G) ≤
          E ⊓ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
        refine le_inf ((Subgroup.zpowers_le.mpr hyE1).trans h.E₁_le) ?_
        rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        intro u hu
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
        exact ((hE1comm x hxE1 y hyE1).zpow_left j).eq
      -- Theorem 13.4 and the prime action of `R`.
      have hT134 := centralizer_le_centralizer_of_tau1 hG h hpτ1 hrπE hxmem hxE hymem hyRC
      have hRact : ActsPrimeOn (S10.Msigma M) R :=
        actsPrimeOn_Msigma_of_mem_tau13 hG h (Or.inl hrτ1) (hRE1.trans h.E1_le_M) hRab hRr
      have hRy : fixedByElement (S10.Msigma M) y = fixedBy (S10.Msigma M) R := hRact y hyR hy1
      calc fixedByElement (S10.Msigma M) x
          = S10.Msigma M ⊓ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
            rw [fixedByElement_def, hcent_zpowers x]
        _ ≤ S10.Msigma M ⊓ Subgroup.centralizer ((Subgroup.zpowers y : Subgroup G) : Set G) := hT134
        _ = fixedByElement (S10.Msigma M) y := by rw [fixedByElement_def, hcent_zpowers y]
        _ = fixedBy (S10.Msigma M) R := hRy
        _ ≤ Subgroup.centralizer ((R : Subgroup G) : Set G) := by
            rw [fixedBy_def]; exact inf_le_right
  -- Main: reduce a general `g ∈ E₁#` to its prime-power part `x = g^{ord g / p}`.
  intro g hgE1 hg1
  have hord1 : orderOf g ≠ 1 := fun hh => hg1 (orderOf_eq_one_iff.mp hh)
  obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd hord1
  have hxp1 : (g ^ (orderOf g / p)) ^ p = 1 := by
    rw [← pow_mul, Nat.div_mul_cancel hp_dvd, pow_orderOf_eq_one]
  have hx1 : g ^ (orderOf g / p) ≠ 1 := by
    intro hh
    have hdvd := orderOf_dvd_of_pow_eq_one hh
    have hpos : 0 < orderOf g / p := Nat.div_pos (Nat.le_of_dvd (orderOf_pos g) hp_dvd) hp_prime.pos
    have hlt : orderOf g / p < orderOf g := Nat.div_lt_self (orderOf_pos g) hp_prime.one_lt
    exact absurd (Nat.le_of_dvd hpos hdvd) (by omega)
  have hxord : orderOf (g ^ (orderOf g / p)) = p := by
    rcases (Nat.dvd_prime hp_prime).mp (orderOf_dvd_of_pow_eq_one hxp1) with hh | hh
    · exact absurd (orderOf_eq_one_iff.mp hh) hx1
    · exact hh
  have hxE1 : g ^ (orderOf g / p) ∈ E₁ := pow_mem hgE1 _
  -- `C(g) ≤ C(x)` since `x = g^(ord g / p)`.
  have hCgx : Subgroup.centralizer ({g} : Set G)
      ≤ Subgroup.centralizer ({g ^ (orderOf g / p)} : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff] at hw ⊢
    intro u hu
    rw [Set.mem_singleton_iff] at hu; subst hu
    have hcm : Commute g w := hw g rfl
    exact (hcm.pow_left (orderOf g / p)).eq
  have hkey := key p (g ^ (orderOf g / p)) hxE1 hp_prime hxord
  refine le_antisymm ?_ (fixedBy_le_fixedByElement hgE1)
  calc fixedByElement (S10.Msigma M) g
      ≤ fixedByElement (S10.Msigma M) (g ^ (orderOf g / p)) := by
        rw [fixedByElement_def, fixedByElement_def]; exact inf_le_inf_left _ hCgx
    _ = fixedBy (S10.Msigma M) E₁ := hkey

private theorem subtype_comp_conj_eq {U : Subgroup G} (n' : ↥U) :
    U.subtype.comp ((MulAut.conj n').toMonoidHom) =
      ((MulAut.conj (n'.val : G)).toMonoidHom).comp U.subtype := by
  ext ⟨x, hx⟩; rfl

private theorem map_subtype_conj_subgroupOf {U : Subgroup G} (n' : ↥U) (K : Subgroup G)
    (hKU : K ≤ U) :
    ((K.subgroupOf U).map (MulAut.conj n').toMonoidHom).map U.subtype =
      K.map (MulAut.conj (n'.val : G)).toMonoidHom := by
  rw [Subgroup.map_map, subtype_comp_conj_eq, ← Subgroup.map_map,
    Subgroup.map_subgroupOf_eq_of_le hKU]

/-- **ℳ-transfer between maximal `q`-subgroups of `N ≤ M`.** If `S` and `S₀` are both maximal
`q`-subgroups of `N` (`N ≤ M`, `M` maximal in `G`) and `ℳ(S₀) = {M}`, then `ℳ(S) = {M}`. The two
are conjugate by some `m ∈ N` (Sylow conjugacy inside `↥N`); since `m ∈ M`, conjugation by `m` fixes
`M`, so the unique maximal over `S₀` transports to the unique maximal over `S`. Used in Lemma 13.6
to
pass from the internal Sylow `S₀ ⊇ X` of the faithful Corollary 12.14 to the arbitrary Sylow `S`. -/
theorem maximalContaining_eq_singleton_of_maximal_qsubgroup [Finite G]
    {M N S S₀ : Subgroup G} (hM : M ∈ maximalSubgroups G) (hNM : N ≤ M)
    {q : ℕ} [Fact q.Prime]
    (hSN : S ≤ N) (hSq : IsPGroup q ↥S)
    (hSmax : ∀ T : Subgroup G, T ≤ N → IsPGroup q ↥T → S ≤ T → S = T)
    (hS₀N : S₀ ≤ N) (hS₀q : IsPGroup q ↥S₀)
    (hS₀max : ∀ T : Subgroup G, T ≤ N → IsPGroup q ↥T → S₀ ≤ T → S₀ = T)
    (hMS₀ : maximalSubgroupsContaining S₀ = {M}) :
    maximalSubgroupsContaining S = {M} := by
  classical
  -- A maximal `q`-subgroup `R ≤ N` is the carrier of a Sylow `q`-subgroup of `↥N`.
  have key : ∀ R : Subgroup G, R ≤ N → IsPGroup q ↥R →
      (∀ T : Subgroup G, T ≤ N → IsPGroup q ↥T → R ≤ T → R = T) →
      ∃ P : Sylow q ↥N, (P : Subgroup ↥N) = R.subgroupOf N := by
    intro R hRN hRq hRmax
    have hRq' : IsPGroup q ↥(R.subgroupOf N) :=
      hRq.of_equiv (Subgroup.subgroupOfEquivOfLe hRN).symm
    obtain ⟨P, hRP⟩ := hRq'.exists_le_sylow
    refine ⟨P, ?_⟩
    have hTN : (P : Subgroup ↥N).map N.subtype ≤ N := Subgroup.map_subtype_le _
    have hTq : IsPGroup q ↥((P : Subgroup ↥N).map N.subtype) :=
      P.2.of_equiv (Subgroup.equivMapOfInjective _ _ N.subtype_injective)
    have hRT : R ≤ (P : Subgroup ↥N).map N.subtype := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hRN]
      exact Subgroup.map_mono hRP
    have hRTeq : R = (P : Subgroup ↥N).map N.subtype := hRmax _ hTN hTq hRT
    rw [hRTeq, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective N.subtype_injective]
  obtain ⟨PS, hPS⟩ := key S hSN hSq hSmax
  obtain ⟨PS₀, hPS₀⟩ := key S₀ hS₀N hS₀q hS₀max
  -- Sylow conjugacy inside `↥N`.
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥N) PS₀ PS
  have hgsub : (PS₀ : Subgroup ↥N).map (MulAut.conj g).toMonoidHom = (PS : Subgroup ↥N) := by
    have h := congr_arg Sylow.toSubgroup hg
    rwa [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
  set m : G := (g : G) with hm
  have hmN : m ∈ N := g.2
  -- Push the conjugation down to `G`: `m S₀ m⁻¹ = S` (`•`-form; `map (conj m).toMonoidHom` is
  -- defeq).
  have hconj : MulAut.conj m • S₀ = S := by
    have hlhs := map_subtype_conj_subgroupOf g S₀ hS₀N
    rw [← hPS₀, hgsub, hPS, Subgroup.map_subgroupOf_eq_of_le hSN] at hlhs
    exact hlhs.symm
  -- `ℳ(S) = {M}` by transporting `ℳ(S₀) = {M}` along `conj m` (`m ∈ N ≤ M` fixes `M`).
  rw [Set.eq_singleton_iff_unique_mem]
  refine ⟨mem_maximalSubgroupsContaining.mpr ⟨mem_maximalSubgroups.mp hM, hSN.trans hNM⟩, ?_⟩
  intro N' hN'
  rw [mem_maximalSubgroupsContaining] at hN'
  obtain ⟨hN'coat, hSN'⟩ := hN'
  have hSN'' : MulAut.conj m • S₀ ≤ N' := by rw [hconj]; exact hSN'
  have hWmem : MulAut.conj m⁻¹ • N' ∈ maximalSubgroupsContaining S₀ := by
    rw [mem_maximalSubgroupsContaining]
    refine ⟨isCoatom_conj_smul hN'coat, ?_⟩
    calc S₀ = MulAut.conj m⁻¹ • (MulAut.conj m • S₀) := by
              rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
      _ ≤ MulAut.conj m⁻¹ • N' := Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hSN''
  rw [hMS₀, Set.mem_singleton_iff] at hWmem
  have hN'eq : MulAut.conj m • M = N' := by
    rw [← hWmem, ← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
  rw [← hN'eq]
  exact conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer (hNM hmN))

/-- **Lemma 13.6 contradiction half, steps 3–4**: if `X ≤ M_σ` centralizes both `E₁` and `E'`
but `X ⊄ M_σ'`, then `E₂ ≠ 1`. Step 3: `E₁ ⊔ E' = E` would give `X ≤ C_{M_σ}(E) ⊆ M_σ'`
(Lemma 12.17), contra `X ⊄ M_σ'`. Step 4: `E₂ = 1` gives `E = E₁ ⊔ E₃ ≤ E₁ ⊔ E'` (`E₃ ≤ E'`),
forcing `E₁ ⊔ E' = E`. -/
theorem E2_ne_bot_of_centralizer [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {X : Subgroup G}
    (hXMσ : X ≤ S10.Msigma M) (hXE1 : X ≤ Subgroup.centralizer (E₁ : Set G))
    (hXE' : X ≤ Subgroup.centralizer (derivedInG E : Set G))
    (hXMσ' : ¬ (X ≤ derivedInG (S10.Msigma M))) :
    E₂ ≠ ⊥ := by
  have hsup_ne : E₁ ⊔ derivedInG E ≠ E := by
    intro hEeq
    have hEcx : E ≤ Subgroup.centralizer (X : Set G) :=
      hEeq ▸ sup_le (Subgroup.le_centralizer_iff.mp hXE1) (Subgroup.le_centralizer_iff.mp hXE')
    exact hXMσ' (le_trans (le_inf (Subgroup.le_centralizer_iff.mp hEcx) hXMσ)
      (Msigma_E_relations hG h).1)
  intro hE2bot
  refine hsup_ne (le_antisymm (sup_le h.E₁_le (Subgroup.map_subtype_le _)) ?_)
  calc E = E₁ ⊔ E₂ ⊔ E₃ := h.eq_sup hG
    _ = E₁ ⊔ E₃ := by rw [hE2bot, sup_bot_eq]
    _ ≤ E₁ ⊔ derivedInG E := sup_le_sup_left (h.E3_le_derived hG) E₁

/-- A nontrivial `E₁` (Hall `τ₁`-subgroup of `E`) contains a `τ₁(M)`-line: `∃ ℓ ∈ τ₁(M)` and
`P ∈ ℰ_ℓ¹(E₁)`. (Cauchy in `↥E₁` plus `π(E₁) ⊆ τ₁(M)`.) Used in Lemma 13.6 step 6 to apply
Theorem 13.4. -/
theorem exists_tau1_line_le_E1 [Finite G]
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) (hE1ne : E₁ ≠ ⊥) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∈ tau1 M ∧ ∃ P : Subgroup G, P ∈ elemAbelianOfRank G ℓ 1 ∧ P ≤ E₁ := by
  have hcard : Nat.card ↥E₁ ≠ 1 := fun hh => hE1ne (Subgroup.card_eq_one.mp hh)
  obtain ⟨ℓ, hℓp, hℓdvd⟩ := Nat.exists_prime_and_dvd hcard
  have : Fact ℓ.Prime := ⟨hℓp⟩
  have hℓτ1 : ℓ ∈ tau1 M :=
    h.isPiGroup_tau1 ℓ (Nat.mem_primeFactors.mpr ⟨hℓp, hℓdvd, Nat.card_pos.ne'⟩)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥E₁) ℓ hℓdvd
  have hPcard : Nat.card ↥((Subgroup.zpowers x).map E₁.subtype) = ℓ := by
    rw [Subgroup.card_map_of_injective E₁.subtype_injective, Nat.card_zpowers, hx]
  refine ⟨ℓ, hℓp, hℓτ1, (Subgroup.zpowers x).map E₁.subtype, ?_, Subgroup.map_subtype_le _⟩
  exact mem_elemAbelianOfRank.mpr
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hPcard, by rw [pow_one]; exact hPcard⟩

/-- **Lemma 13.6 step 6, `A₀ = C_A(E₁)` part**: if `X ≤ M_σ ⊓ C_G(E₁)`, `A ≤ E` is elementary
abelian `p` (`p ∈ τ₂`) and `E₁ ≠ 1`, then `A ⊓ C_G(E₁) ≤ C_G(X)`. Per nonidentity `a ∈ A ⊓ C(E₁)`:
`⟨a⟩ ∈ ℰ_p¹(C_E(P))` for a `τ₁`-line `P ≤ E₁`, so Theorem 13.4 gives `C_{M_σ}(P) ≤ C_{M_σ}(⟨a⟩)`;
prime action (`C_{M_σ}(P) = C_{M_σ}(E₁) ⊇ X`) then forces `X ≤ C(⟨a⟩)`, i.e. `a ∈ C(X)`. -/
theorem centralizer_A0_le_centralizer [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {p : ℕ} [Fact p.Prime] {A X : Subgroup G}
    (hAE : A ≤ E) (hAelem : A.IsElementaryAbelian p) (hE1ne : E₁ ≠ ⊥)
    (hXE1 : X ≤ S10.Msigma M ⊓ Subgroup.centralizer (E₁ : Set G)) :
    A ⊓ Subgroup.centralizer (E₁ : Set G) ≤ Subgroup.centralizer (X : Set G) := by
  classical
  obtain ⟨ℓ, hℓp, hℓτ1, P, hPmem, hPE1⟩ := exists_tau1_line_le_E1 h hE1ne
  have : Fact ℓ.Prime := ⟨hℓp⟩
  have hPne : P ≠ ⊥ := ne_bot_of_mem_elemAbelianOfRank_one hPmem
  have hCPeq : S10.Msigma M ⊓ Subgroup.centralizer (P : Set G)
      = S10.Msigma M ⊓ Subgroup.centralizer (E₁ : Set G) := by
    have := fixedBy_eq_of_le_of_ne_bot (E1_actsPrime hG h hE1ne) hPE1 hPne
    rwa [fixedBy_def, fixedBy_def] at this
  have hXP : X ≤ S10.Msigma M ⊓ Subgroup.centralizer (P : Set G) := hCPeq ▸ hXE1
  intro a ha
  obtain ⟨haA, haE1⟩ := Subgroup.mem_inf.mp ha
  by_cases ha1 : a = 1
  · subst ha1; exact Subgroup.one_mem _
  · have hap : a ^ p = 1 := by
      have h1 := hAelem.pow_eq_one (⟨a, haA⟩ : ↥A)
      have h2 := congrArg (A.subtype) h1
      simpa using h2
    have hordp : orderOf a = p := orderOf_eq_prime hap ha1
    have hRcard : Nat.card ↥(Subgroup.zpowers a) = p := by rw [Nat.card_zpowers, hordp]
    have hRmem : Subgroup.zpowers a ∈ elemAbelianOfRank G p 1 :=
      mem_elemAbelianOfRank.mpr ⟨Subgroup.IsElementaryAbelian.of_card_prime hRcard,
        by rw [pow_one]; exact hRcard⟩
    have hRCP : Subgroup.zpowers a ≤ Subgroup.centralizer (P : Set G) :=
      Subgroup.zpowers_le.mpr
        (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hPE1) haE1)
    have hRC : Subgroup.zpowers a ≤ E ⊓ Subgroup.centralizer (P : Set G) :=
      le_inf (Subgroup.zpowers_le.mpr (hAE haA)) hRCP
    have hpπE : p ∈ (Nat.card ↥E).primeFactors := by
      have hoE : orderOf (⟨a, hAE haA⟩ : ↥E) = p := by
        rw [← hordp]; exact (orderOf_injective E.subtype E.subtype_injective _).symm
      exact Nat.mem_primeFactors.mpr ⟨Fact.out, hoE ▸ orderOf_dvd_natCard _, Nat.card_pos.ne'⟩
    have hthm := centralizer_le_centralizer_of_tau1 hG h hℓτ1 hpπE hPmem
      (hPE1.trans h.E₁_le) hRmem hRC
    have hXR : X ≤ Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) :=
      ((hXP.trans hthm).trans inf_le_right)
    exact (Subgroup.le_centralizer_iff.mp hXR) (Subgroup.mem_zpowers a)

/-- **Proposition 1.6(d), subgroup form**: for a coprime action of `E₁` on `A` (`E₁ ≤ N_G(A)`,
coprime orders, one side solvable), `A = C_A(E₁) ⊔ ⁅A, E₁⁆`. (Translation of
`fixedPoints_sup_actionCommutator_eq_top` via the `conj_map_subtype` bridges.) -/
theorem subgroup_coprime_decomposition [Finite G] {A E₁ : Subgroup G}
    (hE1A : E₁ ≤ Subgroup.normalizer (A : Set G))
    (hcop : Nat.Coprime (Nat.card ↥E₁) (Nat.card ↥A))
    (hSolv : Group.IsSolvable ↥E₁ ∨ Group.IsSolvable ↥A) :
    A = (Subgroup.centralizer (E₁ : Set G) ⊓ A) ⊔ ⁅A, E₁⁆ := by
  have hmap := congrArg (Subgroup.map A.subtype)
    (Ch04.fixedPoints_sup_actionCommutator_eq_top
      (φ := (Subgroup.normalizerMonoidHom A).comp (Subgroup.inclusion hE1A)) hcop hSolv)
  rw [Subgroup.map_sup, OddOrder.BG.Ch1.S06.fixedPointsOfMulAut_conj_map_subtype hE1A,
    OddOrder.BG.Ch1.S06.actionCommutator_conj_map_subtype hE1A,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmap
  exact hmap.symm

/-- **Lemma 13.6 step 6, full `A` part**: with `X ≤ M_σ ⊓ C(E₁)` and `X ≤ C(E')`, a normal
elementary abelian `p`-subgroup `A ≤ E` (`p ∈ τ₂`, `E₁ ≠ 1`) centralizes `X`. Decompose
`A = C_A(E₁) ⊔ ⁅A,E₁⁆` (Prop 1.6, coprime since `p ∈ τ₂`, `π(E₁) ⊆ τ₁`); `C_A(E₁) ≤ C(X)` by
`centralizer_A0_le_centralizer`, and `⁅A,E₁⁆ ≤ ⁅E,E⁆ = E' ≤ C(X)`. -/
theorem centralizer_A_le_centralizer [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {p : ℕ} [Fact p.Prime] (hp : p ∈ tau2 M) {A X : Subgroup G}
    (hAE : A ≤ E) (hAnorm : E ≤ Subgroup.normalizer (A : Set G)) (hAelem : A.IsElementaryAbelian p)
    (hE1ne : E₁ ≠ ⊥) (hXE1 : X ≤ S10.Msigma M ⊓ Subgroup.centralizer (E₁ : Set G))
    (hXE' : X ≤ Subgroup.centralizer (derivedInG E : Set G)) :
    A ≤ Subgroup.centralizer (X : Set G) := by
  have hpndvd : ¬ p ∣ Nat.card ↥E₁ := by
    intro hdvd
    have hpτ1 := h.isPiGroup_tau1 p (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩)
    exact absurd ((((mem_tau1_iff M p).mp hpτ1).2.2).symm.trans ((mem_tau2_iff M p).mp hp).2)
      (by norm_num)
  have hcop : Nat.Coprime (Nat.card ↥E₁) (Nat.card ↥A) := by
    obtain ⟨k, hk⟩ := hAelem.isPGroup.exists_card_eq
    rw [hk]
    exact (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hpndvd)).pow_right k
  rw [subgroup_coprime_decomposition (h.E₁_le.trans hAnorm) hcop
    (Or.inr (Group.isSolvable_of_comm hAelem.comm))]
  refine sup_le ?_ ?_
  · rw [inf_comm]; exact centralizer_A0_le_centralizer hG h hAE hAelem hE1ne hXE1
  · calc ⁅A, E₁⁆ ≤ ⁅E, E⁆ := Subgroup.commutator_mono hAE h.E₁_le
      _ = derivedInG E := (Subgroup.map_subtype_commutator E).symm
      _ ≤ Subgroup.centralizer (X : Set G) := Subgroup.le_centralizer_iff.mp hXE'

private theorem card_conj_smul (g : G) (H : Subgroup G) :
    Nat.card ↥(MulAut.conj g • H) = Nat.card ↥H :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

/-- The Hall property transports under conjugating a `subgroupOf` pair `K ≤ E` by any `c`. -/
private theorem isHallSubgroup_subgroupOf_conj [Finite G] {π : Set ℕ} {E K : Subgroup G}
    (hKE : K ≤ E) (c : G) (hHall : Ch03.IsHallSubgroup π (K.subgroupOf E)) :
    Ch03.IsHallSubgroup π ((MulAut.conj c • K).subgroupOf (MulAut.conj c • E)) := by
  have hcKE : MulAut.conj c • K ≤ MulAut.conj c • E :=
    Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hKE
  have hcard : Nat.card ↥((MulAut.conj c • K).subgroupOf (MulAut.conj c • E))
      = Nat.card ↥(K.subgroupOf E) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcKE).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKE).toEquiv, card_conj_smul]
  have hidx : ((MulAut.conj c • K).subgroupOf (MulAut.conj c • E)).index
      = (K.subgroupOf E).index := by
    have h1 := Subgroup.card_mul_index (K.subgroupOf E)
    have h2 := Subgroup.card_mul_index ((MulAut.conj c • K).subgroupOf (MulAut.conj c • E))
    rw [hcard, card_conj_smul] at h2
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h2.trans h1.symm)
  exact ⟨fun p hp => hHall.1 p (hcard ▸ hp), fun p hp => hHall.2 p (hidx ▸ hp)⟩

/-- **Conjugating a `SubgroupESetup` by `c ∈ M`.** Since `M` and `M_σ` are fixed by such
conjugation, `(MulAut.conj c • E, conj c • E₁, …)` is again a `SubgroupESetup` for `M`. With
`c ∈ C_G(E₁)` one gets `conj c • E₁ = E₁` (used in Lemma 13.6 step 2). -/
theorem SubgroupESetup.conj' [Finite G] {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃) {c : G} (hc : c ∈ M) :
    SubgroupESetup M (MulAut.conj c • E) (MulAut.conj c • E₁) (MulAut.conj c • E₂)
      (MulAut.conj c • E₃) := by
  have hcM : MulAut.conj c • M = M :=
    conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hc)
  have hcMσ : MulAut.conj c • S10.Msigma M = S10.Msigma M :=
    conj_smul_eq_self_of_mem_normalizer (le_normalizer_opiCoreInG (S10.sigma M) M hc)
  refine ⟨h.mem_maximal, ?_, ?_, ?_,
    Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr h.E₁_le,
    Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr h.E₂_le,
    Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr h.E₃_le,
    isHallSubgroup_subgroupOf_conj h.E₁_le c h.E₁_hall,
    isHallSubgroup_subgroupOf_conj h.E₂_le c h.E₂_hall,
    isHallSubgroup_subgroupOf_conj h.E₃_le c h.E₃_hall, ?_⟩
  · calc MulAut.conj c • E ≤ MulAut.conj c • M :=
          Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr h.E_le
      _ = M := hcM
  · rw [← hcMσ, ← Subgroup.smul_inf, h.E_compl_inf, Subgroup.smul_bot]
  · rw [← hcMσ, ← Subgroup.smul_sup, h.E_compl_sup, hcM]
  · rw [← Subgroup.smul_sup]
    exact isHallSubgroup_subgroupOf_conj (sup_le h.E₁_le h.E₂_le) c h.E₁₂_hall

/-- **Proposition 1.5(c), subgroup form**: two `A`-invariant Sylow `q`-subgroups `S, T` of `N`
(`A ≤ N_G(N)`, coprime orders, one side solvable) are conjugate by an element of `N ∩ C_G(A)`. -/
theorem aInvariant_sylow_conj_subgroup [Finite G] {A N : Subgroup G}
    (hAN : A ≤ Subgroup.normalizer (N : Set G)) (hcop : Nat.Coprime (Nat.card ↥A) (Nat.card ↥N))
    (hSolv : Group.IsSolvable ↥A ∨ Group.IsSolvable ↥N) {q : ℕ} [Fact q.Prime]
    {S T : Subgroup G} (hSN : S ≤ N)
    (hScard : Nat.card ↥(S.subgroupOf N) = q ^ (Nat.card ↥N).factorization q)
    (hSinv : A ≤ Subgroup.normalizer (S : Set G)) (hTN : T ≤ N)
    (hTcard : Nat.card ↥(T.subgroupOf N) = q ^ (Nat.card ↥N).factorization q)
    (hTinv : A ≤ Subgroup.normalizer (T : Set G)) :
    ∃ c : G, c ∈ N ∧ c ∈ Subgroup.centralizer (A : Set G) ∧ MulAut.conj c • S = T := by
  classical
  let act : MulDistribMulAction ↥A ↥N :=
    MulDistribMulAction.compHom (M := ↥(Subgroup.normalizer (N : Set G))) ↥N
      (Subgroup.inclusion hAN)
  set φ : ↥A →* MulAut ↥N := MulDistribMulAction.toMulAut ↥A ↥N with hφ
  have hφ_coe : ∀ (a : ↥A) (x : ↥N), ((φ a) x : G) = (a : G) * (x : G) * (a : G)⁻¹ :=
    fun _ _ => rfl
  have htr : ∀ K : Subgroup G, A ≤ Subgroup.normalizer (K : Set G) →
      Ch03.IsAInvariant φ (K.subgroupOf N) := by
    intro K hK
    rw [Ch03.isAInvariant_iff_smul_mem]
    intro a x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    rw [hφ_coe a x]
    exact (Subgroup.mem_normalizer_iff.mp (hK a.2) (x : G)).mp hx
  let Sn : Sylow q ↥N := Sylow.ofCard (S.subgroupOf N) hScard
  let Tn : Sylow q ↥N := Sylow.ofCard (T.subgroupOf N) hTcard
  have hSn : (Sn : Subgroup ↥N) = S.subgroupOf N := rfl
  have hTn : (Tn : Subgroup ↥N) = T.subgroupOf N := rfl
  obtain ⟨c, hc_fix, hc_conj⟩ := Ch04.aInvariant_sylow_conj hcop hSolv
    (S := Sn) (T := Tn) (htr S hSinv) (htr T hTinv)
  refine ⟨(c : G), c.2, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have h1 : ((φ ⟨g, hg⟩) c : G) = (c : G) := congrArg (fun z : ↥N => (z : G)) (hc_fix ⟨g, hg⟩)
    rw [hφ_coe ⟨g, hg⟩ c, mul_inv_eq_iff_eq_mul] at h1
    exact h1
  · have hgsub : (Sn : Subgroup ↥N).map (MulAut.conj c).toMonoidHom = (Tn : Subgroup ↥N) :=
      hc_conj
    have hlhs := map_subtype_conj_subgroupOf c S hSN
    rw [← hSn, hgsub, hTn, Subgroup.map_subgroupOf_eq_of_le hTN] at hlhs
    rw [Subgroup.pointwise_smul_def]; exact hlhs.symm

/-- **Proposition 1.5(b), subgroup form**: an `A`-invariant `q`-subgroup `P ≤ N` (`A ≤ N_G(N)`,
coprime, one side solvable) is contained in an `A`-invariant Sylow `q`-subgroup of `N`. -/
theorem aInvariant_pSubgroup_le_aInvariant_sylow_subgroup [Finite G] {A N : Subgroup G}
    (hAN : A ≤ Subgroup.normalizer (N : Set G)) (hcop : Nat.Coprime (Nat.card ↥A) (Nat.card ↥N))
    (hSolv : Group.IsSolvable ↥A ∨ Group.IsSolvable ↥N) {q : ℕ} [Fact q.Prime]
    {P : Subgroup G} (hPN : P ≤ N) (hPq : IsPGroup q ↥P)
    (hPinv : A ≤ Subgroup.normalizer (P : Set G)) :
    ∃ S : Subgroup G, S ≤ N ∧ IsPGroup q ↥S ∧ A ≤ Subgroup.normalizer (S : Set G) ∧ P ≤ S ∧
      Nat.card ↥S = q ^ (Nat.card ↥N).factorization q := by
  classical
  let act : MulDistribMulAction ↥A ↥N :=
    MulDistribMulAction.compHom (M := ↥(Subgroup.normalizer (N : Set G))) ↥N
      (Subgroup.inclusion hAN)
  set φ : ↥A →* MulAut ↥N := MulDistribMulAction.toMulAut ↥A ↥N with hφ
  have hφ_coe : ∀ (a : ↥A) (x : ↥N), (N.subtype ((φ a) x)) = (↑a) * (N.subtype x) * (↑a)⁻¹ :=
    fun _ _ => rfl
  have hφ_inv_coe : ∀ (a : ↥A) (x : ↥N),
      (N.subtype (((φ a)⁻¹) x)) = (↑a)⁻¹ * (N.subtype x) * (↑a) := by
    intro a x; rw [← map_inv]; simpa using hφ_coe a⁻¹ x
  have hPinv' : Ch03.IsAInvariant φ (P.subgroupOf N) := by
    rw [Ch03.isAInvariant_iff_smul_mem]
    intro a x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    change N.subtype ((φ a) x) ∈ P
    rw [hφ_coe a x]
    exact (Subgroup.mem_normalizer_iff.mp (hPinv a.2) (N.subtype x)).mp hx
  have hPqN : IsPGroup q ↥(P.subgroupOf N) := hPq.of_equiv (Subgroup.subgroupOfEquivOfLe hPN).symm
  obtain ⟨S', hS'inv, hPS'⟩ :=
    OddOrder.Isaacs.Ch04.aInvariant_pSubgroup_le_aInvariant_sylow hcop hSolv hPqN hPinv'
  set S : Subgroup G := (S' : Subgroup ↥N).map N.subtype with hSdef
  refine ⟨S, Subgroup.map_subtype_le _,
    S'.2.of_equiv (Subgroup.equivMapOfInjective _ _ N.subtype_injective), ?_, ?_, ?_⟩
  · intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨x, hxS, rfl⟩
      exact ⟨(φ ⟨a, ha⟩) x, hS'inv.smul_mem ⟨a, ha⟩ hxS, hφ_coe ⟨a, ha⟩ x⟩
    · rintro ⟨x, hxS, hx⟩
      refine ⟨((φ ⟨a, ha⟩)⁻¹) x, hS'inv.inv_smul_mem ⟨a, ha⟩ hxS, ?_⟩
      rw [hφ_inv_coe ⟨a, ha⟩ x, hx]
      change a⁻¹ * (a * y * a⁻¹) * a = y
      group
  · rw [hSdef]
    calc P = (P.subgroupOf N).map N.subtype := (Subgroup.map_subgroupOf_eq_of_le hPN).symm
      _ ≤ (S' : Subgroup ↥N).map N.subtype := Subgroup.map_mono hPS'
  · rw [hSdef, Subgroup.card_map_of_injective N.subtype_injective, S'.card_eq_multiplicity]

/-- **Lemma 13.6 step 2, the `E'`-centralized Sylow.** For `q ∉ β(M)`, there is an `E₁`-invariant
Sylow `q`-subgroup `S₀` of `M_σ` contained in `C_G(E')`. (Lemma 12.19 gives a Hall `β'`-subgroup
`W ⊆ C_{M_σ}(E')` with full `q`-part since `q ∈ β'`, so `|C_{M_σ}(E')|_q = |M_σ|_q`; then
`exists_aInvariant_sylow_subgroup` for `E₁` acting on `C_{M_σ}(E')`.) -/
theorem exists_E1inv_sylow_centralizing_derivedE [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {q : ℕ} [Fact q.Prime]
    (hqβ : q ∉ S10.beta M) :
    ∃ S₀ : Subgroup G, S₀ ≤ S10.Msigma M ∧ IsPGroup q ↥S₀ ∧
      E₁ ≤ Subgroup.normalizer (S₀ : Set G) ∧
      S₀ ≤ Subgroup.centralizer (derivedInG E : Set G) ∧
      Nat.card ↥S₀ = q ^ (Nat.card ↥(S10.Msigma M)).factorization q := by
  classical
  obtain ⟨W, hWMσ, hWhall, hE'CW⟩ := derivedE_centralizes_betaComplement hG h
  set N : Subgroup G := S10.Msigma M ⊓ Subgroup.centralizer (derivedInG E : Set G) with hNdef
  have hWN : W ≤ N := le_inf hWMσ (Subgroup.le_centralizer_iff.mp hE'CW)
  have hNMσ : N ≤ S10.Msigma M := inf_le_left
  have hMσM : S10.Msigma M ≤ M := S10.Msigma_le M
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups h.mem_maximal
  have hNsolv : Group.IsSolvable ↥N :=
    Group.isSolvable_of_surjective
      (f := (Subgroup.subgroupOfEquivOfLe (hNMσ.trans hMσM)).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe (hNMσ.trans hMσM)).surjective
  -- `E₁ ≤ N_G(N)`: `E₁` normalizes `M_σ` and `E'`, hence `C_G(E')` and `N`.
  have hE1NMσ : E₁ ≤ Subgroup.normalizer ((S10.Msigma M : Subgroup G) : Set G) :=
    h.E1_le_M.trans (le_normalizer_opiCoreInG (S10.sigma M) M)
  have hE1NCE' : E₁ ≤ Subgroup.normalizer ((Subgroup.centralizer (derivedInG E : Set G)) : Set G) :=
    (h.E₁_le.trans (S10.le_normalizer_derivedInG E)).trans
      (normalizer_le_normalizer_centralizer (derivedInG E))
  have hE1NN : E₁ ≤ Subgroup.normalizer (N : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hNdef]
    simp only [Subgroup.mem_inf]
    rw [Subgroup.mem_normalizer_iff.mp (hE1NMσ hg) x,
      Subgroup.mem_normalizer_iff.mp (hE1NCE' hg) x]
  -- coprime `(|E₁|, |N|)`.
  have hcop_MσE : Nat.Coprime (Nat.card ↥(S10.Msigma M)) (Nat.card ↥E) := by
    have h1 := (S10.Msigma_subgroupOf_isHall hG h.mem_maximal).coprime_index
    rw [h.isComplement'_subgroupOf.symm.index_eq_card] at h1
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMσM).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E_le).toEquiv] at h1
  have hcop : Nat.Coprime (Nat.card ↥E₁) (Nat.card ↥N) :=
    (hcop_MσE.symm.coprime_dvd_left (Subgroup.card_dvd_of_le h.E₁_le)).coprime_dvd_right
      (Subgroup.card_dvd_of_le hNMσ)
  obtain ⟨S₀, hS₀N, hS₀q, hS₀inv, hS₀card⟩ :=
    exists_aInvariant_sylow_subgroup hE1NN hcop (Or.inr hNsolv) q
  -- `|N|_q = |M_σ|_q` (squeeze `W ≤ N ≤ M_σ`, `W` Hall `β'`, `q ∈ β'`).
  have hfactW : (Nat.card ↥(S10.Msigma M)).factorization q = (Nat.card ↥W).factorization q := by
    have hqidx : q ∉ ((W.subgroupOf (S10.Msigma M)).index).primeFactors :=
      fun hh => hWhall.2 q hh hqβ
    have hcardeq : Nat.card ↥(S10.Msigma M)
        = Nat.card ↥W * (W.subgroupOf (S10.Msigma M)).index := by
      rw [← Subgroup.card_mul_index (W.subgroupOf (S10.Msigma M)),
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWMσ).toEquiv]
    rw [hcardeq, Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd
        (fun hd =>
          hqidx (Nat.mem_primeFactors.mpr ⟨Fact.out, hd, Subgroup.index_ne_zero_of_finite⟩)),
      add_zero]
  have hcardN : (Nat.card ↥N).factorization q = (Nat.card ↥(S10.Msigma M)).factorization q := by
    have h1 : (Nat.card ↥W).factorization q ≤ (Nat.card ↥N).factorization q :=
      (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
        (Subgroup.card_dvd_of_le hWN) q
    have h2 : (Nat.card ↥N).factorization q ≤ (Nat.card ↥(S10.Msigma M)).factorization q :=
      (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
        (Subgroup.card_dvd_of_le hNMσ) q
    exact le_antisymm h2 (hfactW.trans_le h1)
  exact ⟨S₀, hS₀N.trans hNMσ, hS₀q, hS₀inv, hS₀N.trans inf_le_right, by rw [hS₀card, hcardN]⟩

private theorem smul_centralizer_conj (g : G) (H : Subgroup G) :
    MulAut.conj g • Subgroup.centralizer (H : Set G)
      = Subgroup.centralizer ((MulAut.conj g • H : Subgroup G) : Set G) :=
  Subgroup.map_centralizer_eq_of_bijective (H : Set G) (MulAut.conj g).toMonoidHom
    (MulAut.conj g).bijective

set_option backward.isDefEq.respectTransparency false in
private theorem smul_derivedInG_conj (g : G) (E : Subgroup G) :
    derivedInG (MulAut.conj g • E) = MulAut.conj g • derivedInG E := by
  have e1 : derivedInG (MulAut.conj g • E) = ⁅MulAut.conj g • E, MulAut.conj g • E⁆ :=
    Subgroup.map_subtype_commutator _
  have e2 : MulAut.conj g • derivedInG E = ⁅MulAut.conj g • E, MulAut.conj g • E⁆ := by
    have he : derivedInG E = ⁅E, E⁆ := Subgroup.map_subtype_commutator E
    rw [he, Subgroup.pointwise_smul_def, Subgroup.map_commutator]
    rfl
  rw [e1, e2]

/-- **Lemma 13.6 step 2 (the WLOG).** With `X ≤ M_σ ⊓ C_G(E₁)` a `q`-subgroup, `q ∉ β(M)`, there is
a conjugate complement `F = E^{c⁻¹}` (`c ∈ C_{M_σ}(E₁)`, so its `τ₁`-Hall is again `E₁`) with
`X ≤ C_G(F')`. (S₀ = E₁-invariant Sylow `q ⊆ C(E')`; `X ⊆ S₁` an E₁-invariant Sylow; `1.5(c)`
conjugates `S₁` to `S₀` by `c ∈ C_{M_σ}(E₁)`; then `X = (X^c)^{c⁻¹} ⊆ (S₀)^{c⁻¹} ⊆ C(F')`.) -/
theorem exists_conjugate_complement_centralizing [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {q : ℕ} [Fact q.Prime]
    (hqβ : q ∉ S10.beta M) {X : Subgroup G} (hXq : IsPGroup q ↥X) (hXMσ : X ≤ S10.Msigma M)
    (hXE1 : X ≤ Subgroup.centralizer (E₁ : Set G)) :
    ∃ F F₂ F₃ : Subgroup G, SubgroupESetup M F E₁ F₂ F₃ ∧
      X ≤ Subgroup.centralizer (derivedInG F : Set G) := by
  classical
  have hMσM : S10.Msigma M ≤ M := S10.Msigma_le M
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups h.mem_maximal
  have hMσsolv : Group.IsSolvable ↥(S10.Msigma M) :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hMσM).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hMσM).surjective
  have hE1NMσ : E₁ ≤ Subgroup.normalizer ((S10.Msigma M : Subgroup G) : Set G) :=
    h.E1_le_M.trans (le_normalizer_opiCoreInG (S10.sigma M) M)
  have hcop_MσE : Nat.Coprime (Nat.card ↥(S10.Msigma M)) (Nat.card ↥E) := by
    have h1 := (S10.Msigma_subgroupOf_isHall hG h.mem_maximal).coprime_index
    rw [h.isComplement'_subgroupOf.symm.index_eq_card] at h1
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMσM).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E_le).toEquiv] at h1
  have hcop : Nat.Coprime (Nat.card ↥E₁) (Nat.card ↥(S10.Msigma M)) :=
    hcop_MσE.symm.coprime_dvd_left (Subgroup.card_dvd_of_le h.E₁_le)
  obtain ⟨S₀, hS₀Mσ, _hS₀q, hS₀inv, hS₀CE', hS₀card⟩ :=
    exists_E1inv_sylow_centralizing_derivedE hG h hqβ
  have hXNX : E₁ ≤ Subgroup.normalizer (X : Set G) :=
    (Subgroup.le_centralizer_iff.mp hXE1).trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨S₁, hS₁Mσ, _hS₁q, hS₁inv, hXS₁, hS₁card⟩ :=
    aInvariant_pSubgroup_le_aInvariant_sylow_subgroup hE1NMσ hcop (Or.inr hMσsolv) hXMσ hXq hXNX
  have hcardS₀ : Nat.card ↥(S₀.subgroupOf (S10.Msigma M))
      = q ^ (Nat.card ↥(S10.Msigma M)).factorization q := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS₀Mσ).toEquiv]; exact hS₀card
  have hcardS₁ : Nat.card ↥(S₁.subgroupOf (S10.Msigma M))
      = q ^ (Nat.card ↥(S10.Msigma M)).factorization q := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS₁Mσ).toEquiv]; exact hS₁card
  obtain ⟨c, hcMσ, hcCE1, hcConj⟩ := aInvariant_sylow_conj_subgroup hE1NMσ hcop (Or.inr hMσsolv)
    hS₁Mσ hcardS₁ hS₁inv hS₀Mσ hcardS₀ hS₀inv
  -- `F = conj c⁻¹ • E`; its `E₁`-slot is fixed since `c⁻¹ ∈ C(E₁) ≤ N(E₁)`.
  have hc1 : MulAut.conj c⁻¹ • E₁ = E₁ :=
    conj_smul_eq_self_of_mem_normalizer (Subgroup.centralizer_le_normalizer _ (inv_mem hcCE1))
  refine ⟨MulAut.conj c⁻¹ • E, MulAut.conj c⁻¹ • E₂, MulAut.conj c⁻¹ • E₃,
    hc1 ▸ SubgroupESetup.conj' h (inv_mem (hMσM hcMσ)), ?_⟩
  -- `X ≤ C(F')`.  `conj c • X ⊆ conj c • S₁ = S₀ ⊆ C(E')`, then conjugate back by `c⁻¹`.
  have hcXCE' : MulAut.conj c • X ≤ Subgroup.centralizer (derivedInG E : Set G) :=
    ((conj_smul_mono _ hXS₁).trans (le_of_eq hcConj)).trans hS₀CE'
  have hE'cX : derivedInG E ≤ Subgroup.centralizer ((MulAut.conj c • X : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.mp hcXCE'
  rw [smul_derivedInG_conj, Subgroup.le_centralizer_iff]
  -- `conj c⁻¹ • derivedInG E ≤ conj c⁻¹ • C(conj c • X) = C(X)`.
  calc MulAut.conj c⁻¹ • derivedInG E
      ≤ MulAut.conj c⁻¹ • Subgroup.centralizer ((MulAut.conj c • X : Subgroup G) : Set G) :=
        conj_smul_mono _ hE'cX
    _ = Subgroup.centralizer (X : Set G) := by
        rw [smul_centralizer_conj, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]

/-- **BG Lemma 13.6** (mmd L3574): `1⊂P⊆E₁`, `q∈σ(M)`, `X∈ℰ_q¹(C_{M_σ}(P))`, `S` を `M_σ` の
Sylow `q`-部分群とすると `ℳ(C_G(X))=ℳ(S)={M}`。 -/
theorem maximalContaining_eq_singleton_of_E1 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {q : ℕ} [Fact q.Prime]
    (hq : q ∈ S10.sigma M) {P : Subgroup G} (hPE1 : P ≤ E₁) (hPne : P ≠ ⊥)
    {X : Subgroup G} (hX : X ∈ elemAbelianOfRank G q 1)
    (hXC : X ≤ S10.Msigma M ⊓ Subgroup.centralizer (P : Set G))
    {S : Subgroup G} (hSle : S ≤ S10.Msigma M) (hSq : IsPGroup q ↥S)
    (hSmax : ∀ T : Subgroup G, T ≤ S10.Msigma M → IsPGroup q ↥T → S ≤ T → S = T) :
    maximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M} ∧
    maximalSubgroupsContaining S = {M} := by
  classical
  have hXMσ : X ≤ S10.Msigma M := hXC.trans inf_le_left
  have hXM : X ≤ M := hXMσ.trans (S10.Msigma_le M)
  by_cases hcase : q ∈ S10.beta M ∨ X ≤ derivedInG (S10.Msigma M)
  · -- **Reduction half** (BG L3608): Corollary 12.14 (faithful form) supplies both
    -- `ℳ(C_G(X)) = {M}`
    -- and `ℳ(S₀) = {M}` for its internal Sylow `S₀ ⊇ X`; the arbitrary `S` follows by conjugacy.
    obtain ⟨hCG, S₀, _hXS₀, hS₀Mσ, hS₀q, hS₀max, hMS₀⟩ :=
      Cor1214.maximalContaining_centralizer_and_someSylow_eq_singleton
        hG h.mem_maximal hq hX hXM hcase
    exact ⟨hCG, maximalContaining_eq_singleton_of_maximal_qsubgroup h.mem_maximal
      (S10.Msigma_le M) hSle hSq hSmax hS₀Mσ hS₀q hS₀max hMS₀⟩
  · -- **Contradiction half** (BG L3610-3624): `q ∉ β(M)` and `X ⊄ M_σ'` is impossible.
    -- Recipe (deps all pinned) = issue 8003. Steps: (1) `X ⊆ C_{M_σ}(E₁)` (Thm 13.5 prime action);
    -- (2) `X ⊆ C_{M_σ}(E')` (Lemma 12.19 `derivedE_centralizes_betaComplement` — the mmd's
    -- "Theorem 12.13" is a mis-citation — + Prop 1.5 coprime normalization); (3) `E₁E' ≠ E`
    -- (Lemma 12.17 `C_{M_σ}(E) ⊆ M_σ'`, `X ⊄ M_σ'`); (4) `E₂ ≠ 1` (`E₃ ⊆ E'`); (5) `A ∈ ℰ_p²(E)`
    -- with `A ◁ E` (Cor 12.6a) and `C_{M_σ}(A) = 1` (Thm 12.5d); (6) `A = A₀ × [A,E₁]` centralizes
    -- `X` (Thm 13.4 per-line via `E'`); (7) `X ≤ M_σ ⊓ C(A) = ⊥`, contra `X ≠ ⊥`.
    exfalso
    have hqβ : q ∉ S10.beta M := fun hh => hcase (Or.inl hh)
    have hXMσ' : ¬ X ≤ derivedInG (S10.Msigma M) := fun hh => hcase (Or.inr hh)
    have hXne : X ≠ ⊥ := ne_bot_of_mem_elemAbelianOfRank_one hX
    have hXq : IsPGroup q ↥X := (mem_elemAbelianOfRank.mp hX).1.isPGroup
    have hE1ne : E₁ ≠ ⊥ := fun hb => hPne (le_bot_iff.mp (hb ▸ hPE1))
    -- (1) `X ≤ M_σ ⊓ C_G(E₁)` (prime action: `C_{M_σ}(P) = C_{M_σ}(E₁)`).
    have hXmC : X ≤ S10.Msigma M ⊓ Subgroup.centralizer (E₁ : Set G) := by
      have hfix := fixedBy_eq_of_le_of_ne_bot (E1_actsPrime hG h hE1ne) hPE1 hPne
      rw [fixedBy_def, fixedBy_def] at hfix
      exact hfix ▸ hXC
    -- (2) replace `E` by a conjugate complement `F` (`F₁ = E₁`) with `X ≤ C_G(F')`.
    obtain ⟨F, F₂, F₃, hFsetup, hXF'⟩ :=
      exists_conjugate_complement_centralizing hG h hqβ hXq hXMσ (hXmC.trans inf_le_right)
    -- (3)(4) `F₂ ≠ 1`.
    have hF2ne := E2_ne_bot_of_centralizer hG hFsetup (hXmC.trans inf_le_left)
      (hXmC.trans inf_le_right) hXF' hXMσ'
    -- (5) `p ∈ τ₂(M)`, `A ∈ ℰ_p²(F)` with `A ◁ F` and `C_{M_σ}(A) = 1`.
    obtain ⟨p, hp_prime, hp_dvd⟩ :=
      Nat.exists_prime_and_dvd (fun hh => hF2ne (Subgroup.card_eq_one.mp hh))
    have : Fact p.Prime := ⟨hp_prime⟩
    have hpτ2 : p ∈ tau2 M :=
      hFsetup.isPiGroup_tau2 p (Nat.mem_primeFactors.mpr ⟨hp_prime, hp_dvd, Nat.card_pos.ne'⟩)
    obtain ⟨A, hA, hAF⟩ := exists_elemAb_rank_two_le_E_of_tau2 hG hFsetup hpτ2
    have hAnorm : F ≤ Subgroup.normalizer (A : Set G) :=
      (elemAb_normal_in_E_of_tau2 hG hFsetup hpτ2 hA hAF).1.1
    have hCA : S10.Msigma M ⊓ Subgroup.centralizer (A : Set G) = ⊥ :=
      (Msigma_nilpotent_of_tau2 hG hFsetup.mem_maximal hpτ2 hA (hAF.trans hFsetup.E_le)).2.2.2.1
    have hAelem : A.IsElementaryAbelian p := (mem_elemAbelianOfRank.mp hA).1
    -- (6) `A` centralizes `X`; (7) `X ≤ M_σ ⊓ C_G(A) = 1`, contradicting `X ≠ 1`.
    have hAX := centralizer_A_le_centralizer hG hFsetup hpτ2 hAF hAnorm hAelem hE1ne hXmC hXF'
    exact hXne (le_bot_iff.mp (hCA ▸ le_inf hXMσ (Subgroup.le_centralizer_iff.mp hAX)))

end OddOrder.BG.Ch3.S13


