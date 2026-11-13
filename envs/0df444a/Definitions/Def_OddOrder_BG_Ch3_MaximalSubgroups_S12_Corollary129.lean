-- Prove2me | Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_Corollary129
-- name    : OddOrder_BG_Ch3_MaximalSubgroups_S12_Corollary129
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T07:56:28.669208+00:00
-- url     : https://prove2.me/theorems/6dfe6079-bd2a-49ae-815d-ec923e1827e4
-- title:
--   BG §12: Corollary 12.9
-- statement:
--   Formalizes Corollary 12.9 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §12: for $p\in\tau_2(M)$, $A\in\mathcal{E}_p^2(E)$, $q\in\tau_1(M)$, $Q\in\mathcal{E}_q^1(E)$ with $C_{M_\sigma}(Q)=1$ and $[A,Q]\ne 1$, and with $A_0=[A,Q]$, $A_1=C_A(Q)$: (a) $A_0\in\mathcal{E}^1(A)$ and $A_0=C_A(M_\sigma)\trianglelefteq M$; (b) $A_0$ and $A_1$ are not conjugate in $G$; (c) $A_1\in\mathcal{E}^1(A)$ and $C_G(A_1)\not\subseteq M$.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 5 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch3_MaximalSubgroups/S12_Corollary129.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch3_MaximalSubgroups/S12_Corollary129.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_Theorem127d
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_Lemma128d

namespace OddOrder.BG.Ch3.S12

open OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- conj-smul は card を保つ。(`S10_HallStructure`/`S10_BetaRadical` の private 重複の
3 例目; hoist は hub 仕事。) -/
private theorem card_conj_smul (g : G) (H : Subgroup G) :
    Nat.card ↥(MulAut.conj g • H) = Nat.card ↥H :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

/-- conj-smul は単調。(12.10 でも使うため public。) -/
theorem conj_smul_mono (φ : MulAut G) {H K : Subgroup G} (h : H ≤ K) :
    φ • H ≤ φ • K := by
  rw [mulAut_smul_eq_map, mulAut_smul_eq_map]
  exact Subgroup.map_mono h

/-- `M.subtype` による像は `↥M` 内 conj-smul と `G` 内 conj-smul を交換する。 -/
private theorem map_subtype_conj_smul {M : Subgroup G} (m : ↥M) (H : Subgroup ↥M) :
    (MulAut.conj m • H).map M.subtype = MulAut.conj (m : G) • (H.map M.subtype) := by
  rw [mulAut_smul_eq_map, mulAut_smul_eq_map, Subgroup.map_map, Subgroup.map_map]
  congr 1

/-- 任意の `p`-部分群は指定した Sylow `p`-部分群の中へ共役で押し込める。
(`S09_Corollaries.exists_conj_le_sylow_of_isPGroup` (private) の再掲。) -/
private theorem exists_conj_le_sylow_of_isPGroup {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {Q : Subgroup G} (hQ : IsPGroup p Q) (P : Sylow p G) :
    ∃ g : G, ((MulAut.conj g) • Q : Subgroup G) ≤ (P : Subgroup G) := by
  classical
  obtain ⟨Q', hQQ'⟩ := hQ.exists_le_sylow
  have : MulAction.IsPretransitive G (Sylow p G) := Sylow.isPretransitive_of_finite
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q' P
  refine ⟨g, ?_⟩
  have hle : ((MulAut.conj g) • Q : Subgroup G) ≤
      ((MulAut.conj g) • (Q' : Subgroup G) : Subgroup G) :=
    (Subgroup.pointwise_smul_le_pointwise_smul_iff).mpr hQQ'
  have hQ'eq : ((MulAut.conj g) • (Q' : Subgroup G) : Subgroup G) = (P : Subgroup G) := by
    have := congrArg Sylow.toSubgroup hg
    rwa [Sylow.coe_subgroup_smul] at this
  exact hle.trans (le_of_eq hQ'eq)

/-- **BG Corollary 12.9** (mmd L3286): `p ∈ τ₂(M)`, `A ∈ ℰ_p²(E)`, `q ∈ τ₁(M)`,
`Q ∈ ℰ_q¹(E)`, `C_{M_σ}(Q)=1`, `[A,Q]≠1` のとき `A₀=[A,Q]`, `A₁=C_A(Q)` で
(a) `A₀ ∈ ℰ¹(A)` かつ `A₀=C_A(M_σ) ⊴ M`; (b) `A₀` は `A₁` と `G` 内で非共役; (c) `A₁ ∈ ℰ¹(A)` かつ
`C_G(A₁) ⊄ M`。 -/
theorem commutator_decomp_of_tau1_action [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hp : p ∈ tau2 M) (hq : q ∈ tau1 M)
    {A Q : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E)
    (hQ : Q ∈ elemAbelianOfRank G q 1) (hQE : Q ≤ E)
    (hCQ : S10.Msigma M ⊓ Subgroup.centralizer (Q : Set G) = ⊥) (hAQ : ⁅A, Q⁆ ≠ ⊥) :
    (⁅A, Q⁆ ∈ elemAbelianOfRank G p 1 ∧ ⁅A, Q⁆ ≤ A ∧
      ⁅A, Q⁆ = A ⊓ Subgroup.centralizer (S10.Msigma M : Set G) ∧
      M ≤ Subgroup.normalizer ((⁅A, Q⁆ : Subgroup G) : Set G)) ∧
    (¬ ∃ g : G, MulAut.conj g • (⁅A, Q⁆ : Subgroup G) = A ⊓ Subgroup.centralizer (Q : Set G)) ∧
    ((A ⊓ Subgroup.centralizer (Q : Set G)) ∈ elemAbelianOfRank G p 1 ∧
      (A ⊓ Subgroup.centralizer (Q : Set G)) ≤ A ∧
      ¬ (Subgroup.centralizer ((A ⊓ Subgroup.centralizer (Q : Set G)) : Set G) ≤ M)) := by
  classical
  have hM := h.mem_maximal
  have hA_le_M : A ≤ M := hAE.trans h.E_le
  have hQ_le_M : Q ≤ M := hQE.trans h.E_le
  have hQcard : Nat.card ↥Q = q := by rw [hQ.2, pow_one]
  -- `p ≠ q` (`r_p(M) = 2` vs `r_q(M) = 1`).
  have hp_ne_q : p ≠ q := by
    intro heq
    have h1 : pRank ↥M q = 2 := heq ▸ hp.2
    rw [hq.2.2] at h1
    exact absurd h1 (by norm_num)
  -- `E ≤ N_G(A)` (Corollary 12.6(a)).
  obtain ⟨⟨hE_norm_A, -⟩, -, -, -, -, -⟩ := elemAb_normal_in_E_of_tau2 hG h hp hA hAE
  -- Proposition 10.11(d) with `K := A`, `P := Q`:
  -- `[A,Q] ≤ C_G(M_σ)`, `[A,Q]` cyclic, `M ≤ N_G([A,Q])`.
  have hA_pi : Subgroup.IsPiSubgroup (S10.sigma M)ᶜ A :=
    Subgroup.isPiSubgroup_of_isPGroup_of_mem hA.1.isPGroup hp.1
  have hA_q' : Subgroup.IsPiSubgroup (({q} : Set ℕ)ᶜ) A := by
    intro r hr
    rw [hA.2] at hr
    obtain ⟨hr_prime, hr_dvd, -⟩ := Nat.mem_primeFactors.mp hr
    have hrp : r = p :=
      (Nat.prime_dvd_prime_iff_eq hr_prime Fact.out).mp (hr_prime.dvd_of_dvd_pow hr_dvd)
    simpa [hrp] using hp_ne_q
  have hA_comm : IsMulCommutative ↥A := ⟨⟨hA.1.comm⟩⟩
  obtain ⟨hA₀_cent, hA₀_cyc, hM_norm_A₀⟩ :=
    S10.sigma_complement_commutator_cyclic_normal hG hM hA_le_M hA_pi hq.1 hQ
      (le_inf (hQE.trans hE_norm_A) hQ_le_M) hCQ hA_comm hA_q'
  -- Coprime decomposition `A = (A ⊓ C_G(Q)) × [A,Q]`.
  have := hA_comm
  have hcop : Nat.Coprime (Nat.card ↥A) (Nat.card ↥Q) := by
    rw [hA.2, hQcard]
    exact Nat.Coprime.pow_left _ ((Nat.coprime_primes Fact.out Fact.out).mpr hp_ne_q)
  obtain ⟨hinf, hsup⟩ :=
    OddOrder.Isaacs.Ch05.fitting_coprime_abelian_decomp (P := A) (K := Q)
      (hQE.trans hE_norm_A) hcop
  -- Reorient: `A₁ := A ⊓ C_G(Q)`.
  rw [inf_comm (Subgroup.centralizer (Q : Set G)) A] at hinf hsup
  have hA₀_le_A : (⁅A, Q⁆ : Subgroup G) ≤ A := le_sup_right.trans hsup.le
  -- The rank-clash engine (Proposition 10.11(b)): no `ℰ_p²` inside `C_G(M_σ)`.
  have hrank_clash : ¬ A ≤ Subgroup.centralizer ((S10.Msigma M : Subgroup G) : Set G) := by
    intro hAC
    have h1011 := S10.rank_centralizer_Msigma_inf_le_one hG hM hA_le_M hA_pi
    rw [inf_eq_right.mpr hAC] at h1011
    have h2 := two_le_rank_of_mem_elemAbelianOfRank_two hA
    omega
  -- `card [A,Q] = p`.
  have hA₀_card : Nat.card ↥(⁅A, Q⁆ : Subgroup G) = p := by
    have hdvd : Nat.card ↥(⁅A, Q⁆ : Subgroup G) ∣ p ^ 2 :=
      hA.2 ▸ Subgroup.card_dvd_of_le hA₀_le_A
    obtain ⟨j, hj_le, hjcard⟩ := (Nat.dvd_prime_pow Fact.out).mp hdvd
    interval_cases j
    · exact absurd (Subgroup.card_eq_one.mp (by rw [hjcard, pow_zero])) hAQ
    · rw [hjcard, pow_one]
    · exfalso
      have hA₀_eq_A : (⁅A, Q⁆ : Subgroup G) = A :=
        Subgroup.eq_of_le_of_card_ge hA₀_le_A (by rw [hjcard, hA.2])
      exact hrank_clash (hA₀_eq_A ▸ hA₀_cent)
  -- (a) third conjunct: `[A,Q] = A ⊓ C_G(M_σ)`.
  have ha3 : (⁅A, Q⁆ : Subgroup G)
      = A ⊓ Subgroup.centralizer (S10.Msigma M : Set G) := by
    have hle : (⁅A, Q⁆ : Subgroup G)
        ≤ A ⊓ Subgroup.centralizer (S10.Msigma M : Set G) := le_inf hA₀_le_A hA₀_cent
    have hdvd : Nat.card ↥(A ⊓ Subgroup.centralizer (S10.Msigma M : Set G)) ∣ p ^ 2 :=
      hA.2 ▸ Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨j, hj_le, hjcard⟩ := (Nat.dvd_prime_pow Fact.out).mp hdvd
    interval_cases j
    · exfalso
      have hbot : A ⊓ Subgroup.centralizer (S10.Msigma M : Set G) = ⊥ :=
        Subgroup.card_eq_one.mp (by rw [hjcard, pow_zero])
      have : (⁅A, Q⁆ : Subgroup G) = ⊥ := le_bot_iff.mp (hbot ▸ hle)
      exact hAQ this
    · exact Subgroup.eq_of_le_of_card_ge hle (by rw [hjcard, pow_one, hA₀_card])
    · exfalso
      have hXA : A ⊓ Subgroup.centralizer (S10.Msigma M : Set G) = A :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hA.2, hjcard])
      exact hrank_clash (by rw [← hXA]; exact inf_le_right)
  -- (a) first conjunct: `[A,Q] ∈ ℰ¹`.
  have hA₀_mem : (⁅A, Q⁆ : Subgroup G) ∈ elemAbelianOfRank G p 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hA₀_card, by rw [hA₀_card, pow_one]⟩
  -- `card (A ⊓ C_G(Q)) = p` from `|A| = |A₁| · |A₀|`.
  have hA_le_CA₀ : A ≤ Subgroup.centralizer ((⁅A, Q⁆ : Subgroup G) : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hA₀_le_A))
    exact le_centralizer_self_of_isElementaryAbelian hA.1
  have hA₁_card : Nat.card ↥(A ⊓ Subgroup.centralizer (Q : Set G)) = p := by
    have hcard_eq : Nat.card ↥((A ⊓ Subgroup.centralizer (Q : Set G))
          ⊔ (⁅A, Q⁆ : Subgroup G))
        = Nat.card ↥(A ⊓ Subgroup.centralizer (Q : Set G))
          * Nat.card ↥(⁅A, Q⁆ : Subgroup G) :=
      card_sup_eq_mul_of_le_normalizer_of_disjoint
        ((inf_le_left.trans hA_le_CA₀).trans (Subgroup.centralizer_le_normalizer _)) hinf
    rw [hsup, hA.2, hA₀_card, pow_two] at hcard_eq
    exact Nat.eq_of_mul_eq_mul_right (Fact.out : p.Prime).pos hcard_eq.symm
  have hA₁_mem : (A ⊓ Subgroup.centralizer (Q : Set G)) ∈ elemAbelianOfRank G p 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hA₁_card, by rw [hA₁_card, pow_one]⟩
  -- (b): `A₀` is not conjugate to `A₁`.
  have hb : ¬ ∃ g : G, MulAut.conj g • (⁅A, Q⁆ : Subgroup G)
      = A ⊓ Subgroup.centralizer (Q : Set G) := by
    rintro ⟨g, hg⟩
    -- `Q ≤ C_G(A₁) = conj g • C_G(A₀)`.
    have hQ_le_CA₁ : Q ≤ Subgroup.centralizer
        ((A ⊓ Subgroup.centralizer (Q : Set G) : Subgroup G) : Set G) :=
      le_centralizer_swap inf_le_right
    rw [← hg, ← centralizer_conj_smul] at hQ_le_CA₁
    -- `Q' := conj g⁻¹ • Q ≤ C_G(A₀)`.
    have hQ'_le_C : MulAut.conj g⁻¹ • Q
        ≤ Subgroup.centralizer ((⁅A, Q⁆ : Subgroup G) : Set G) := by
      have h1 := conj_smul_mono (MulAut.conj g⁻¹) hQ_le_CA₁
      rwa [smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul] at h1
    -- `N_G(A₀) = M`, hence `C_G(A₀) ≤ M` and `C_G(A₀)` is `M`-conj-invariant.
    have hA₀_le_M : (⁅A, Q⁆ : Subgroup G) ≤ M := hA₀_le_A.trans hA_le_M
    have hN_eq : Subgroup.normalizer ((⁅A, Q⁆ : Subgroup G) : Set G) = M := by
      by_contra hne
      have hlt : M < Subgroup.normalizer ((⁅A, Q⁆ : Subgroup G) : Set G) :=
        lt_of_le_of_ne hM_norm_A₀ (Ne.symm hne)
      exact absurd (hM.2 _ hlt)
        (normalizer_lt_top_of_le_of_ne_bot hG hM hA₀_le_M hAQ).ne
    have hC_le_M : Subgroup.centralizer ((⁅A, Q⁆ : Subgroup G) : Set G) ≤ M :=
      (Subgroup.centralizer_le_normalizer _).trans hN_eq.le
    have hC_inv : ∀ m : G, m ∈ M →
        MulAut.conj m • Subgroup.centralizer ((⁅A, Q⁆ : Subgroup G) : Set G)
          = Subgroup.centralizer ((⁅A, Q⁆ : Subgroup G) : Set G) := by
      intro m hm
      rw [centralizer_conj_smul, conj_smul_eq_self_of_mem_normalizer (hM_norm_A₀ hm)]
    -- Set up the two order-`q` subgroups of `M`.
    set Q' : Subgroup G := MulAut.conj g⁻¹ • Q with hQ'def
    have hQ'_card : Nat.card ↥Q' = q := by rw [hQ'def, card_conj_smul, hQcard]
    have hQ'_le_M : Q' ≤ M := hQ'_le_C.trans hC_le_M
    have hQ'_pg : IsPGroup q ↥Q' := by
      rw [hQ'def, mulAut_smul_eq_map]
      exact hQ.1.isPGroup.map _
    -- A Sylow `q`-subgroup of `M` (taken inside `↥M`) containing `Q`.
    obtain ⟨S₁, hS₁⟩ := hQ.1.isPGroup.comap_subtype.exists_le_sylow (G := M)
    -- Conjugate `Q'` (inside `↥M`) into `S₁`.
    obtain ⟨m, hm⟩ := exists_conj_le_sylow_of_isPGroup hQ'_pg.comap_subtype S₁
    -- `G`-level Sylow.
    set SylG : Subgroup G := (S₁ : Subgroup ↥M).map M.subtype with hSylGdef
    have hSylG_le_M : SylG ≤ M := Subgroup.map_subtype_le _
    have hSylG_pg : IsPGroup q ↥SylG := S₁.isPGroup'.map _
    have hQ_le_SylG : Q ≤ SylG := by
      rw [hSylGdef, ← Subgroup.map_subgroupOf_eq_of_le hQ_le_M]
      exact Subgroup.map_mono hS₁
    have hQ'm_le : MulAut.conj ((m : G)) • Q' ≤ SylG := by
      have h1 : (MulAut.conj m • Q'.subgroupOf M).map M.subtype ≤ SylG :=
        Subgroup.map_mono hm
      rwa [map_subtype_conj_smul, Subgroup.map_subgroupOf_eq_of_le hQ'_le_M] at h1
    -- `SylG` is cyclic (`r_q(M) = 1`, `q` odd).
    have hodd_q : Odd q := by
      refine hG.odd.of_dvd_nat (dvd_trans ?_ (Subgroup.card_subgroup_dvd_card M))
      rw [← hQcard]
      exact Subgroup.card_dvd_of_le hQ_le_M
    have hSylG_rank : pRank ↥SylG q ≤ 1 := by
      have h1 : pRank ↥SylG q ≤ pRank ↥M q :=
        pRank_le_of_injective (f := Subgroup.inclusion hSylG_le_M)
          (Subgroup.inclusion_injective _)
      rwa [hq.2.2] at h1
    have : IsCyclic ↥SylG := S10.isCyclic_of_pRank_le_one hSylG_pg hodd_q hSylG_rank
    -- Uniqueness of order-`q` subgroups in the cyclic `SylG`: `Q = conj m • Q'`.
    have hkey : Q.subgroupOf SylG = (MulAut.conj ((m : G)) • Q').subgroupOf SylG := by
      apply OddOrder.GroupTheory.cyclic_subgroup_eq_of_card_eq
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ_le_SylG).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ'm_le).toEquiv,
        hQcard, card_conj_smul, hQ'_card]
    have hQ_eq : Q = MulAut.conj ((m : G)) • Q' := by
      have h2 := congrArg (Subgroup.map SylG.subtype) hkey
      rwa [Subgroup.map_subgroupOf_eq_of_le hQ_le_SylG,
        Subgroup.map_subgroupOf_eq_of_le hQ'm_le] at h2
    -- Transport `Q' ≤ C_G(A₀)` along `conj m` (`m ∈ M`): `Q ≤ C_G(A₀)`.
    have hQ_le_C : Q ≤ Subgroup.centralizer ((⁅A, Q⁆ : Subgroup G) : Set G) := by
      conv_lhs => rw [hQ_eq]
      rw [← hC_inv (m : G) m.2]
      exact conj_smul_mono _ hQ'_le_C
    -- `A₀ ≤ A₁`, contradicting `A₁ ⊓ A₀ = ⊥` and `card A₀ = p`.
    have hA₀_le_A₁ : (⁅A, Q⁆ : Subgroup G) ≤ A ⊓ Subgroup.centralizer (Q : Set G) :=
      le_inf hA₀_le_A (le_centralizer_swap hQ_le_C)
    have hbot : (⁅A, Q⁆ : Subgroup G) = ⊥ :=
      le_bot_iff.mp (hinf ▸ le_inf hA₀_le_A₁ le_rfl)
    exact hAQ hbot
  -- (c) third conjunct: `C_G(A₁) ⊄ M`.
  have hc3 : ¬ (Subgroup.centralizer
      ((A ⊓ Subgroup.centralizer (Q : Set G) : Subgroup G) : Set G) ≤ M) := by
    by_cases hnonab : ∃ S : Sylow p G, ¬ IsMulCommutative ↥(S : Subgroup G)
    · -- Nonabelian Sylow `p`: Theorem 12.7(c).
      obtain ⟨-, A₀', hA₀'eq, -, -, hc, -⟩ :=
        tau2_singleton_of_nonabelianSylow hG h hp hA hAE hnonab
      have hA₁_ne : A ⊓ Subgroup.centralizer (Q : Set G) ≠ A₀' := by
        rw [hA₀'eq, ← ha3]
        intro heq
        have hle : (⁅A, Q⁆ : Subgroup G) ≤ (⊥ : Subgroup G) := by
          rw [← hinf]
          exact le_inf heq.ge le_rfl
        exact hAQ (le_bot_iff.mp hle)
      exact (hc _ hA₁_mem (inf_le_left.trans hAE) hA₁_ne).2
    · -- Abelian Sylow `p`: Lemma 12.8(e) forces `[A,Q] = 1`, contradiction.
      push Not at hnonab
      exfalso
      have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
      have : Group.IsSolvable ↥E :=
        Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective h.E_le)
      -- `M ≤ N_G(M_σ)`.
      have hM_norm_Mσ : M ≤ Subgroup.normalizer ((S10.Msigma M) : Set G) := by
        rw [S10.Msigma, OddOrder.GroupTheory.opiCoreInG]
        have hle := Subgroup.le_normalizer_map
          (H := Ch03.oPiCore (S10.sigma M) ↥M) M.subtype
        rwa [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map,
          Subgroup.range_subtype] at hle
      -- Push `Q` into a Hall `τ₁`-subgroup of `E`, then conjugate onto `E₁`.
      have hQE_pi : Ch03.Subgroup.IsPiGroup (tau1 M) (Q.subgroupOf E) := by
        intro r hr
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQE).toEquiv, hQcard] at hr
        obtain ⟨hr_prime, hr_dvd, -⟩ := Nat.mem_primeFactors.mp hr
        rwa [(Nat.prime_dvd_prime_iff_eq hr_prime Fact.out).mp hr_dvd]
      obtain ⟨H, hH_hall, -, hQ_le_H⟩ :=
        Ch1.S01.aInvariant_piSubgroup_le_aInvariant_hall
          (A := Unit) (φ := (1 : Unit →* MulAut ↥E))
          (by rw [Nat.card_unique]; exact Nat.coprime_one_left _)
          hQE_pi (fun _ => one_smul _ _)
      set HG : Subgroup G := H.map E.subtype with hHGdef
      have hHG_le_E : HG ≤ E := Subgroup.map_subtype_le _
      have hHG_hall : Ch03.IsHallSubgroup (tau1 M) (HG.subgroupOf E) := by
        rwa [hHGdef, Subgroup.subgroupOf,
          Subgroup.comap_map_eq_self_of_injective E.subtype_injective]
      obtain ⟨w, hwE, hw⟩ :=
        Ch1.S06.exists_conj_eq_of_isHall_subgroupOf inferInstance hHG_le_E h.E₁_le
          hHG_hall h.E₁_hall
      set X : Subgroup G := MulAut.conj w • Q with hXdef
      have hQ_le_HG : Q ≤ HG := by
        rw [hHGdef, ← Subgroup.map_subgroupOf_eq_of_le hQE]
        exact Subgroup.map_mono hQ_le_H
      have hX_le_E₁ : X ≤ E₁ := by
        rw [hXdef, ← hw]
        exact conj_smul_mono _ hQ_le_HG
      have hX_mem : X ∈ elemAbelianOfRank G q 1 := by
        refine ⟨?_, by rw [hXdef, card_conj_smul, hQ.2]⟩
        rw [hXdef, mulAut_smul_eq_map]
        exact hQ.1.map (MulAut.conj w).injective
      have hwM : w ∈ M := h.E_le hwE
      -- `M_σ ⊓ C_G(X) = ⊥` by conjugating `hCQ`.
      have hMσCX : S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) = ⊥ := by
        rw [eq_bot_iff]
        rintro x ⟨hx1, hx2⟩
        have hx1' : w⁻¹ * x * w ∈ S10.Msigma M := by
          have h1 := (Subgroup.mem_normalizer_iff.mp
            (hM_norm_Mσ (M.inv_mem hwM)) x).mp hx1
          simpa using h1
        have hx2' : w⁻¹ * x * w ∈ Subgroup.centralizer (Q : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro u hu
          have huX : w * u * w⁻¹ ∈ X := by
            rw [hXdef, mulAut_smul_eq_map]
            exact ⟨u, hu, by simp [MulAut.conj_apply]⟩
          have hxu := Subgroup.mem_centralizer_iff.mp hx2 _ huX
          -- `(w u w⁻¹) x = x (w u w⁻¹)` ⟹ `u (w⁻¹ x w) = (w⁻¹ x w) u`
          have h2 := congrArg (fun z => w⁻¹ * z * w) hxu
          simpa [mul_assoc] using h2
        have : w⁻¹ * x * w ∈ (⊥ : Subgroup G) := hCQ ▸ ⟨hx1', hx2'⟩
        rw [Subgroup.mem_bot] at this
        have hx_eq : x = 1 := by
          have := congrArg (fun z => w * z * w⁻¹) this
          simpa [mul_assoc] using this
        simp [hx_eq]
      -- Apply Lemma 12.8(e) and derive `[A,Q] = 1`.
      obtain ⟨S₀, hAS₀⟩ := hA.1.isPGroup.exists_le_sylow
      obtain ⟨-, hE_cent⟩ :=
        central_line_of_abelianSylow hG h hp hA hAE hAS₀ (hnonab S₀) X
          ⟨q, Fact.out, hX_mem⟩ hX_le_E₁ hMσCX
      have hbot : (⁅A, X⁆ : Subgroup G) = ⊥ :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hAE.trans hE_cent)
      have hconj_comm : MulAut.conj w • (⁅A, Q⁆ : Subgroup G) = ⁅A, X⁆ := by
        rw [hXdef, mulAut_smul_eq_map, Subgroup.map_commutator]
        congr 1
        rw [← mulAut_smul_eq_map, conj_smul_eq_self_of_mem_normalizer (hE_norm_A hwE)]
      rw [hbot] at hconj_comm
      have hAQ_bot : (⁅A, Q⁆ : Subgroup G) = ⊥ := by
        have h2 := congrArg (fun K => MulAut.conj w⁻¹ • K) hconj_comm
        rwa [map_inv, inv_smul_smul, mulAut_smul_eq_map, Subgroup.map_bot] at h2
      exact hAQ hAQ_bot
  exact ⟨⟨hA₀_mem, hA₀_le_A, ha3, hM_norm_A₀⟩, hb, hA₁_mem, inf_le_left, hc3⟩

end OddOrder.BG.Ch3.S12


