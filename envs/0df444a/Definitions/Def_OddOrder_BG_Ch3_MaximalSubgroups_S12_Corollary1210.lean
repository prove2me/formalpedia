-- Prove2me | Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_Corollary1210
-- name    : OddOrder_BG_Ch3_MaximalSubgroups_S12_Corollary1210
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T07:58:07.003463+00:00
-- url     : https://prove2.me/theorems/fe3e1f4f-77d5-4b5b-a462-e866cd0e6786
-- title:
--   BG §12: Corollary 12.10
-- statement:
--   Formalizes Corollary 12.10 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §12: (a) every nilpotent $\sigma(M)'$-subgroup of $M$ is abelian; (b) $E_2$ and $E'$ are abelian; (c) for $p\in\tau_2(M)$, $A\in\mathcal{E}_p^2(E)$, $E_2E_3\subseteq C_E(A)\trianglelefteq E$ and $\pi(E/C_E(A))\subseteq\tau_1(M)$; (d) for $p\in\sigma(M)$ and a noncyclic $p$-subgroup $P$ of $M$, $N_G(P)\subseteq M$; (e) a condition giving $\mathcal{M}(C_G(x))=\{M\}$.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 4 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch3_MaximalSubgroups/S12_Corollary1210.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch3_MaximalSubgroups/S12_Corollary1210.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_Corollary129

namespace OddOrder.BG.Ch3.S12

open OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped commutatorElement

variable {G : Type*} [Group G]

/-- 有限 nilpotent 群は Sylow 直積なので、全 Sylow が abelian なら全体も abelian。 -/
theorem isMulCommutative_of_isNilpotent_of_forall_sylow {H : Type*} [Group H] [Finite H]
    (hnil : Group.IsNilpotent H)
    (hab : ∀ (q : ℕ), q.Prime → ∀ S : Sylow q H, IsMulCommutative ↥(S : Subgroup H)) :
    IsMulCommutative H := by
  classical
  obtain ⟨e⟩ := ((Group.isNilpotent_of_finite_tfae (G := H)).out 0 4).mp hnil
  refine S11.isMulCommutative_of_mulEquiv e ⟨⟨fun x y => ?_⟩⟩
  funext q P
  exact (hab q (Nat.prime_of_mem_primeFactors q.2) P).is_comm.comm (x q P) (y q P)

/-- **Cor 12.10 の鍵** (mmd L3309 "By Lemma 12.1(d) and Theorem 12.5(b), `M` has abelian
Sylow `p`-subgroups for every prime `p ∈ τ₁(M) ∪ τ₂(M) ∪ τ₃(M)`"): `r ∉ σ(M)` で
`r ∣ |M|` なら `M` の Sylow `r`-部分群は abelian。`τ₁ ∪ τ₃` では `r_r(M) = 1` から
cyclic、`τ₂` では Theorem 12.5(b)。 -/
theorem sylow_isMulCommutative_of_sigma_compl [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {r : ℕ} [Fact r.Prime]
    (hr_dvd : r ∣ Nat.card ↥M) (hrσ : r ∉ S10.sigma M) (S : Sylow r ↥M) :
    IsMulCommutative ↥(S : Subgroup ↥M) := by
  classical
  -- `r ∈ π(E)`: `|M| = |M_σ| · |E|` and `π(M_σ) ⊆ σ(M)`.
  have hrE : r ∈ (Nat.card ↥E).primeFactors := by
    refine Nat.mem_primeFactors.mpr ⟨Fact.out, ?_, Nat.card_pos.ne'⟩
    have hcard := card_Msigma_mul_card_E h
    have hrMσ : ¬ r ∣ Nat.card ↥(S10.Msigma M) := by
      intro hdvd
      have hhall := (S10.isHall_Msigma_Malpha hG h.mem_maximal).1
      exact hrσ (hhall.1 r (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩))
    rcases (Nat.Prime.dvd_mul Fact.out).mp (hcard ▸ hr_dvd) with h1 | h1
    · exact absurd h1 hrMσ
    · exact h1
  rcases SubgroupESetup.mem_tau_union_of_mem_primeFactors hG h hrE with (hr1 | hr2) | hr3
  · -- `r ∈ τ₁`: rank 1, cyclic Sylow.
    have hodd : Odd r := hG.odd.of_dvd_nat (hr_dvd.trans (Subgroup.card_subgroup_dvd_card M))
    have : IsCyclic ↥(S : Subgroup ↥M) :=
      S10.isCyclic_of_pRank_le_one S.isPGroup' hodd (le_of_eq ((pRank_sylow_eq S).trans hr1.2.2))
    let : CommGroup ↥(S : Subgroup ↥M) := IsCyclic.commGroup
    exact ⟨⟨mul_comm⟩⟩
  · -- `r ∈ τ₂`: Theorem 12.5(b).
    obtain ⟨A, hA, hAE⟩ := exists_elemAb_rank_two_le_E_of_tau2 hG h hr2
    exact (Msigma_nilpotent_of_tau2 hG h.mem_maximal hr2 hA (hAE.trans h.E_le)).2.1.1 S
  · -- `r ∈ τ₃`: rank 1, cyclic Sylow.
    have hodd : Odd r := hG.odd.of_dvd_nat (hr_dvd.trans (Subgroup.card_subgroup_dvd_card M))
    have : IsCyclic ↥(S : Subgroup ↥M) :=
      S10.isCyclic_of_pRank_le_one S.isPGroup' hodd (le_of_eq ((pRank_sylow_eq S).trans hr3.2.2))
    let : CommGroup ↥(S : Subgroup ↥M) := IsCyclic.commGroup
    exact ⟨⟨mul_comm⟩⟩

/-- conj-smul は singleton centralizer と交換する: `(C_G(x))^g = C_G(gxg⁻¹)`。 -/
private theorem centralizer_singleton_conj_smul (g x : G) :
    MulAut.conj g • Subgroup.centralizer ({x} : Set G)
      = Subgroup.centralizer ({g * x * g⁻¹} : Set G) := by
  ext z
  rw [mulAut_smul_eq_map, Subgroup.mem_map]
  constructor
  · rintro ⟨z₀, hz₀, rfl⟩
    have hcomm := Subgroup.mem_centralizer_iff.mp hz₀ x rfl
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    rw [Set.mem_singleton_iff] at hu
    rw [hu]
    have happ : (MulAut.conj g).toMonoidHom z₀ = g * z₀ * g⁻¹ := rfl
    rw [happ]
    have h1 : g * x * g⁻¹ * (g * z₀ * g⁻¹) = g * (x * z₀) * g⁻¹ := by group
    have h2 : g * z₀ * g⁻¹ * (g * x * g⁻¹) = g * (z₀ * x) * g⁻¹ := by group
    rw [h1, h2, hcomm]
  · intro hz
    have hcomm := Subgroup.mem_centralizer_iff.mp hz (g * x * g⁻¹) rfl
    refine ⟨g⁻¹ * z * g, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro u hu
      rw [Set.mem_singleton_iff] at hu
      rw [hu]
      have h1 : x * (g⁻¹ * z * g) = g⁻¹ * ((g * x * g⁻¹) * z) * g := by group
      have h2 : (g⁻¹ * z * g) * x = g⁻¹ * (z * (g * x * g⁻¹)) * g := by group
      rw [h1, h2, hcomm]
    · have happ : (MulAut.conj g).toMonoidHom (g⁻¹ * z * g)
          = g * (g⁻¹ * z * g) * g⁻¹ := rfl
      rw [happ]
      group

/-- **BG Corollary 12.10** (mmd L3294): (a) `M` の nilpotent `σ(M)'`-部分群は abelian;
(b) `E₂` と `E'` は abelian; (c) `p ∈ τ₂(M)`, `A ∈ ℰ_p²(E)` で `E₂E₃ ⊆ C_E(A) ⊴ E` かつ
`π(E/C_E(A)) ⊆ τ₁(M)`; (d) `p ∈ σ(M)`, `P` noncyclic `p`-部分群 ⇒ `N_G(P) ⊆ M`;
(e) `x ∈ M#`, `π(⟨x⟩) ⊆ τ₂(M)`, `C_{M_σ}(x)≠1` ⇒ `ℳ(C_G(x))={M}`。

(c) の `p` には素数性を明示する (scaffold からの faithful 化: BG の `τ₂(M)` は素数集合
だが、repo の `tau2` は `pRank` 条件のみで合成数を排除しないため)。 -/
theorem nilpotent_sigmaComplement_abelian [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) :
    (∀ N : Subgroup G, N ≤ M → Subgroup.IsPiSubgroup ((S10.sigma M)ᶜ) N →
      Group.IsNilpotent ↥N → IsMulCommutative ↥N) ∧
    (IsMulCommutative ↥E₂ ∧ IsMulCommutative ↥(derivedInG E)) ∧
    (∀ p : ℕ, p.Prime → p ∈ tau2 M → ∀ A ∈ elemAbelianOfRank G p 2, A ≤ E →
      E₂ ⊔ E₃ ≤ E ⊓ Subgroup.centralizer (A : Set G) ∧
      E ≤ Subgroup.normalizer ((E ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) : Set G) ∧
      ∀ r ∈ (((E ⊓ Subgroup.centralizer (A : Set G)).subgroupOf E).index).primeFactors,
        r ∈ tau1 M) ∧
    (∀ p : ℕ, p ∈ S10.sigma M → ∀ P : Subgroup G, P ≤ M → IsPGroup p ↥P →
      ¬ IsCyclic ↥P → Subgroup.normalizer (P : Set G) ≤ M) ∧
    (∀ x ∈ M, x ≠ 1 → (∀ r ∈ (orderOf x).primeFactors, r ∈ tau2 M) →
      S10.Msigma M ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ →
      maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) = {M}) := by
  classical
  have hM := h.mem_maximal
  -- (a)
  have ha : ∀ N : Subgroup G, N ≤ M → Subgroup.IsPiSubgroup ((S10.sigma M)ᶜ) N →
      Group.IsNilpotent ↥N → IsMulCommutative ↥N := by
    intro N hNM hNpi hNnil
    refine isMulCommutative_of_isNilpotent_of_forall_sylow hNnil ?_
    intro q hq_prime S
    have : Fact q.Prime := ⟨hq_prime⟩
    by_cases hSbot : (S : Subgroup ↥N) = ⊥
    · refine ⟨⟨fun a b => ?_⟩⟩
      have : Subsingleton ↥(S : Subgroup ↥N) := by
        rw [hSbot]
        exact ⟨fun a b => Subtype.ext (by
          rw [Subgroup.mem_bot.mp a.2, Subgroup.mem_bot.mp b.2])⟩
      exact Subsingleton.elim _ _
    · -- `q ∣ |N|`, hence `q ∉ σ(M)`.
      have hq_dvd_S : q ∣ Nat.card ↥(S : Subgroup ↥N) := by
        obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp S.isPGroup'
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · exact absurd (Subgroup.card_eq_one.mp (by rw [hn, h0, pow_zero])) hSbot
        · rw [hn]; exact dvd_pow_self q hpos.ne'
      have hq_dvd_N : q ∣ Nat.card ↥N :=
        hq_dvd_S.trans (Subgroup.card_subgroup_dvd_card _)
      have hqσ : q ∉ S10.sigma M :=
        hNpi q (Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd_N, Nat.card_pos.ne'⟩)
      -- transport the Sylow to `G` level, then into a Sylow of `M`.
      set SG : Subgroup G := ((S : Subgroup ↥N)).map N.subtype with hSGdef
      have hSG_le_M : SG ≤ M := (Subgroup.map_subtype_le _).trans hNM
      have hSG_pg : IsPGroup q ↥SG := S.isPGroup'.map _
      obtain ⟨T, hT⟩ := hSG_pg.comap_subtype.exists_le_sylow (G := M)
      have hT_ab := sylow_isMulCommutative_of_sigma_compl hG h
        (hq_dvd_N.trans (Subgroup.card_dvd_of_le hNM)) hqσ T
      have h1 : IsMulCommutative ↥(SG.subgroupOf M) :=
        isMulCommutative_of_le (G := ↥M) hT_ab hT
      have h2 : IsMulCommutative ↥SG :=
        S11.isMulCommutative_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hSG_le_M) h1
      exact S11.isMulCommutative_of_mulEquiv
        (Subgroup.equivMapOfInjective _ _ N.subtype_injective).symm h2
  -- (b) `E₂` abelian.
  have hbE₂ : IsMulCommutative ↥E₂ := by
    by_cases hτ₂ : ∃ p' : ℕ, p'.Prime ∧ p' ∈ tau2 M
    · obtain ⟨p', hp'_prime, hp'⟩ := hτ₂
      have : Fact p'.Prime := ⟨hp'_prime⟩
      obtain ⟨A', hA', hA'E⟩ := exists_elemAb_rank_two_le_E_of_tau2 hG h hp'
      by_cases hnonab : ∃ S : Sylow p' G, ¬ IsMulCommutative ↥(S : Subgroup G)
      · exact E2_isMulCommutative_of_prime_eq hG h hp' hA' (hA'E.trans h.E_le)
          (fun q hq hq2 => tau2_prime_eq_of_nonabelianSylow hG h hp' hA' hA'E hnonab hq hq2)
      · push Not at hnonab
        obtain ⟨S₀, hAS₀⟩ := hA'.1.isPGroup.exists_le_sylow
        exact (E2_abelian_normal_hall_of_abelianSylow hG h hp' hA' hA'E (hnonab S₀)).1.1
    · -- `τ₂` empty on primes: `E₂` is trivial.
      have hcard : Nat.card ↥E₂ = 1 := by
        by_contra h1
        obtain ⟨r, hr_prime, hr_dvd⟩ := Nat.exists_prime_and_dvd h1
        have hr_dvd' : r ∣ Nat.card ↥(E₂.subgroupOf E) := by
          rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₂_le).toEquiv]
        exact hτ₂ ⟨r, hr_prime, h.E₂_hall.1 r
          (Nat.mem_primeFactors.mpr ⟨hr_prime, hr_dvd', Nat.card_pos.ne'⟩)⟩
      refine ⟨⟨fun a b => ?_⟩⟩
      have : Subsingleton ↥E₂ := Nat.card_eq_one_iff_unique.mp hcard |>.1
      exact Subsingleton.elim _ _
  -- (b) `E'` abelian: nilpotent (12.1(a)) + (a).
  have hbE' : IsMulCommutative ↥(derivedInG E) := by
    refine ha _ ((Subgroup.map_subtype_le _).trans h.E_le) ?_ (h.derived_isNilpotent hG)
    intro r hr
    have hr_dvd_E : r ∣ Nat.card ↥E :=
      (Nat.mem_primeFactors.mp hr).2.1.trans
        (Subgroup.card_dvd_of_le (Subgroup.map_subtype_le _))
    exact h.not_mem_sigma_of_mem_primeFactors hG
      (Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hr).1, hr_dvd_E, Nat.card_pos.ne'⟩)
  -- 共通部品: `A ∈ ℰ_p²(E)` は `E₂` に入る (normal `τ₂`-subgroup ≤ Hall `τ₂`)。
  have hA_le_E₂_gen : ∀ (p : ℕ), p.Prime → p ∈ tau2 M →
      ∀ A ∈ elemAbelianOfRank G p 2, A ≤ E → A ≤ E₂ := by
    intro p hp_prime hp A hA hAE
    have : Fact p.Prime := ⟨hp_prime⟩
    obtain ⟨⟨hE_norm_A, -⟩, -, -, -, -, -⟩ := elemAb_normal_in_E_of_tau2 hG h hp hA hAE
    have hnormal : (A.subgroupOf E).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hAE).mpr hE_norm_A
    have hpi : Ch03.Subgroup.IsPiGroup (tau2 M) (A.subgroupOf E) := by
      intro r hr
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAE).toEquiv, hA.2] at hr
      obtain ⟨hr_prime, hr_dvd, -⟩ := Nat.mem_primeFactors.mp hr
      rwa [(Nat.prime_dvd_prime_iff_eq hr_prime hp_prime).mp
        (hr_prime.dvd_of_dvd_pow hr_dvd)]
    have hle := hpi.normal_le_hall h.E₂_hall
    intro a ha
    have h1 : (⟨a, hAE ha⟩ : ↥E) ∈ A.subgroupOf E := by
      rwa [Subgroup.mem_subgroupOf]
    have h2 := hle h1
    rwa [Subgroup.mem_subgroupOf] at h2
  refine ⟨ha, ⟨hbE₂, hbE'⟩, ?_, ?_, ?_⟩
  · -- (c)
    intro p hp_prime hp A hA hAE
    have : Fact p.Prime := ⟨hp_prime⟩
    obtain ⟨⟨hE_norm_A, -⟩, -, -, -, -, -⟩ := elemAb_normal_in_E_of_tau2 hG h hp hA hAE
    have hA_le_E₂ : A ≤ E₂ := hA_le_E₂_gen p hp_prime hp A hA hAE
    have hE₂_le_CA : E₂ ≤ Subgroup.centralizer (A : Set G) :=
      le_centralizer_of_le_of_le hbE₂ le_rfl hA_le_E₂
    have hE₃_le_CA : E₃ ≤ Subgroup.centralizer (A : Set G) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
      have h1 : (⁅E₃, A⁆ : Subgroup G) ≤ E₃ ⊓ A := by
        rw [Subgroup.commutator_le]
        intro a ha b hb
        refine ⟨?_, ?_⟩
        · have h2 : b * a⁻¹ * b⁻¹ ∈ E₃ :=
            (Subgroup.mem_normalizer_iff.mp (h.E3_normal hG (hAE hb)) a⁻¹).mp
              (E₃.inv_mem ha)
          have h4 : ⁅a, b⁆ = a * (b * a⁻¹ * b⁻¹) := by
            rw [commutatorElement_def]; group
          rw [h4]
          exact E₃.mul_mem ha h2
        · have h2 : a * b * a⁻¹ ∈ A :=
            (Subgroup.mem_normalizer_iff.mp (hE_norm_A (h.E₃_le ha)) b).mp hb
          have h4 : ⁅a, b⁆ = (a * b * a⁻¹) * b⁻¹ := by
            rw [commutatorElement_def]
          rw [h4]
          exact A.mul_mem h2 (A.inv_mem hb)
      refine le_bot_iff.mp (h1.trans (le_of_eq ?_))
      refine (Subgroup.disjoint_of_coprime_natCard (coprime_of_forall_prime_not_dvd ?_)).eq_bot
      intro r hr_prime hr_E₃ hr_A
      have hr3 : r ∈ tau3 M := by
        apply h.E₃_hall.1 r
        refine Nat.mem_primeFactors.mpr ⟨hr_prime, ?_, Nat.card_pos.ne'⟩
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₃_le).toEquiv]
      have hrp : r = p := by
        rw [hA.2] at hr_A
        exact (Nat.prime_dvd_prime_iff_eq hr_prime hp_prime).mp
          (hr_prime.dvd_of_dvd_pow hr_A)
      rw [hrp] at hr3
      have h21 := hp.2
      have h22 := hr3.2.2
      omega
    refine ⟨le_inf (sup_le h.E₂_le h.E₃_le) (sup_le hE₂_le_CA hE₃_le_CA), ?_, ?_⟩
    · -- `C_E(A) ⊴ E`.
      intro e he
      refine mem_normalizer_of_conj_smul_eq_self ?_
      rw [Subgroup.smul_inf, centralizer_conj_smul,
        conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer he),
        conj_smul_eq_self_of_mem_normalizer (hE_norm_A he)]
    · -- `π(E/C_E(A)) ⊆ τ₁(M)`.
      intro r hr
      have hr_prime : r.Prime := Nat.prime_of_mem_primeFactors hr
      have hr_dvd_index : r ∣ ((E ⊓ Subgroup.centralizer (A : Set G)).subgroupOf E).index :=
        (Nat.mem_primeFactors.mp hr).2.1
      have hr_dvd_E : r ∣ Nat.card ↥E :=
        hr_dvd_index.trans (dvd_of_mul_left_eq _
          (Subgroup.card_mul_index ((E ⊓ Subgroup.centralizer (A : Set G)).subgroupOf E)))
      rcases SubgroupESetup.mem_tau_union_of_mem_primeFactors hG h
        (Nat.mem_primeFactors.mpr ⟨hr_prime, hr_dvd_E, Nat.card_pos.ne'⟩) with (h1 | h2) | h3
      · exact h1
      · exfalso
        have hE₂_le_C : E₂ ≤ E ⊓ Subgroup.centralizer (A : Set G) :=
          le_inf h.E₂_le hE₂_le_CA
        have hchain := Subgroup.relIndex_mul_relIndex (hHK := hE₂_le_C)
          (hKL := (inf_le_left : E ⊓ Subgroup.centralizer (A : Set G) ≤ E))
        have hr_dvd' : r ∣ E₂.relIndex E := by
          rw [← hchain]
          exact Dvd.dvd.mul_left hr_dvd_index _
        exact h.E₂_hall.2 r (Nat.mem_primeFactors.mpr ⟨hr_prime, hr_dvd',
          Subgroup.index_ne_zero_of_finite⟩) h2
      · exfalso
        have hE₃_le_C : E₃ ≤ E ⊓ Subgroup.centralizer (A : Set G) :=
          le_inf h.E₃_le hE₃_le_CA
        have hchain := Subgroup.relIndex_mul_relIndex (hHK := hE₃_le_C)
          (hKL := (inf_le_left : E ⊓ Subgroup.centralizer (A : Set G) ≤ E))
        have hr_dvd' : r ∣ E₃.relIndex E := by
          rw [← hchain]
          exact Dvd.dvd.mul_left hr_dvd_index _
        exact h.E₃_hall.2 r (Nat.mem_primeFactors.mpr ⟨hr_prime, hr_dvd',
          Subgroup.index_ne_zero_of_finite⟩) h3
  · -- (d)
    intro p hpσ P hPM hPp hPnc
    have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hpσ.1⟩
    have hodd : Odd p := hG.odd.of_dvd_nat
      ((Nat.mem_primeFactors.mp hpσ.1).2.1.trans (Subgroup.card_subgroup_dvd_card M))
    have hPne : P ≠ ⊥ := by
      intro hbot
      apply hPnc
      rw [hbot]
      infer_instance
    obtain ⟨A₀, hA₀ea, hA₀card⟩ :=
      Ch1.S04.exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic hPp hodd hPnc
    set A : Subgroup G := A₀.map P.subtype with hAdef
    have hA_mem : A ∈ elemAbelianOfRank G p 2 := by
      refine ⟨hA₀ea.map P.subtype_injective, ?_⟩
      rw [hAdef, Subgroup.card_map_of_injective P.subtype_injective, hA₀card]
    have hA_le_P : A ≤ P := Subgroup.map_subtype_le _
    have hCA_le_M : Subgroup.centralizer (A : Set G) ≤ M :=
      centralizer_le_of_elemAb_rank_two hG hM hA_mem (hA_le_P.trans hPM)
    obtain ⟨-, -, h101c, -, -⟩ := S10.fusion_control_of_mem_sigma hG hM hpσ hPne hPp
    intro n hn
    obtain ⟨a, ha, c, hc, rfl⟩ := h101c hPM n hn
    refine M.mul_mem ha.2 (hCA_le_M ?_)
    exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hA_le_P) hc
  · -- (e)
    intro x hxM hx1 hxτ₂ hCMσx
    have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
    -- `M ≤ N_G(M_σ)`.
    have hM_norm_Mσ : M ≤ Subgroup.normalizer ((S10.Msigma M) : Set G) := by
      rw [S10.Msigma, OddOrder.GroupTheory.opiCoreInG]
      have hle := Subgroup.le_normalizer_map
        (H := Ch03.oPiCore (S10.sigma M) ↥M) M.subtype
      rwa [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype] at hle
    -- `E₂` is a Hall `τ₂`-subgroup of `M` as well.
    have hE₂_hall_M : Ch03.IsHallSubgroup (tau2 M) (E₂.subgroupOf M) := by
      constructor
      · intro r hr
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E2_le_M).toEquiv] at hr
        apply h.E₂_hall.1 r
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₂_le).toEquiv]
      · intro r hr hr2
        obtain ⟨hr_prime, hr_dvd, -⟩ := Nat.mem_primeFactors.mp hr
        have hchain := Subgroup.relIndex_mul_relIndex (hHK := h.E₂_le) (hKL := h.E_le)
        have hr_dvd' : r ∣ E₂.relIndex E * E.relIndex M := by
          rwa [hchain]
        rcases hr_prime.dvd_mul.mp hr_dvd' with h1 | h1
        · exact h.E₂_hall.2 r (Nat.mem_primeFactors.mpr ⟨hr_prime, h1,
            Subgroup.index_ne_zero_of_finite⟩) hr2
        · -- `E.relIndex M = |M_σ|`, whose primes lie in `σ(M)`.
          have hEM : E.relIndex M = Nat.card ↥(S10.Msigma M) := by
            have hcard := card_Msigma_mul_card_E h
            have h2 := Subgroup.card_mul_index (E.subgroupOf M)
            rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E_le).toEquiv] at h2
            have h3 : Nat.card ↥E * E.relIndex M
                = Nat.card ↥E * Nat.card ↥(S10.Msigma M) := by
              rw [show E.relIndex M = (E.subgroupOf M).index from rfl, h2, ← hcard]
              ring
            exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h3
          rw [hEM] at h1
          have hrσ : r ∈ S10.sigma M :=
            (S10.isHall_Msigma_Malpha hG hM).1.1 r
              (Nat.mem_primeFactors.mpr ⟨hr_prime, h1, Nat.card_pos.ne'⟩)
          exact (tau2_subset_sigma_compl M hr2) hrσ
    -- Push `⟨x⟩` into a Hall `τ₂`-subgroup of `M`, then conjugate onto `E₂`.
    have hzx_le_M : Subgroup.zpowers x ≤ M := Subgroup.zpowers_le.mpr hxM
    have hx_pi : Ch03.Subgroup.IsPiGroup (tau2 M) ((Subgroup.zpowers x).subgroupOf M) := by
      intro r hr
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzx_le_M).toEquiv,
        Nat.card_zpowers] at hr
      exact hxτ₂ r hr
    obtain ⟨H, hH_hall, -, hx_le_H⟩ :=
      Ch1.S01.aInvariant_piSubgroup_le_aInvariant_hall
        (A := Unit) (φ := (1 : Unit →* MulAut ↥M))
        (by rw [Nat.card_unique]; exact Nat.coprime_one_left _)
        hx_pi (fun _ => one_smul _ _)
    set HG : Subgroup G := H.map M.subtype with hHGdef
    have hHG_le_M : HG ≤ M := Subgroup.map_subtype_le _
    have hHG_hall : Ch03.IsHallSubgroup (tau2 M) (HG.subgroupOf M) := by
      rwa [hHGdef, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    obtain ⟨w, hwM, hw⟩ :=
      Ch1.S06.exists_conj_eq_of_isHall_subgroupOf inferInstance hHG_le_M h.E2_le_M
        hHG_hall hE₂_hall_M
    set y : G := w * x * w⁻¹ with hydef
    have hx_mem_HG : x ∈ HG := by
      rw [hHGdef]
      refine Subgroup.mem_map.mpr ⟨⟨x, hxM⟩, ?_, rfl⟩
      exact hx_le_H (by
        rw [Subgroup.mem_subgroupOf]
        exact Subgroup.mem_zpowers x)
    have hy_mem_E₂ : y ∈ E₂ := by
      rw [← hw, mulAut_smul_eq_map]
      exact ⟨x, hx_mem_HG, by simp [hydef, MulAut.conj_apply]⟩
    have hy1 : y ≠ 1 := by
      intro h1
      apply hx1
      have h2 := congrArg (fun z => w⁻¹ * z * w) h1
      simpa [hydef, mul_assoc] using h2
    have hy_ord : orderOf y = orderOf x := by
      have := orderOf_injective (MulAut.conj w).toMonoidHom (MulAut.conj w).injective x
      simpa [hydef, MulAut.conj_apply] using this
    -- `C_{M_σ}(y) ≠ ⊥` (conjugate of the hypothesis on `x`).
    have hcentr_eq : Subgroup.centralizer ({y} : Set G)
        = MulAut.conj w • Subgroup.centralizer ({x} : Set G) := by
      rw [centralizer_singleton_conj_smul, hydef]
    have hCy_ne : S10.Msigma M ⊓ Subgroup.centralizer ({y} : Set G) ≠ ⊥ := by
      intro hbot
      apply hCMσx
      rw [eq_bot_iff]
      rintro z ⟨hz1, hz2⟩
      have ha1 : w * z * w⁻¹ ∈ S10.Msigma M := by
        have h1 := (Subgroup.mem_normalizer_iff.mp (hM_norm_Mσ hwM) z).mp hz1
        exact h1
      have ha2 : w * z * w⁻¹ ∈ Subgroup.centralizer ({y} : Set G) := by
        rw [hcentr_eq, mulAut_smul_eq_map]
        exact ⟨z, hz2, by simp [MulAut.conj_apply]⟩
      have h3 : w * z * w⁻¹ ∈ (⊥ : Subgroup G) := hbot ▸ ⟨ha1, ha2⟩
      rw [Subgroup.mem_bot] at h3
      have h4 := congrArg (fun u => w⁻¹ * u * w) h3
      simpa [mul_assoc] using h4
    -- Choose the `ℰ_p²(E)`-witness for a prime of `orderOf y`.
    obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd
      (fun h1 => hy1 (orderOf_eq_one_iff.mp h1))
    have : Fact p.Prime := ⟨hp_prime⟩
    have hpτ₂ : p ∈ tau2 M := by
      refine hxτ₂ p (Nat.mem_primeFactors.mpr ⟨hp_prime, ?_, (orderOf_pos x).ne'⟩)
      rwa [← hy_ord]
    obtain ⟨A, hA, hAE⟩ := exists_elemAb_rank_two_le_E_of_tau2 hG h hpτ₂
    have hA_le_M := hAE.trans h.E_le
    have hA_le_Cy : A ≤ Subgroup.centralizer ({y} : Set G) := by
      intro a haA
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact congrArg Subtype.val
        (hbE₂.is_comm.comm (⟨y, hy_mem_E₂⟩ : ↥E₂)
          ⟨a, hA_le_E₂_gen p hp_prime hpτ₂ A hA hAE haA⟩)
    -- Core: every coatom over `C_G(y)` equals `M` (Theorem 12.5(e)).
    have hkey : ∀ Mstar : Subgroup G, IsCoatom Mstar →
        Subgroup.centralizer ({y} : Set G) ≤ Mstar → Mstar = M := by
      intro Mstar hcoat hle
      by_contra hne
      have h125e := (Msigma_nilpotent_of_tau2 hG hM hpτ₂ hA hA_le_M).2.2.2.2.1 Mstar
        (mem_maximalSubgroupsContaining.mpr ⟨hcoat, hA_le_Cy.trans hle⟩) hne
      apply hCy_ne
      rw [eq_bot_iff, ← h125e]
      exact inf_le_inf_left _ hle
    -- `C_G(y) ≤ M` (some coatom exists since `C_G(y) ≠ ⊤`).
    have hCy_le_M : Subgroup.centralizer ({y} : Set G) ≤ M := by
      rcases IsCoatomic.eq_top_or_exists_le_coatom
          (Subgroup.centralizer ({y} : Set G)) with htop | ⟨Mstar, hcoat, hle⟩
      · exfalso
        apply hy1
        have hyZ : y ∈ Subgroup.center G := by
          rw [Subgroup.mem_center_iff]
          intro g
          have hg : g ∈ Subgroup.centralizer ({y} : Set G) := by
            rw [htop]; exact Subgroup.mem_top g
          exact (Subgroup.mem_centralizer_iff.mp hg y rfl).symm
        have hZbot : Subgroup.center G = ⊥ := by
          rcases hG.simple.eq_bot_or_eq_top_of_normal (Subgroup.center G)
            inferInstance with hb | ht
          · exact hb
          · exfalso
            apply hG.notSolvable
            have hcomm : ∀ a b : G, a * b = b * a := fun a b => by
              have ha : a ∈ Subgroup.center G := by
                rw [ht]; exact Subgroup.mem_top a
              exact (Subgroup.mem_center_iff.mp ha b).symm
            let : CommGroup G :=
              { (inferInstance : Group G) with mul_comm := hcomm }
            infer_instance
        rw [hZbot, Subgroup.mem_bot] at hyZ
        exact hyZ
      · exact (hkey Mstar hcoat hle) ▸ hle
    -- Assemble: transport back along `conj w`.
    ext Mstar
    simp only [Set.mem_singleton_iff]
    rw [mem_maximalSubgroupsContaining]
    constructor
    · rintro ⟨hcoat, hle⟩
      have h2 : MulAut.conj w • Mstar = M := by
        apply hkey _ (isCoatom_conj_smul hcoat)
        rw [hcentr_eq]
        exact conj_smul_mono _ hle
      have hMfix : MulAut.conj w⁻¹ • M = M :=
        conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer (inv_mem hwM))
      have h3 := congrArg (fun K => MulAut.conj w⁻¹ • K) h2
      rwa [smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul, hMfix] at h3
    · intro hMs
      rw [hMs]
      refine ⟨mem_maximalSubgroups.mp hM, ?_⟩
      have h4 : Subgroup.centralizer ({x} : Set G)
          = MulAut.conj w⁻¹ • Subgroup.centralizer ({y} : Set G) := by
        rw [hcentr_eq, smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
      rw [h4]
      have hMfix : MulAut.conj w⁻¹ • M = M :=
        conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer (inv_mem hwM))
      have h5 := conj_smul_mono (MulAut.conj w⁻¹) hCy_le_M
      rwa [hMfix] at h5

end OddOrder.BG.Ch3.S12


