-- Prove2me | Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S10_BetaRadicalGlobal
-- name    : OddOrder_BG_Ch3_MaximalSubgroups_S10_BetaRadicalGlobal
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:57:05.389888+00:00
-- url     : https://prove2.me/theorems/bc8ad7bb-1a4c-4b4c-ab8e-067451fcd712
-- title:
--   BG §10: the $\beta$-radical spine, Proposition 10.14 (global structure of $\beta(G)$-primes)
-- statement:
--   Formalizes Proposition 10.14 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §10 (`beta_global_structure`), together with part (d) on normalizers of nontrivial $\beta(M)$-subgroups. It is the middle file of the split $\beta$-radical spine.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 9 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch3_MaximalSubgroups/S10_BetaRadicalGlobal.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch3_MaximalSubgroups/S10_BetaRadicalGlobal.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_SubgroupInAmbient
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S10_BetaRadicalCore
import Definitions.Def_OddOrder_GroupTheory_CyclicSubgroupUniqueness

namespace OddOrder.BG.Ch3.S10

open OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

/-- **Monotonicity of `𝒰` under inclusion within a proper subgroup** (the fiddly lemma of
Prop 10.14(b)): if `A ∈ 𝒰`, `A ≤ R`, and `R` is proper, then `R ∈ 𝒰`. The unique maximal
`M ⊇ A` is the unique maximal `⊇ R`: any coatom `⊇ R` also `⊇ A`, hence equals it; and `R`
proper lies in some coatom (`IsCoatomic`). -/
theorem isUniquelyMaximal_of_le_of_lt_top [Finite G] {A R : Subgroup G}
    (hA : IsUniquelyMaximal A) (hAR : A ≤ R) (hR : R < ⊤) : IsUniquelyMaximal R := by
  obtain ⟨_, M, ⟨hMc, _⟩, hMu⟩ := hA
  refine ⟨hR, M, ?_, ?_⟩
  · -- `M` is a coatom containing `R`: it contains some coatom `⊇ R`, which `⊇ A`, hence `= M`.
    obtain ⟨N, hNc, hRN⟩ :=
      (IsCoatomic.eq_top_or_exists_le_coatom R).resolve_left hR.ne
    have hNeqM : N = M := hMu N ⟨hNc, hAR.trans hRN⟩
    exact ⟨hNeqM ▸ hNc, hNeqM ▸ hRN⟩
  · -- Uniqueness: any coatom `⊇ R` also `⊇ A`, so equals `M`.
    intro N hN
    exact hMu N ⟨hN.1, hAR.trans hN.2⟩

/-- A finite cyclic group has `rank ≤ 1`: any elementary abelian `q`-subgroup `A` is cyclic
(subgroup of cyclic), so its exponent equals its order and divides `q`, whence `|A| ≤ q` and
`log_q |A| ≤ 1`. Contrapositive used in Prop 10.14(b): `2 ≤ rank ↥R ⇒ R` noncyclic. -/
private theorem rank_le_one_of_isCyclic {C : Type*} [Group C] [Finite C] [IsCyclic C] :
    rank C ≤ 1 := by
  rw [rank_le_iff]
  intro q hq
  rw [pRank_le_iff]
  intro A hA
  -- `A` is cyclic, elementary abelian `q`, so `|A| = exponent A ∣ q`, hence `|A| ≤ q`.
  have : IsCyclic ↥A := Subgroup.isCyclic A
  have hexp : Monoid.exponent ↥A ∣ q :=
    Monoid.exponent_dvd_of_forall_pow_eq_one (fun g => hA.pow_eq_one g)
  rw [IsCyclic.exponent_eq_card (α := ↥A)] at hexp
  have hcard_le : Nat.card ↥A ≤ q := Nat.le_of_dvd hq.pos hexp
  calc Nat.log q (Nat.card ↥A) ≤ Nat.log q q := Nat.log_mono_right hcard_le
    _ = 1 := by simpa using (Nat.log_pow hq.one_lt 1)

/-- **BG Proposition 10.14 (a)(b)(c)** (mmd L2894): `p` ideal (`p ∈ β(G)`), `P ∈ Syl_p(G)`。
(a) `ℰ_p²(G) ∩ ℰ_p*(G) = ∅`; (b) `p`-部分群 `R` で `r(R) ≥ 2` なら `R ∈ 𝒰`;
(c) 任意の `X ≤ P` で `N_P(X) ∈ 𝒰`。(原典 (d) は
`normalizer_le_of_nontrivial_beta_subgroup` として別 theorem に露出。)

Proof: (a) `A ∈ ℰ²(G) ∩ ℰ*(G)` ⇒ `A ≤ Q` for some Sylow `Q` (`exists_le_sylow`), `A.subgroupOf Q`
maximal-elem-ab of order `p²` in `↥Q`, contradicting `idealPrime`. (b) `2 ≤ rank ↥R` ⇒ `R`
noncyclic ⇒ `A ∈ ℰ²(R)` (S04), not maximal by (a), so `A ∈ 𝒰` by §9's
`isUniquelyMaximal_of_mem_e2_not_maximal` (Uniqueness Theorem — cited), lifted to `R` by
`isUniquelyMaximal_of_le_of_lt_top`. (c) `Q = N_P(X)`: if `r(Q) ≥ 2` use (b); else `Q` cyclic,
`X char Q`
(cyclic uniqueness), `N_P(Q) ⊆ N_P(X) = Q`, so `Q = P` by the nilpotent normalizer condition,
contradicting `3 ≤ pRank G p ≤ rank ↥P`. -/
theorem beta_global_structure [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    (hp : idealPrime p G) (P : Sylow p G) :
    (¬ ∃ A : Subgroup G, A ∈ elemAbelianOfRank G p 2 ∧ IsMaximalElementaryAbelian p A) ∧
    (∀ R : Subgroup G, IsPGroup p ↥R → 2 ≤ rank ↥R → IsUniquelyMaximal R) ∧
    (∀ X : Subgroup G, X ≤ (P : Subgroup G) →
      IsUniquelyMaximal (Subgroup.normalizer (X : Set G) ⊓ (P : Subgroup G))) := by
  obtain ⟨hpRank3, hpIdeal⟩ := hp
  have hp_prime : p.Prime := Fact.out
  -- `p ∣ |G|` (from `pRank G p ≥ 3 > 0`), hence `p` is odd.
  have hp_odd : Odd p := by
    -- `¬ pRank G p ≤ 0` gives an elem-ab `A` with `1 ≤ log_p |A|`, so `p ≤ |A|`.
    have hnle : ¬ pRank G p ≤ 0 := by omega
    rw [pRank_le_iff] at hnle
    simp only [not_forall, not_le] at hnle
    obtain ⟨A, hA_elem, hAlog⟩ := hnle
    have hp_le_A : p ≤ Nat.card ↥A := by
      have h1 : 1 ≤ Nat.log p (Nat.card ↥A) := by omega
      calc p = p ^ 1 := (pow_one p).symm
        _ ≤ Nat.card ↥A := Nat.pow_le_of_le_log Nat.card_pos.ne' h1
    have hp_dvd_A : p ∣ Nat.card ↥A := by
      obtain ⟨j, hj⟩ := (IsPGroup.iff_card (p := p)).mp hA_elem.isPGroup
      have hjpos : 1 ≤ j := by
        rcases Nat.eq_zero_or_pos j with hj0 | hjpos
        · rw [hj, hj0, pow_zero] at hp_le_A
          exact absurd hp_le_A (by have := hp_prime.one_lt; omega)
        · exact hjpos
      rw [hj]; exact dvd_pow_self p (by omega : j ≠ 0)
    have hp_dvd_G : p ∣ Nat.card G := hp_dvd_A.trans A.card_subgroup_dvd_card
    exact hG.odd.of_dvd_nat hp_dvd_G
  -- ===== Part (a) =====
  have partA : ¬ ∃ A : Subgroup G,
      A ∈ elemAbelianOfRank G p 2 ∧ IsMaximalElementaryAbelian p A := by
    rintro ⟨A, hA2, hAmax⟩
    rw [mem_elemAbelianOfRank] at hA2
    obtain ⟨hA_elem, hA_card⟩ := hA2
    -- `A` is a `p`-group, land it in a Sylow `Q`.
    obtain ⟨Q, hAQ⟩ := hA_elem.isPGroup.exists_le_sylow
    -- `A.subgroupOf Q` has order `p²` and is maximal-elem-ab in `↥Q`, contradicting `idealPrime`.
    refine hpIdeal Q ⟨A.subgroupOf (Q : Subgroup G), ?_, ?_⟩
    · rw [← Subgroup.card_map_of_injective (Q : Subgroup G).subtype_injective,
        Subgroup.map_subgroupOf_eq_of_le hAQ, hA_card]
    · refine ⟨?_, ?_⟩
      · apply Subgroup.IsElementaryAbelian.of_map (f := (Q : Subgroup G).subtype)
          (Q : Subgroup G).subtype_injective
        rwa [Subgroup.map_subgroupOf_eq_of_le hAQ]
      · intro F' hF'_elem hF'_ge
        -- map `F' ≤ ↥Q` to `G`; it is elem-ab, ⊇ `A`, so `= A` by `G`-maximality.
        have hF_elem : (F'.map (Q : Subgroup G).subtype).IsElementaryAbelian p :=
          hF'_elem.map (Q : Subgroup G).subtype_injective
        have hAF : A ≤ F'.map (Q : Subgroup G).subtype := by
          calc A = (A.subgroupOf (Q : Subgroup G)).map (Q : Subgroup G).subtype :=
                (Subgroup.map_subgroupOf_eq_of_le hAQ).symm
            _ ≤ F'.map (Q : Subgroup G).subtype := Subgroup.map_mono hF'_ge
        have hFeqA : F'.map (Q : Subgroup G).subtype = A := hAmax.2 _ hF_elem hAF
        -- inject back: `F' = A.subgroupOf Q`.
        have := hFeqA.trans (Subgroup.map_subgroupOf_eq_of_le hAQ).symm
        exact Subgroup.map_injective (Q : Subgroup G).subtype_injective this
  -- ===== Part (b) =====
  have partB : ∀ R : Subgroup G, IsPGroup p ↥R → 2 ≤ rank ↥R → IsUniquelyMaximal R := by
    intro R hR_pg hR_rank
    -- `2 ≤ rank ↥R` ⇒ `R` noncyclic ⇒ `R` has `E ∈ ℰ²(↥R)` (S04).
    have hR_nc : ¬ IsCyclic ↥R := by
      intro hRc
      have := hRc
      have : rank ↥R ≤ 1 := rank_le_one_of_isCyclic (C := ↥R)
      omega
    obtain ⟨E, hE_elem, hE_card⟩ :=
      OddOrder.BG.Ch1.S04.exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic
        hR_pg hp_odd hR_nc
    -- map `E ≤ ↥R` to `A ≤ R` in `G`.
    set A : Subgroup G := E.map R.subtype with hA_def
    have hAR : A ≤ R := Subgroup.map_subtype_le E
    have hA_elem : A.IsElementaryAbelian p :=
      hE_elem.map R.subtype_injective
    have hA_card : Nat.card ↥A = p ^ 2 := by
      rw [hA_def, Subgroup.card_map_of_injective R.subtype_injective, hE_card]
    have hA2 : A ∈ elemAbelianOfRank G p 2 := by
      rw [mem_elemAbelianOfRank]; exact ⟨hA_elem, hA_card⟩
    -- By (a), `A` is not maximal-elem-ab, so `A ∈ 𝒰` (§9 Uniqueness Theorem corollary).
    have hAns : ¬ IsMaximalElementaryAbelian p A := fun hAmax => partA ⟨A, hA2, hAmax⟩
    have hAU : IsUniquelyMaximal A :=
      OddOrder.BG.Ch2.S09.isUniquelyMaximal_of_mem_e2_not_maximal hG hA2 hAns
    -- `R` is proper (`R = ⊤` ⇒ `G` is a solvable `p`-group, contradiction), so lift `A ∈ 𝒰`.
    have hR_lt : R < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro hRtop
      have hGpg : IsPGroup p G :=
        hR_pg.of_equiv (hRtop ▸ Subgroup.topEquiv : (↥R : Type _) ≃* G)
      have : Group.IsNilpotent G := hGpg.isNilpotent
      exact hG.notSolvable inferInstance
    exact isUniquelyMaximal_of_le_of_lt_top hAU hAR hR_lt
  -- ===== Part (c) =====
  refine ⟨partA, partB, ?_⟩
  intro X hXP
  set Q : Subgroup G := Subgroup.normalizer (X : Set G) ⊓ (P : Subgroup G) with hQ_def
  -- `Q ≤ P`, so `Q` is a `p`-group.
  have hQP : Q ≤ (P : Subgroup G) := inf_le_right
  have hQ_pg : IsPGroup p ↥Q :=
    P.2.of_injective (Subgroup.inclusion hQP) (Subgroup.inclusion_injective hQP)
  by_cases hrank : 2 ≤ rank ↥Q
  · exact partB Q hQ_pg hrank
  · -- `rank ↥Q ≤ 1`; derive a contradiction (`Q = P` but `rank ↥P ≥ 3`).
    exfalso
    -- `Q` is cyclic: else it has an `E_{p²}`, forcing `rank ↥Q ≥ 2`.
    have hQ_cyclic : IsCyclic ↥Q := by
      by_contra hQnc
      obtain ⟨E, hE_elem, hE_card⟩ :=
        OddOrder.BG.Ch1.S04.exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic
          hQ_pg hp_odd hQnc
      have : 2 ≤ pRank ↥Q p := pow_le_card_of_le_pRank E hE_elem hE_card
      have : 2 ≤ rank ↥Q := le_trans this (pRank_le_rank p)
      omega
    -- `X ≤ Q` (`X` normalizes itself and `X ≤ P`).
    have hXQ : X ≤ Q := by
      rw [hQ_def, le_inf_iff]
      exact ⟨Subgroup.le_normalizer, hXP⟩
    -- `N_G(Q) ⊓ P ≤ Q`: any `g ∈ P` normalizing `Q` normalizes the characteristic `X`.
    have hself : Subgroup.normalizer (Q : Set G) ⊓ (P : Subgroup G) ≤ Q := by
      rintro g ⟨hgN, hgP⟩
      rw [hQ_def, Subgroup.mem_inf]
      refine ⟨?_, hgP⟩
      -- `g` normalizes `Q`: `∀ n, n ∈ Q ↔ g n g⁻¹ ∈ Q`.
      have hgN' : ∀ n, n ∈ (Q : Set G) ↔ g * n * g⁻¹ ∈ (Q : Set G) :=
        Subgroup.mem_set_normalizer_iff.mp hgN
      -- `X' = gXg⁻¹` is a subgroup of `Q` of order `|X|`, so `X' = X` (cyclic uniqueness in `↥Q`).
      set X' : Subgroup G := X.map (MulAut.conj g).toMonoidHom with hX'_def
      have hX'Q : X' ≤ Q := by
        rw [hX'_def]
        rintro y ⟨x, hx, rfl⟩
        have hxQ : (x : G) ∈ (Q : Set G) := hXQ hx
        have : g * x * g⁻¹ ∈ (Q : Set G) := (hgN' x).mp hxQ
        simpa [MulAut.conj_apply] using this
      have hX'_card : Nat.card ↥X' = Nat.card ↥X := by
        rw [hX'_def, Subgroup.card_map_of_injective (MulAut.conj g).injective]
      -- Inside `↥Q`: the two `subgroupOf`s have equal card, hence are equal.
      have hsubOf_card : Nat.card ↥(X'.subgroupOf Q) = Nat.card ↥(X.subgroupOf Q) := by
        rw [← Subgroup.card_map_of_injective Q.subtype_injective,
          Subgroup.map_subgroupOf_eq_of_le hX'Q,
          ← Subgroup.card_map_of_injective Q.subtype_injective,
          Subgroup.map_subgroupOf_eq_of_le hXQ, hX'_card]
      have hsubOf_eq : X'.subgroupOf Q = X.subgroupOf Q :=
        cyclic_subgroup_eq_of_card_eq (C := ↥Q) hsubOf_card
      -- Map back along `Q.subtype`: `X' = X`.
      have hX'eqX : X' = X := by
        have hmap : (X'.subgroupOf Q).map Q.subtype = (X.subgroupOf Q).map Q.subtype :=
          congrArg (Subgroup.map Q.subtype) hsubOf_eq
        rwa [Subgroup.map_subgroupOf_eq_of_le hX'Q,
          Subgroup.map_subgroupOf_eq_of_le hXQ] at hmap
      -- `X.map (conj g) = X` gives `g h g⁻¹ ∈ X ↔ h ∈ X`.
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        have : g * h * g⁻¹ ∈ X' := by
          rw [hX'_def, Subgroup.mem_map]
          exact ⟨h, hh, by simp [MulAut.conj_apply]⟩
        rwa [hX'eqX] at this
      · intro hh
        rw [← hX'eqX, hX'_def, Subgroup.mem_map] at hh
        obtain ⟨x, hx, hxeq⟩ := hh
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hxeq
        -- `g * x * g⁻¹ = g * h * g⁻¹` ⇒ `x = h`.
        have hxh : x = h := by
          have h1 : g * x = g * h := mul_right_cancel hxeq
          exact mul_left_cancel h1
        rwa [← hxh]
    -- `Q = P` by the nilpotent normalizer condition.
    have hQeqP : Q = (P : Subgroup G) := by
      by_contra hQne
      have hQlt : Q < (P : Subgroup G) := lt_of_le_of_ne hQP hQne
      have : Group.IsNilpotent ↥(P : Subgroup G) := P.2.isNilpotent
      have hNC : NormalizerCondition ↥(P : Subgroup G) :=
        Group.normalizerCondition_of_isNilpotent (G := ↥(P : Subgroup G))
      have hQsub_lt : Q.subgroupOf (P : Subgroup G) < ⊤ := by
        rw [lt_top_iff_ne_top]
        intro htop
        rw [Subgroup.subgroupOf_eq_top] at htop
        exact hQne (le_antisymm hQP htop)
      obtain ⟨t, ht_norm, ht_not⟩ := SetLike.exists_of_lt (hNC _ hQsub_lt)
      rw [← Subgroup.subgroupOf_normalizer_eq hQP, Subgroup.mem_subgroupOf] at ht_norm
      rw [Subgroup.mem_subgroupOf] at ht_not
      -- `↑t ∈ N_G(Q) ⊓ P ≤ Q`, so `↑t ∈ Q`, contradicting `t ∉ Q.subgroupOf P`.
      exact ht_not (hself ⟨ht_norm, t.2⟩)
    -- But `rank ↥P ≥ 3 > 1 ≥ rank ↥Q = rank ↥P`.
    have hPrank : 3 ≤ rank ↥(P : Subgroup G) :=
      le_trans (le_trans hpRank3 (pRank_le_pRank_sylow P)) (pRank_le_rank p)
    rw [hQeqP] at hrank
    omega

/-- **BG Proposition 10.14(d)** (mmd L2894): `M ∈ ℳ` とし、`Y` を `M` の非自明
`β(M)`-部分群とする。このとき `N_G(Y) ⊆ M`。

This is the §13-facing clause used in Lemma 13.8 and Theorem 13.10. The proof is still a
§10 proof gate: BG chooses a prime `q ∈ π(F(Y))`, reduces to `q ∈ β(M)`, applies
Proposition 10.14(c) to `O_q(Y)`, and then obtains the ambient normalizer containment.
It is intentionally exposed as a theorem, not hoisted into any downstream setup field. -/
theorem normalizer_le_of_nontrivial_beta_subgroup [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {Y : Subgroup G} (hYM : Y ≤ M)
    (hYne : Y ≠ ⊥) (hYβ : Subgroup.IsPiSubgroup (beta M) Y) :
    Subgroup.normalizer (Y : Set G) ≤ M := by
  classical
  have hM_co : IsCoatom M := mem_maximalSubgroups.mp hM
  -- `↥Y` is finite, solvable and nontrivial, so `F(↥Y) ≠ 1` and `q ∣ |F(↥Y)|` for some prime `q`.
  have hMsolv : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  have hYsolv : Group.IsSolvable ↥Y :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hYM)
  have hYnt : Nontrivial ↥Y := (Subgroup.nontrivial_iff_ne_bot Y).mpr hYne
  have hFne : Ch01.fitting ↥Y ≠ ⊥ := Ch01.fitting_ne_bot_of_isSolvable_nontrivial ↥Y
  have hFnt : Nontrivial ↥(Ch01.fitting ↥Y) := (Subgroup.nontrivial_iff_ne_bot _).mpr hFne
  obtain ⟨q, hq_prime, hq_dvdF⟩ :=
    (Nat.card ↥(Ch01.fitting ↥Y)).exists_prime_and_dvd
      (by have := Finite.one_lt_card_iff_nontrivial.mpr hFnt; omega)
  have : Fact q.Prime := ⟨hq_prime⟩
  -- `q ∈ π(F(↥Y)) ⊆ π(Y)`, hence `q ∈ β(M)`: `idealPrime q G` and `q ∈ α(M) ⊆ σ(M)`.
  have hq_piY : q ∈ (Nat.card ↥Y).primeFactors := by
    refine Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvdF.trans ?_, Nat.card_pos.ne'⟩
    exact Subgroup.card_subgroup_dvd_card _
  have hqβ : q ∈ beta M := hYβ q hq_piY
  rw [mem_beta_iff] at hqβ
  obtain ⟨hqα, hq_ideal⟩ := hqβ
  have hqσ : q ∈ sigma M := alpha_subset_sigma hG hM hqα
  -- `X := O_q(↥Y)` realised in `G`: a `q`-subgroup, `≤ Y ≤ M`, and characteristic in `Y`.
  set X : Subgroup G := opiCoreInG ({q} : Set ℕ) Y with hXdef
  have hX_pg : IsPGroup q ↥X := isPGroup_opiCoreInG_singleton Y
  have hXY : X ≤ Y := opiCoreInG_le _ _
  have hXM : X ≤ M := hXY.trans hYM
  -- `X ≠ ⊥`: a `q`-element of `F(↥Y)` lies in `O_q(↥Y)` (`mem_opCore_of_le_fitting`).
  have hXne : X ≠ ⊥ := by
    obtain ⟨x, hx_ord⟩ := exists_prime_orderOf_dvd_card' q hq_dvdF
    set K : Subgroup ↥Y := (Subgroup.zpowers x).map (Ch01.fitting ↥Y).subtype with hKdef
    have hKcard : Nat.card ↥K = q := by
      rw [hKdef, Subgroup.card_map_of_injective (Ch01.fitting ↥Y).subtype_injective,
        Nat.card_zpowers, hx_ord]
    have hK_pg : IsPGroup q ↥K := by
      rw [IsPGroup.iff_card]; exact ⟨1, by rw [hKcard, pow_one]⟩
    have hK_fit : K ≤ Ch01.fitting ↥Y := Subgroup.map_subtype_le _
    have hK_op : K ≤ Ch01.opCore q ↥Y :=
      Ch02.mem_opCore_of_le_fitting_of_isPGroup hK_pg hK_fit
    have hop_ne : Ch01.opCore q ↥Y ≠ ⊥ := by
      intro hbot
      rw [hbot, le_bot_iff] at hK_op
      have h1 : Nat.card ↥K = 1 := by simp [hK_op]
      have := hq_prime.two_le
      omega
    have hbridge : X = (Ch01.opCore q ↥Y).map Y.subtype := by
      rw [hXdef, OddOrder.GroupTheory.opiCoreInG, Ch04.oPiCore_singleton_eq_opCore]
    rw [hbridge, Ne, Subgroup.map_eq_bot_iff, Subgroup.ker_subtype, le_bot_iff]
    exact hop_ne
  -- Land `X` in a Sylow `q`-subgroup `S` of `G` that lies in `M` (using `q ∈ σ(M)`).
  have hXMsub_pg : IsPGroup q ↥(X.subgroupOf M) :=
    hX_pg.of_equiv (Subgroup.subgroupOfEquivOfLe hXM).symm
  obtain ⟨P, hXP⟩ := hXMsub_pg.exists_le_sylow
  obtain ⟨S, hS_eq⟩ := isSylow_sylowMap_of_mem_sigma hqσ P
  have hS_le_M : (S : Subgroup G) ≤ M := by rw [hS_eq]; exact Subgroup.map_subtype_le _
  have hXS : X ≤ (S : Subgroup G) := by
    rw [hS_eq, ← Subgroup.map_subgroupOf_eq_of_le hXM]
    exact Subgroup.map_mono hXP
  -- Proposition 10.14(c): `N_G(X) ⊓ S` is uniquely maximal, with unique coatom `M`.
  obtain ⟨_, M', ⟨hM'co, _⟩, hM'uniq⟩ := (beta_global_structure hG hq_ideal S).2.2 X hXS
  have hcap_le_M : Subgroup.normalizer (X : Set G) ⊓ (S : Subgroup G) ≤ M :=
    le_trans inf_le_right hS_le_M
  have hM_eq : M = M' := hM'uniq M ⟨hM_co, hcap_le_M⟩
  -- `N_G(X)` is proper (else `X ⊴ G`, contradicting `G` simple with `⊥ ≠ X ≠ ⊤`).
  have hNX_lt : Subgroup.normalizer (X : Set G) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    have hXnormal : X.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases (hG.simple).eq_bot_or_eq_top_of_normal X hXnormal with hb | ht
    · exact hXne hb
    · exact hM_co.1 (top_le_iff.mp (ht ▸ hXM))
  -- A coatom `C ⊇ N_G(X)` exists; it contains `N_G(X) ⊓ S`, so `C = M' = M`.
  obtain ⟨C, hCco, hNXC⟩ :=
    (IsCoatomic.eq_top_or_exists_le_coatom (Subgroup.normalizer (X : Set G))).resolve_left
      hNX_lt.ne
  have hCeq : C = M' := hM'uniq C ⟨hCco, le_trans inf_le_left hNXC⟩
  -- `N_G(Y) ≤ N_G(X) ≤ C = M` (characteristic core normalizer).
  have hNYNX : Subgroup.normalizer (Y : Set G) ≤ Subgroup.normalizer (X : Set G) := by
    rw [hXdef]
    exact le_normalizer_opiCoreInG_of_le_normalizer ({q} : Set ℕ) (le_refl _)
  calc Subgroup.normalizer (Y : Set G)
      ≤ Subgroup.normalizer (X : Set G) := hNYNX
    _ ≤ C := hNXC
    _ = M := by rw [hCeq, ← hM_eq]

/-- 有限 nilpotent 群では `q`-部分群 `X` が `p`-部分群 `P` を中心化する (`p ≠ q`)。
nilpotent ⟹ 各 Sylow 正規 (`Group.isNilpotent_of_finite_tfae`)、`X ≤` Sylow `q` `Q`,
`P ≤` Sylow `p` `P_W`, 異素数ゆえ `Q ⊓ P_W = ⊥` (`IsPGroup.disjoint_of_ne`)、正規 2 部分群は
disjoint なら可換 (`commute_of_normal_of_disjoint`)。BG Cor 10.9(a)(1) で「`W` nilpotent ⟹
`X` が `M_σ` の Sylow `p` を中心化」に使う。 -/
theorem isPGroup_le_centralizer_of_isNilpotent {W : Type*} [Group W] [Finite W]
    (hW : Group.IsNilpotent W) {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {X P : Subgroup W} (hX : IsPGroup q ↥X) (hP : IsPGroup p ↥P) :
    X ≤ Subgroup.centralizer (P : Set W) := by
  obtain ⟨Q, hXQ⟩ := hX.exists_le_sylow
  obtain ⟨PW, hPPW⟩ := hP.exists_le_sylow
  have hAllNormal : ∀ (r : ℕ), Fact r.Prime → ∀ (R : Sylow r W), (↑R : Subgroup W).Normal :=
    ((Group.isNilpotent_of_finite_tfae (G := W)).out 0 3).mp hW
  have hQnorm : (Q : Subgroup W).Normal := hAllNormal q ‹Fact q.Prime› Q
  have hPWnorm : (PW : Subgroup W).Normal := hAllNormal p ‹Fact p.Prime› PW
  have hdis : Disjoint (Q : Subgroup W) (PW : Subgroup W) :=
    IsPGroup.disjoint_of_ne q p hpq.symm (Q : Subgroup W) (PW : Subgroup W)
      Q.isPGroup' PW.isPGroup'
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (Subgroup.commute_of_normal_of_disjoint _ _ hQnorm hPWnorm hdis x y
    (hXQ hx) (hPPW hy)).symm.eq

/-- **Cor 10.9(a) 核 (`X ⊄ M'` の `W` nilpotent 判定)** (一般・unconditional): `W` が
`{p,q}`-群 (`p ≠ q`), 正規 Sylow `q`-部分群 `Qs` を持ち, `N ⊴ W` が nilpotent で `W/N` が
`q`-群なら `W` は nilpotent。

`N` nilpotent ⟹ Sylow `p` `PN` が `N` で正規・characteristic (`Sylow.characteristic_of_normal`)、
`N ⊴ W` で押し出すと `W` で正規 (`OddOrder.GroupTheory.normal_map_subtype_of_characteristic`)。`W/N` が `q`-群ゆえ
`|W|_p = |N|_p` で `PN.map N.subtype` は `W` の Sylow `p`。正規 Sylow `p`/`q` で全 Sylow 正規
(`Sylow.unique_of_normal`)、よって `W` nilpotent (`Group.isNilpotent_of_finite_tfae` 3→0)。
BG Cor 10.9(a) の `X ⊄ M'` (`p < q`) ケースで `W` の nilpotency に使う。 -/
theorem isNilpotent_of_normalSylowQ_of_nilpotent_qQuotient {W : Type*} [Group W] [Finite W]
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    (hWpq : ∀ r ∈ (Nat.card W).primeFactors, r = p ∨ r = q)
    (Qs : Sylow q W) (hQnorm : (Qs : Subgroup W).Normal)
    {N : Subgroup W} [N.Normal] (hNnil : Group.IsNilpotent ↥N)
    (hWNq : ∀ r ∈ (Nat.card (W ⧸ N)).primeFactors, r = q) :
    Group.IsNilpotent W := by
  -- `|W|_p = |N|_p` since `W/N` is a `q`-group.
  have hp_ndvd_quot : ¬ p ∣ Nat.card (W ⧸ N) := fun hdvd =>
    hpq (hWNq p (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩))
  have hfact : (Nat.card W).factorization p = (Nat.card ↥N).factorization p := by
    have hq0 : Nat.card (W ⧸ N) ≠ 0 := Nat.card_pos.ne'
    have hn0 : Nat.card ↥N ≠ 0 := Nat.card_pos.ne'
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N,
        Nat.factorization_mul hq0 hn0, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hp_ndvd_quot, zero_add]
  -- A normal Sylow `p`-subgroup of `W`, built from `N`.
  obtain ⟨PN⟩ := (inferInstance : Nonempty (Sylow p ↥N))
  have hAllNormalN : ∀ (r : ℕ), Fact r.Prime → ∀ (R : Sylow r ↥N), (↑R : Subgroup ↥N).Normal :=
    ((Group.isNilpotent_of_finite_tfae (G := ↥N)).out 0 3).mp hNnil
  have hPNnorm : (PN : Subgroup ↥N).Normal := hAllNormalN p ‹Fact p.Prime› PN
  have hPNchar : (PN : Subgroup ↥N).Characteristic := Sylow.characteristic_of_normal PN hPNnorm
  have hPpcard : Nat.card ↥((PN : Subgroup ↥N).map N.subtype) =
      p ^ (Nat.card W).factorization p := by
    rw [Subgroup.card_subtype, Sylow.card_eq_multiplicity PN, hfact]
  have hPpnorm : ((PN : Subgroup ↥N).map N.subtype).Normal :=
    OddOrder.GroupTheory.normal_map_subtype_of_characteristic hPNchar
  set Psyl : Sylow p W := Sylow.ofCard _ hPpcard with hPsyl
  have hPsyl_coe : (Psyl : Subgroup W) = (PN : Subgroup ↥N).map N.subtype :=
    Sylow.coe_ofCard _ hPpcard
  have hPsylnorm : (Psyl : Subgroup W).Normal := by rw [hPsyl_coe]; exact hPpnorm
  -- Every Sylow of `W` is normal ⟹ `W` nilpotent.
  have hAllNormalW : ∀ (r : ℕ), Fact r.Prime → ∀ (P : Sylow r W), (↑P : Subgroup W).Normal := by
    intro r hr_fact P
    have := hr_fact
    by_cases hrW : r ∈ (Nat.card W).primeFactors
    · rcases hWpq r hrW with rfl | rfl
      · have := Sylow.unique_of_normal Psyl hPsylnorm
        rw [Subsingleton.elim P Psyl]; exact hPsylnorm
      · have := Sylow.unique_of_normal Qs hQnorm
        rw [Subsingleton.elim P Qs]; exact hQnorm
    · -- `r ∉ π(W)`: the Sylow `r`-subgroup is trivial.
      have hr_ndvd : ¬ r ∣ Nat.card W := fun hdvd =>
        hrW (Nat.mem_primeFactors.mpr ⟨hr_fact.out, hdvd, Nat.card_pos.ne'⟩)
      have hPcard : Nat.card ↥(P : Subgroup W) = 1 := by
        rw [Sylow.card_eq_multiplicity P, Nat.factorization_eq_zero_of_not_dvd hr_ndvd, pow_zero]
      rw [Subgroup.card_eq_one.mp hPcard]; infer_instance
  exact ((Group.isNilpotent_of_finite_tfae (G := W)).out 3 0).mp hAllNormalW

/-- **Corollary 10.9 核 (W ∩ M' is nilpotent)** (mmd L2860, forward-conditional via Theorem 10.6):
`M' = derivedInG M` の任意の `β(M)'`-部分群 `V` は nilpotent。

BG Cor 10.9(a) の証明で「`W ∩ M'` is nilpotent」(及び `X ⊆ M'` のとき `W` 自身が nilpotent) に
使う。`M'` は nilpotent な Hall `β(M)'`-部分群 `W*` を持つ (Lemma 10.8(b) = `isHall_Mbeta`)。
任意の `β(M)'`-部分群 `V` は Hall `β(M)'`-部分群 `W'` に含まれ (Hall-D = `Ch03.hall_D`)、`W'` は
`W*` と共役 (Hall-C = `Ch03.hall_C`) ゆえ nilpotent、よって部分群 `V ≤ W'` も nilpotent。 -/
theorem betacompl_subgroup_derived_isNilpotent [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {V : Subgroup G} (hVD : V ≤ derivedInG M)
    (hVβ : ∀ r ∈ (Nat.card ↥V).primeFactors, r ∉ beta M) :
    Group.IsNilpotent ↥V := by
  have hMsolv : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  have hDsolv : Group.IsSolvable ↥(derivedInG M) := by
    let e := Subgroup.equivMapOfInjective (commutator ↥M) M.subtype M.subtype_injective
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  -- `W*`: a nilpotent Hall `β(M)'`-subgroup of `M'` (Lemma 10.8(b)).
  obtain ⟨Wstar, hWstar_le, hWstar_hall, hWstar_nilp⟩ := (isHall_Mbeta hG hM).2.1
  have := hWstar_nilp
  have hWstar'_nilp : Group.IsNilpotent ↥(Wstar.subgroupOf (derivedInG M)) :=
    Group.nilpotent_of_surjective (Subgroup.subgroupOfEquivOfLe hWstar_le).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hWstar_le).symm.surjective
  -- `V.subgroupOf M'` is a `β(M)'`-subgroup; embed it in a Hall `β(M)'`-subgroup `W'` (Hall-D).
  have hV'β : ∀ r ∈ (Nat.card ↥(V.subgroupOf (derivedInG M))).primeFactors, r ∈ (beta M)ᶜ := by
    intro r hr
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVD).toEquiv] at hr
    exact hVβ r hr
  obtain ⟨W', hW'_hall, hV'_le⟩ := Ch03.hall_D (G := ↥(derivedInG M)) hV'β
  -- `W'` is conjugate to `W*` (Hall-C), hence nilpotent.
  obtain ⟨g, hg⟩ := Ch03.hall_C hWstar_hall hW'_hall
  have hW'_nilp : Group.IsNilpotent ↥W' := by
    rw [← hg]
    exact Group.nilpotent_of_surjective
      (Subgroup.equivMapOfInjective (Wstar.subgroupOf (derivedInG M))
        (MulAut.conj g).toMonoidHom (MulEquiv.injective _)).toMonoidHom (MulEquiv.surjective _)
  -- `V ≤ W'` (in `M'`) and `W'` nilpotent ⟹ `V` nilpotent.
  have : Group.IsNilpotent ↥((V.subgroupOf (derivedInG M)).subgroupOf W') := inferInstance
  have hV'_nilp : Group.IsNilpotent ↥(V.subgroupOf (derivedInG M)) :=
    Group.nilpotent_of_surjective (Subgroup.subgroupOfEquivOfLe hV'_le).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hV'_le).surjective
  exact Group.nilpotent_of_surjective (Subgroup.subgroupOfEquivOfLe hVD).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hVD).surjective

/-- `Ch03.IsHallSubgroup` は位数と指数のみで定義されるので, 群同型 `e : A ≃* B` で
`π`-Hall 部分群 `H` の像 `H.map e` も `π`-Hall。`Nat.card`/`index` がともに `e` で保存される
(`equivMapOfInjective` / `index_map_equiv`)。Cor 10.9 で `W ∩ M_σ` が `M_σ` の Hall であることを
nested ambient `↥Y` から `↥(M_σ)` へ移すのに使う。 -/
theorem isHallSubgroup_map_mulEquiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) {π : Set ℕ} {H : Subgroup A} (h : Ch03.IsHallSubgroup π H) :
    Ch03.IsHallSubgroup π (H.map (e : A →* B)) := by
  have hcard : Nat.card ↥(H.map (e : A →* B)) = Nat.card ↥H :=
    (Nat.card_congr (Subgroup.equivMapOfInjective H (e : A →* B) e.injective).toEquiv).symm
  refine ⟨?_, ?_⟩
  · intro r hr
    rw [hcard] at hr
    exact h.1 r hr
  · intro r hr
    rw [Subgroup.index_map_equiv H e] at hr
    exact h.2 r hr

/-- **Cor 10.9(a)(1) 核, ambient 形** (一般・unconditional): `W ≤ G` が nilpotent (`↥W` として),
`X, P ≤ W` でそれぞれ `q`-群 / `p`-群 (`p ≠ q`) なら `X ≤ C_G(P)`。
`isPGroup_le_centralizer_of_isNilpotent` を `X.subgroupOf W` / `P.subgroupOf W` に適用し,
`↥W` 内の可換性を `W.subtype` で `G` へ移す。 -/
theorem isPGroup_le_centralizer_of_isNilpotent_ambient {W : Subgroup G} [Finite ↥W]
    (hW : Group.IsNilpotent ↥W) {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {X P : Subgroup G} (hXW : X ≤ W) (hPW : P ≤ W) (hXq : IsPGroup q ↥X) (hPp : IsPGroup p ↥P) :
    X ≤ Subgroup.centralizer (P : Set G) := by
  have hX' : IsPGroup q ↥(X.subgroupOf W) :=
    hXq.of_equiv (Subgroup.subgroupOfEquivOfLe hXW).symm
  have hP' : IsPGroup p ↥(P.subgroupOf W) :=
    hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPW).symm
  have key := isPGroup_le_centralizer_of_isNilpotent hW hpq hX' hP'
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hxW : x ∈ W := hXW hx
  have hyW : y ∈ W := hPW hy
  have hxmem : (⟨x, hxW⟩ : ↥W) ∈ X.subgroupOf W := Subgroup.mem_subgroupOf.mpr hx
  have hymem : (⟨y, hyW⟩ : ↥W) ∈ P.subgroupOf W := Subgroup.mem_subgroupOf.mpr hy
  have hcent := key hxmem
  rw [Subgroup.mem_centralizer_iff] at hcent
  have hcomm := hcent ⟨y, hyW⟩ hymem
  have := congrArg (Subtype.val) hcomm
  simpa using this

end OddOrder.BG.Ch3.S10


