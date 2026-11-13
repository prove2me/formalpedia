-- Prove2me | Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S10_LocalCriteria
-- name    : OddOrder_BG_Ch3_MaximalSubgroups_S10_LocalCriteria
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:49:55.756132+00:00
-- url     : https://prove2.me/theorems/fbed6f5c-a7da-4211-83bc-9655f6ef4e74
-- title:
--   BG §10: local criteria lemmas (Lemmas 10.3 and 10.4)
-- statement:
--   Formalizes Lemmas 10.3 and 10.4 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §10: a cluster of $\alpha$/$\sigma$ criteria sitting on top of the Hall-structure base (Theorems 10.1/10.2). It covers Lemma 10.3 (a centralizer is uniquely maximal under a rank condition), Lemma 10.4(a)(c) (the $\alpha$-criterion) and Lemma 10.4(b) (existence of an $\Omega_1$-central element in a Z-group centralizer).
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 10 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch3_MaximalSubgroups/S10_LocalCriteria.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch3_MaximalSubgroups/S10_LocalCriteria.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S10_HallStructure
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S01c_Omega1Rigidity
import Definitions.Def_OddOrder_BG_AppB_PuigB3B4
import Mathlib.GroupTheory.SpecificGroups.ZGroup

namespace OddOrder.BG.Ch3.S10

open OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- A Sylow `p`-subgroup `P` of `G` contained in `K ≤ G` restricts to a Sylow `p`-subgroup of
`↥K` with carrier `P.subgroupOf K` (replicates the private `S07.sylow_subgroupOf_of_le`). -/
private theorem sylow_subgroupOf_of_le {p : ℕ} [Fact p.Prime] [Finite G] (P : Sylow p G)
    {K : Subgroup G} (hPK : (P : Subgroup G) ≤ K) :
    ∃ Q : Sylow p ↥K, (Q : Subgroup ↥K) = (P : Subgroup G).subgroupOf K := by
  have hpg : IsPGroup p ↥((P : Subgroup G).subgroupOf K) := by
    obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
    exact IsPGroup.of_card
      (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPK).toEquiv]; exact hn)
  have hidx : ¬ p ∣ ((P : Subgroup G).subgroupOf K).index := fun h =>
    P.not_dvd_index (dvd_trans h (Subgroup.relIndex_dvd_index_of_le hPK))
  exact ⟨hpg.toSylow hidx, hpg.toSylow_coe hidx⟩

/-- **Converse of BG Lemma 4.5**: a finite `p`-group (`p` odd) of `p`-rank `≤ 1` is cyclic.
Contrapositive of `exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic` (a noncyclic odd
`p`-group has a rank-`2` elementary abelian subgroup, forcing `pRank ≥ 2`). Used in
Lemmas 10.4(b)/10.5 and §12 (Lemma 12.1: `E₁`, `E₃` and all rank-one Sylow subgroups of `E`
are cyclic). -/
theorem isCyclic_of_pRank_le_one {Q : Type*} [Group Q] [Finite Q] {p : ℕ}
    [Fact p.Prime] (hQ : IsPGroup p Q) (hodd : Odd p) (hr : pRank Q p ≤ 1) : IsCyclic Q := by
  by_contra hnc
  obtain ⟨E, hEea, hEcard⟩ :=
    OddOrder.BG.Ch1.S04.exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic hQ hodd hnc
  have hle : Nat.log p (Nat.card ↥E) ≤ pRank Q p := le_pRank E hEea
  rw [hEcard, Nat.log_pow (Fact.out : p.Prime).one_lt] at hle
  omega

/-- `N_G(P) ≤ N_G(Ω₁(Z(P)))` (`Z₀ = omega1CenterInG P p`): the inner `Ω₁(Z(↥P))` is
characteristic in `↥P` (the center is characteristic and `g ^ p = 1` is automorphism-stable),
so `AppB.normalizer_le_normalizer_map_of_characteristic` applies. Replicates the private
`CriticalSubgroup.omega1Center.characteristic`. Used in Lemmas 10.4(b) and 10.5. -/
theorem normalizer_le_normalizer_omega1CenterInG (P : Subgroup G) (p : ℕ) :
    Subgroup.normalizer (P : Set G) ≤
      Subgroup.normalizer ((omega1CenterInG P p : Subgroup G) : Set G) := by
  have hchar : (omega1OfAbelian ↥P (Subgroup.center ↥P) p
      (fun _ hx y _ => (Subgroup.mem_center_iff.mp hx y).symm)).Characteristic := by
    rw [Subgroup.characteristic_iff_comap_eq]
    intro φ
    have hcZ : ∀ g : ↥P, φ g ∈ Subgroup.center ↥P ↔ g ∈ Subgroup.center ↥P := by
      intro g
      rw [Subgroup.mem_center_iff, Subgroup.mem_center_iff]
      constructor
      · intro h h'
        have := h (φ h')
        rwa [← map_mul, ← map_mul, φ.injective.eq_iff] at this
      · intro h h'
        obtain ⟨h'', rfl⟩ := φ.surjective h'
        rw [← map_mul, ← map_mul, φ.injective.eq_iff]
        exact h h''
    ext g
    simp only [Subgroup.mem_comap, mem_omega1OfAbelian, MulEquiv.coe_toMonoidHom]
    rw [hcZ g]
    refine and_congr_right fun _ => ?_
    constructor
    · intro hpow
      have := congrArg φ.symm hpow
      rwa [map_pow, φ.symm_apply_apply, map_one] at this
    · intro hpow
      rw [← map_pow, hpow, map_one]
  exact OddOrder.BG.AppB.normalizer_le_normalizer_map_of_characteristic (K := P)
    (W := omega1OfAbelian ↥P (Subgroup.center ↥P) p
      (fun _ hx y _ => (Subgroup.mem_center_iff.mp hx y).symm))

/-- Every element of `Ω₁(Z(P))` (ambient form) has `p`-th power one. -/
theorem pow_eq_one_of_mem_omega1CenterInG {P : Subgroup G} {p : ℕ} {x : G}
    (hx : x ∈ omega1CenterInG P p) : x ^ p = 1 := by
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
  rw [← map_pow, (mem_omega1OfAbelian.mp hz).2, map_one]

/-- **BG Lemma 10.3** (mmd MISSING_PAGE, PDF p.74 = PDF page 87): `M ∈ ℳ`, `X` を `M` の
`α(M)'`-部分群とし `r(C_{M_α}(X)) ≥ 2` なら `C_M(X) ∈ 𝒰`。 -/
theorem centralizer_isUniquelyMaximal_of_two_le_rank [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {X : Subgroup G} (hXM : X ≤ M)
    (hXpi : Subgroup.IsPiSubgroup (alpha M)ᶜ X)
    (hr : 2 ≤ rank ↥(Subgroup.centralizer (X : Set G) ⊓ Malpha M)) :
    IsUniquelyMaximal (Subgroup.centralizer (X : Set G) ⊓ M) := by
  classical
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  have hMlt : M < ⊤ := lt_top_iff_ne_top.mpr (mem_maximalSubgroups.mp hM).1
  have hCMX_lt : Subgroup.centralizer (X : Set G) ⊓ M < ⊤ := lt_of_le_of_lt inf_le_right hMlt
  -- (1) some prime `p` realises `r_p(C_{M_α}(X)) ≥ 2`.
  obtain ⟨p, hp, hpr⟩ :=
    exists_pRank_ge_of_pos_le_rank (G := ↥(Subgroup.centralizer (X : Set G) ⊓ Malpha M))
      (n := 2) (by norm_num) hr
  have : Fact p.Prime := ⟨hp⟩
  -- (2) an elementary abelian `B ≤ C_{M_α}(X)` of `p`-rank ≥ 2.
  obtain ⟨B, hB_le, hBea, hBlog⟩ :
      ∃ B : Subgroup G, B ≤ Subgroup.centralizer (X : Set G) ⊓ Malpha M ∧
        B.IsElementaryAbelian p ∧ 2 ≤ Nat.log p (Nat.card ↥B) := by
    obtain ⟨E, hEea, hElog⟩ := exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank
      (G := ↥(Subgroup.centralizer (X : Set G) ⊓ Malpha M)) (n := 2) (by norm_num) hpr
    refine ⟨E.map (Subgroup.centralizer (X : Set G) ⊓ Malpha M).subtype,
      Subgroup.map_subtype_le _,
      hEea.map (Subgroup.centralizer (X : Set G) ⊓ Malpha M).subtype_injective, ?_⟩
    rwa [Subgroup.card_map_of_injective
      (Subgroup.centralizer (X : Set G) ⊓ Malpha M).subtype_injective]
  have hB_le_CGX : B ≤ Subgroup.centralizer (X : Set G) := hB_le.trans inf_le_left
  have hB_le_Ma : B ≤ Malpha M := hB_le.trans inf_le_right
  have hB_le_M : B ≤ M := hB_le_Ma.trans (Malpha_le M)
  -- `p ∈ α(M)` (it divides `|M_α|`, an `α(M)`-group), hence `r_p(M) ≥ 3`.
  have hpα : p ∈ alpha M := by
    obtain ⟨m, hm⟩ := hBea.isPGroup.exists_card_eq
    have hp_dvd_B : p ∣ Nat.card ↥B := by
      rw [hm]; exact dvd_pow_self p (by rw [hm, Nat.log_pow hp.one_lt] at hBlog; omega)
    exact Malpha_isPiGroup M p (Nat.mem_primeFactors.mpr
      ⟨hp, dvd_trans hp_dvd_B (Subgroup.card_dvd_of_le hB_le_Ma), Nat.card_pos.ne'⟩)
  -- (3) `X` normalizes a Sylow `p`-subgroup `P` of `M_α` containing `B` (Proposition 1.5),
  -- and `P` carries the full `p`-rank of `M` (`r(P) ≥ 3`).
  obtain ⟨P, hP_le_Ma, hP_pgrp, hX_norm_P, hB_le_P, hP_rank3⟩ :
      ∃ P : Subgroup G, P ≤ Malpha M ∧ IsPGroup p ↥P ∧
        X ≤ Subgroup.normalizer (P : Set G) ∧ B ≤ P ∧ 3 ≤ rank ↥P := by
    have : Group.IsSolvable ↥(Malpha M) :=
      Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe (Malpha_le M)).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe (Malpha_le M)).surjective
    have hX_norm_Ma : X ≤ Subgroup.normalizer (Malpha M : Set G) :=
      hXM.trans (le_normalizer_opiCoreInG (alpha M) M)
    have hcop : Nat.Coprime (Nat.card ↥X) (Nat.card ↥(Malpha M)) :=
      Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl (π := (alpha M)ᶜ)
        Nat.card_pos.ne' Nat.card_pos.ne' hXpi
        (fun q hq hqc => hqc (Malpha_isPiGroup M q hq))
    let act : MulDistribMulAction ↥X ↥(Malpha M) :=
      MulDistribMulAction.compHom (M := ↥(Subgroup.normalizer (Malpha M : Set G))) ↥(Malpha M)
        (Subgroup.inclusion hX_norm_Ma)
    set φ : ↥X →* MulAut ↥(Malpha M) := MulDistribMulAction.toMulAut ↥X ↥(Malpha M) with hφ
    have hφ_coe : ∀ (a : ↥X) (x : ↥(Malpha M)),
        ((Malpha M).subtype ((φ a) x)) = (↑a) * ((Malpha M).subtype x) * (↑a)⁻¹ := fun _ _ => rfl
    have hφ_inv_coe : ∀ (a : ↥X) (x : ↥(Malpha M)),
        ((Malpha M).subtype (((φ a)⁻¹) x)) = (↑a)⁻¹ * ((Malpha M).subtype x) * (↑a) := by
      intro a x
      rw [← map_inv]; simpa using hφ_coe a⁻¹ x
    have hBsub_pg : IsPGroup p ↥(B.subgroupOf (Malpha M)) := by
      obtain ⟨m, hm⟩ := hBea.isPGroup.exists_card_eq
      exact IsPGroup.of_card (n := m)
        (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB_le_Ma).toEquiv, hm])
    have hBsub_inv : Ch03.IsAInvariant φ (B.subgroupOf (Malpha M)) := by
      rw [Ch03.isAInvariant_iff_smul_mem]
      intro a x hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      change (Malpha M).subtype ((φ a) x) ∈ B
      rw [hφ_coe a x]
      have hcomm : (↑a : G) * (Malpha M).subtype x = (Malpha M).subtype x * ↑a :=
        (Subgroup.mem_centralizer_iff.mp (hB_le_CGX hx)) (↑a) a.2
      have heq : (↑a : G) * (Malpha M).subtype x * (↑a)⁻¹ = (Malpha M).subtype x := by
        rw [hcomm]; group
      rw [heq]; exact hx
    obtain ⟨S, hS_inv, hBS⟩ :=
      OddOrder.Isaacs.Ch04.aInvariant_pSubgroup_le_aInvariant_sylow (G := ↥(Malpha M)) (A := ↥X)
        (φ := φ) hcop (Or.inr inferInstance) hBsub_pg hBsub_inv
    set P : Subgroup G := (S : Subgroup ↥(Malpha M)).map (Malpha M).subtype with hPdef
    have hP_pgrp : IsPGroup p ↥P :=
      S.2.of_equiv (Subgroup.equivMapOfInjective _ _ (Malpha M).subtype_injective)
    have hX_norm_P : X ≤ Subgroup.normalizer (P : Set G) := by
      intro a ha
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨x, hxS, rfl⟩
        exact ⟨(φ ⟨a, ha⟩) x, hS_inv.smul_mem ⟨a, ha⟩ hxS, hφ_coe ⟨a, ha⟩ x⟩
      · rintro ⟨x, hxS, hx⟩
        refine ⟨((φ ⟨a, ha⟩)⁻¹) x, hS_inv.inv_smul_mem ⟨a, ha⟩ hxS, ?_⟩
        rw [hφ_inv_coe ⟨a, ha⟩ x, hx]
        change a⁻¹ * (a * y * a⁻¹) * a = y
        group
    have hB_le_P : B ≤ P := by
      rw [hPdef, ← Subgroup.map_subgroupOf_eq_of_le hB_le_Ma]
      exact Subgroup.map_mono hBS
    -- `pRank ↥M p ≤ pRank ↥P p`: `P` is a Sylow `p` of `M_α`, which (as `p ∈ α`) contains a
    -- full Sylow `p` of `M`.
    have eP : ↥(S : Subgroup ↥(Malpha M)) ≃* ↥P :=
      hPdef ▸ Subgroup.equivMapOfInjective _ (Malpha M).subtype (Malpha M).subtype_injective
    have hPpr : pRank ↥M p ≤ pRank ↥P p := by
      have h1 : pRank ↥(S : Subgroup ↥(Malpha M)) p ≤ pRank ↥P p :=
        pRank_le_of_injective (f := eP.toMonoidHom) eP.injective
      rw [pRank_sylow_eq S] at h1
      obtain ⟨T⟩ : Nonempty (Sylow p ↥M) := inferInstance
      have hTle : ((T : Subgroup ↥M).map M.subtype) ≤ Malpha M :=
        sylow_le_Malpha_of_mem_alpha_of_isHall (Malpha_isHall hG hM) hpα T
      have eT : ↥(T : Subgroup ↥M) ≃* ↥((T : Subgroup ↥M).map M.subtype) :=
        Subgroup.equivMapOfInjective _ M.subtype M.subtype_injective
      have hTeq : pRank ↥M p = pRank ↥((T : Subgroup ↥M).map M.subtype) p := by
        rw [← pRank_sylow_eq T]
        exact le_antisymm (pRank_le_of_injective (f := eT.toMonoidHom) eT.injective)
          (pRank_le_of_injective (f := eT.symm.toMonoidHom) eT.symm.injective)
      have hTpr : pRank ↥((T : Subgroup ↥M).map M.subtype) p ≤ pRank ↥(Malpha M) p :=
        pRank_le_of_injective (f := Subgroup.inclusion hTle) (Subgroup.inclusion_injective hTle)
      omega
    refine ⟨P, Subgroup.map_subtype_le _, hP_pgrp, hX_norm_P, hB_le_P, ?_⟩
    exact le_trans (le_trans ((mem_alpha_iff M p).mp hpα).2 hPpr) (pRank_le_rank p)
  -- (4) if `B ∈ 𝒰` we are done immediately (`B ≤ C_M(X) < ⊤`).
  by_cases hBU : IsUniquelyMaximal B
  · exact hBU.of_le_of_lt_top (le_inf hB_le_CGX hB_le_M) hCMX_lt
  -- (5) otherwise `r(C_P(B)) ≤ 2` by the Uniqueness Theorem: were `r(C_P(B)) ≥ 3`, then
  -- `C_P(B) ∈ 𝒰`, and `B ≤ C_G(C_P(B))` with `r(B) = 2` would force `B ∈ 𝒰`.
  have hrankB : 2 ≤ rank ↥B :=
    le_trans (le_trans hBlog hBea.log_card_le_pRank) (pRank_le_rank p)
  have hCPB_rank : rank ↥(Subgroup.centralizer (B : Set G) ⊓ P) ≤ 2 := by
    by_contra hcon
    push Not at hcon
    have hCPB_lt : Subgroup.centralizer (B : Set G) ⊓ P < ⊤ :=
      lt_of_le_of_lt (inf_le_right.trans (hP_le_Ma.trans (Malpha_le M))) hMlt
    have hCPB_U : IsUniquelyMaximal (Subgroup.centralizer (B : Set G) ⊓ P) :=
      OddOrder.BG.Ch2.S09.isUniquelyMaximal_of_three_le_rank_of_lt_top hG hCPB_lt (by omega)
    have hB_le_cent : B ≤ Subgroup.centralizer
        ((Subgroup.centralizer (B : Set G) ⊓ P : Subgroup G) : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (Subgroup.mem_centralizer_iff.mp hy.1 x hx).symm
    exact hBU (OddOrder.BG.Ch2.S09.isUniquelyMaximal_of_le_centralizer_of_two_le_rank
      hG hCPB_U hB_le_cent hrankB)
  -- `|B| = p²`: `r(B) ≤ r(C_P(B)) ≤ 2` and `log_p|B| ≥ 2`.
  have hB_le_CB : B ≤ Subgroup.centralizer (B : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (hBea.1 ⟨y, hy⟩ ⟨x, hx⟩)
  have hB_le_CPB : B ≤ Subgroup.centralizer (B : Set G) ⊓ P := le_inf hB_le_CB hB_le_P
  have hBcard : Nat.card ↥B = p ^ 2 := by
    have hrB : rank ↥B ≤ 2 :=
      le_trans (rank_le_of_injective (Subgroup.inclusion_injective hB_le_CPB)) hCPB_rank
    have hlog_eq : Nat.log p (Nat.card ↥B) = 2 :=
      le_antisymm (le_trans (le_trans hBea.log_card_le_pRank (pRank_le_rank p)) hrB) hBlog
    obtain ⟨m, hm⟩ := hBea.isPGroup.exists_card_eq
    rw [hm, Nat.log_pow hp.one_lt] at hlog_eq
    rw [hm, hlog_eq]
  -- (6) every order-`p` element of `C_P(B)` lies in `B`: otherwise `B ⊔ ⟨g⟩` is elementary
  -- abelian of order `> p²` inside `C_P(B)`, forcing `r(C_P(B)) ≥ 3`, contrary to (5).
  have hOmega : ∀ g : G, g ∈ Subgroup.centralizer (B : Set G) ⊓ P → g ^ p = 1 → g ∈ B := by
    intro g hg hgp
    by_contra hgB
    have hg_ne : g ≠ 1 := by rintro rfl; exact hgB (one_mem B)
    have hord : orderOf g = p := orderOf_eq_prime hgp hg_ne
    have hzg_ea : (Subgroup.zpowers g).IsElementaryAbelian p :=
      Subgroup.IsElementaryAbelian.of_card_prime (by rw [Nat.card_zpowers, hord])
    have hB_cent : B ≤ Subgroup.centralizer (Subgroup.zpowers g : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hc : Commute g x := (Subgroup.mem_centralizer_iff.mp hg.1 x hx).symm
      exact hc.zpow_left k
    set A' : Subgroup G := B ⊔ Subgroup.zpowers g with hA'def
    have hA'ea : A'.IsElementaryAbelian p := hBea.sup_of_le_centralizer hzg_ea hB_cent
    have hA'le : A' ≤ Subgroup.centralizer (B : Set G) ⊓ P := by
      refine sup_le (le_inf ?_ hB_le_P) (le_inf (Subgroup.zpowers_le.mpr hg.1)
        (Subgroup.zpowers_le.mpr hg.2))
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (congrArg Subtype.val (hBea.1 ⟨y, hy⟩ ⟨x, hx⟩))
    have hlt : B < A' := by
      refine lt_of_le_of_ne le_sup_left (fun h => hgB ?_)
      have hgA' : g ∈ A' := Subgroup.mem_sup_right (Subgroup.mem_zpowers g)
      rwa [← h] at hgA'
    -- `|A'| ≥ p³`, so `pRank (C_P(B)) ≥ 3`, contradicting `rank (C_P(B)) ≤ 2`.
    obtain ⟨k, hk⟩ := hA'ea.isPGroup.exists_card_eq
    have hk3 : 3 ≤ k := by
      have hdvd : Nat.card ↥B ∣ Nat.card ↥A' := Subgroup.card_dvd_of_le le_sup_left
      have hne : Nat.card ↥B ≠ Nat.card ↥A' := fun heq =>
        (ne_of_lt hlt) (Subgroup.eq_of_le_of_card_ge le_sup_left (le_of_eq heq.symm))
      have hgt : p ^ 2 < p ^ k := by
        rw [← hBcard, ← hk]
        exact lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos hdvd) hne
      have := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hgt
      omega
    have hsub_ea : (A'.subgroupOf (Subgroup.centralizer (B : Set G) ⊓ P)).IsElementaryAbelian p :=
      IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hA'le).symm hA'ea
    have hle := le_pRank (A'.subgroupOf (Subgroup.centralizer (B : Set G) ⊓ P)) hsub_ea
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA'le).toEquiv, hk,
      Nat.log_pow hp.one_lt] at hle
    have hpr := pRank_le_rank (G := ↥(Subgroup.centralizer (B : Set G) ⊓ P)) p
    omega
  -- (7)(8) `X` centralises `P` (Corollary 1.12 with `E = B`): `X` fixes every order-`p`
  -- element of `C_P(B)` (these all lie in `B ⊆ C_G(X)` by step (6)), so `X` acts trivially on `P`.
  have hCPX : P ≤ Subgroup.centralizer (X : Set G) := by
    have hp_dvd_M : p ∣ Nat.card ↥M := (Nat.mem_primeFactors.mp ((mem_alpha_iff M p).mp hpα).1).2.1
    have hpodd : Odd p := hG.odd.of_dvd_nat (dvd_trans hp_dvd_M (Subgroup.card_subgroup_dvd_card M))
    have hp_ne2 : p ≠ 2 := by rintro rfl; exact (Nat.not_odd_iff_even.mpr even_two) hpodd
    have hX_p' : ¬ p ∣ Nat.card ↥X := fun hdvd =>
      (hXpi p (Nat.mem_primeFactors.mpr ⟨hp, hdvd, Nat.card_pos.ne'⟩)) hpα
    let act : MulDistribMulAction ↥X ↥P :=
      MulDistribMulAction.compHom (M := ↥(Subgroup.normalizer (P : Set G))) ↥P
        (Subgroup.inclusion hX_norm_P)
    set ψ : ↥X →* MulAut ↥P := MulDistribMulAction.toMulAut ↥X ↥P with hψ
    have hψ_coe : ∀ (a : ↥X) (x : ↥P), (↑((ψ a) x) : G) = (↑a) * (↑x : G) * (↑a)⁻¹ :=
      fun _ _ => rfl
    have hE_ea : (B.subgroupOf P).IsElementaryAbelian p :=
      IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hB_le_P).symm hBea
    have hfix : ∀ a : ↥X, ∀ g : ↥P,
        g ∈ Subgroup.centralizer ((B.subgroupOf P : Subgroup ↥P) : Set ↥P) →
        g ^ p = 1 → (ψ a) g = g := by
      intro a g hg hgp
      apply Subtype.ext
      rw [hψ_coe a g]
      have hgB : (↑g : G) ∈ B := by
        refine hOmega (↑g : G) (Subgroup.mem_inf.mpr ⟨?_, g.2⟩) ?_
        · rw [Subgroup.mem_centralizer_iff]
          intro b hb
          exact congrArg Subtype.val
            (Subgroup.mem_centralizer_iff.mp hg ⟨b, hB_le_P hb⟩ (Subgroup.mem_subgroupOf.mpr hb))
        · have h := congrArg Subtype.val hgp
          rwa [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h
      have hcomm := (Subgroup.mem_centralizer_iff.mp (hB_le_CGX hgB)) (↑a) a.2
      rw [hcomm]; group
    have htriv := OddOrder.BG.Ch1.S01.actsTrivially_of_fixes_omega1_centralizer
      hp_ne2 hP_pgrp hX_p' ψ hE_ea hfix
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h2 := congrArg Subtype.val (htriv ⟨x, hx⟩ ⟨y, hy⟩)
    rw [hψ_coe ⟨x, hx⟩ ⟨y, hy⟩] at h2
    exact (mul_inv_eq_iff_eq_mul.mp h2)
  -- (9) hence `r(C_M(X)) ≥ r(P) ≥ 3` (since `p ∈ α(M)`).
  have hr3 : 3 ≤ rank ↥(Subgroup.centralizer (X : Set G) ⊓ M) := by
    have hP_le : P ≤ Subgroup.centralizer (X : Set G) ⊓ M :=
      le_inf hCPX (hP_le_Ma.trans (Malpha_le M))
    exact le_trans hP_rank3 (rank_le_of_injective (Subgroup.inclusion_injective hP_le))
  -- (10) the Uniqueness Theorem gives `C_M(X) ∈ 𝒰`.
  exact OddOrder.BG.Ch2.S09.isUniquelyMaximal_of_three_le_rank_of_lt_top hG hCMX_lt hr3

/-- **BG Lemma 10.4 (a)(c)** (mmd MISSING_PAGE, PDF p.74 = PDF page 87; recovered 2026-06-07):
`M ∈ ℳ`。(a) `p ∣ |M/M'|` ⇒ `p ∉ σ(M)`; (c) `p ∉ σ(M)`, `r_p(M) = 2` ⇒ `p` は ideal でなく、
`M` の位数 `p²` elem-ab はすべて `G` の極大 elem-ab (`ℰ_p²(M) ⊆ ℰ_p*(G)`)。

**注意**: 旧 scaffold は (a) を `p ∉ α(M)` (弱い) に、(c) の仮定を `p ∈ α(M)` (⇒ `pRank ≥ 3`
で `pRank = 2` と矛盾 = vacuous) に誤記していた。原典 Lemma 10.4 に合わせ `σ(M)` 版へ修正
(downstream 未使用を確認済)。原典 (b) は `exists_mem_omega1_center_zgroupCentralizer`。 -/
theorem alpha_criterion [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    (∀ p : ℕ, p.Prime → p ∣ (commutator ↥M).index → p ∉ sigma M) ∧
    (∀ p : ℕ, p.Prime → p ∉ sigma M → pRank ↥M p = 2 →
      ¬ idealPrime p G ∧
      ∀ A : Subgroup G, A ≤ M → A ∈ elemAbelianOfRank G p 2 →
        IsMaximalElementaryAbelian p A) := by
  refine ⟨fun p hp hdvd hpσ => ?_, fun p hp hpσ hr2 => ?_⟩
  · -- (a) `p ∣ |M/M'|` and `p ∈ σ(M)` are contradictory: a Sylow `p` of `M` lies in `M'`.
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨P, -⟩ := hpσ.2
    have hPder : (P : Subgroup ↥M) ≤ commutator ↥M := by
      have h := sylow_le_derived_of_mem_sigma hG hM hpσ P
      rwa [derivedInG, Subgroup.map_le_map_iff_of_injective M.subtype_injective] at h
    exact P.not_dvd_index (dvd_trans hdvd (Subgroup.index_dvd_of_le hPder))
  · -- (c)
    have : Fact p.Prime := ⟨hp⟩
    -- ∀-part: a rank-`2` elementary abelian `A ≤ M` is `G`-maximal
    -- (else `A ∈ 𝒰` forces `p ∈ σ(M)`).
    have hmax : ∀ A : Subgroup G, A ≤ M → A ∈ elemAbelianOfRank G p 2 →
        IsMaximalElementaryAbelian p A := by
      intro A hAM hA2
      by_contra hAns
      have hAU := OddOrder.BG.Ch2.S09.isUniquelyMaximal_of_mem_e2_not_maximal hG hA2 hAns
      obtain ⟨PG, hAPG⟩ := hA2.1.isPGroup.exists_le_sylow
      have hAne : A ≠ ⊥ := by
        intro hb
        have h1 : Nat.card ↥A = 1 := by rw [hb]; exact Subgroup.card_bot
        rw [hA2.2] at h1
        exact hp.ne_one ((Nat.pow_eq_one.mp h1).resolve_right two_ne_zero)
      have hPGne : (PG : Subgroup G) ≠ ⊥ := fun hb => hAne (le_bot_iff.mp (hAPG.trans_eq hb))
      have hNlt : Subgroup.normalizer ((PG : Subgroup G) : Set G) < ⊤ := by
        rw [lt_top_iff_ne_top]
        intro htop
        have hPGnormal : (PG : Subgroup G).Normal := Subgroup.normalizer_eq_top_iff.mp htop
        rcases hG.simple.eq_bot_or_eq_top_of_normal _ hPGnormal with hbot | htop'
        · exact hPGne hbot
        · have hsolv : Group.IsSolvable ↥(PG : Subgroup G) := by
            have := (PG.isPGroup').isNilpotent; infer_instance
          rw [htop'] at hsolv
          have := hsolv
          exact hG.notSolvable (Group.isSolvable_of_surjective
            (f := (Subgroup.topEquiv (G := G)).toMonoidHom) (Subgroup.topEquiv (G := G)).surjective)
      have hAN : A ≤ Subgroup.normalizer ((PG : Subgroup G) : Set G) :=
        hAPG.trans Subgroup.le_normalizer
      obtain ⟨K, hKco, hNK⟩ :=
        (eq_top_or_exists_le_coatom (Subgroup.normalizer ((PG : Subgroup G) : Set G))).resolve_left
          hNlt.ne
      have hNM : Subgroup.normalizer ((PG : Subgroup G) : Set G) ≤ M := by
        have hKeqM : K = M :=
          (hAU.eq_uniqueMaximalSubgroup_of_isCoatom_of_le hKco (hAN.trans hNK)).trans
            (hAU.eq_uniqueMaximalSubgroup_of_isCoatom_of_le (mem_maximalSubgroups.mp hM) hAM).symm
        exact hKeqM ▸ hNK
      have hPGM : (PG : Subgroup G) ≤ M := Subgroup.le_normalizer.trans hNM
      apply hpσ
      rw [mem_sigma_iff]
      refine ⟨Nat.mem_primeFactors.mpr ⟨hp, ?_, Nat.card_pos.ne'⟩, ?_⟩
      · exact dvd_trans (by rw [hA2.2]; exact dvd_pow_self p two_ne_zero)
          ((Subgroup.card_dvd_of_le hAM))
      · obtain ⟨Q, hQ⟩ := sylow_subgroupOf_of_le PG hPGM
        exact ⟨Q, by rw [hQ, Subgroup.map_subgroupOf_eq_of_le hPGM]; exact hNM⟩
    refine ⟨?_, hmax⟩
    -- `¬ idealPrime`: `r_p(M) = 2` gives `A ∈ ℰ_p²(M)`, maximal by `hmax` — a non-ideality witness.
    intro hideal
    obtain ⟨A0, hA0ea, hA0log⟩ :=
      exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank (G := ↥M) (p := p) (n := 2)
        (by norm_num) (le_of_eq hr2.symm)
    have hA0card : Nat.card ↥A0 = p ^ 2 := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA0ea.isPGroup
      have hlog : Nat.log p (Nat.card ↥A0) = k := by
        rw [hk, Nat.log_pow (Fact.out : p.Prime).one_lt]
      have hle : Nat.log p (Nat.card ↥A0) ≤ pRank ↥M p := le_pRank A0 hA0ea
      rw [hr2, hlog] at hle
      rw [hlog] at hA0log
      rw [hk, le_antisymm hle hA0log]
    set A : Subgroup G := A0.map M.subtype with hAdef
    have hAea : A.IsElementaryAbelian p := hA0ea.map M.subtype_injective
    have hAcard : Nat.card ↥A = p ^ 2 := by
      rw [hAdef, Subgroup.card_map_of_injective M.subtype_injective]; exact hA0card
    have hAM : A ≤ M := Subgroup.map_subtype_le _
    have hAmax : IsMaximalElementaryAbelian p A := hmax A hAM ⟨hAea, hAcard⟩
    obtain ⟨PG, hAPG⟩ := hAea.isPGroup.exists_le_sylow
    refine hideal.2 PG ⟨A.subgroupOf PG, ?_, ?_, ?_⟩
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAPG).toEquiv]; exact hAcard
    · exact IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAPG).symm hAea
    · intro F hFea hFle
      have hmapF : F.map (PG : Subgroup G).subtype = A := by
        refine hAmax.2 _ (hFea.map (PG : Subgroup G).subtype_injective) ?_
        rw [← Subgroup.map_subgroupOf_eq_of_le hAPG]
        exact Subgroup.map_mono hFle
      have hF_eq : F = (F.map (PG : Subgroup G).subtype).subgroupOf (PG : Subgroup G) := by
        rw [Subgroup.subgroupOf,
          Subgroup.comap_map_eq_self_of_injective (PG : Subgroup G).subtype_injective]
      rw [hF_eq, hmapF]

/-- The pointwise action of a `MulAut` on a subgroup is its image (replicates the private
`mulAut_smul_eq_map` of the BG `Ch1`/`Ch2` files). -/
private theorem conjSmul_eq_map (φ : MulAut G) (H : Subgroup G) :
    φ • H = H.map (φ : G →* G) := by rw [Subgroup.pointwise_smul_def]; rfl

/-- A finite group of odd order that is not a `Z`-group has rank `≥ 2` (its noncyclic Sylow
`r`-subgroup contains a rank-`2` elementary abelian subgroup). Abstract core of the
"Lemma 10.3 upgrade" step in Lemma 10.4(b). -/
private theorem two_le_rank_of_not_isZGroup {H : Type*} [Group H] [Finite H]
    (hodd : Odd (Nat.card H)) (hZ : ¬ _root_.IsZGroup H) : 2 ≤ rank H := by
  rw [isZGroup_iff] at hZ
  push Not at hZ
  obtain ⟨r, hr, R, hRnc⟩ := hZ
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨k, hk⟩ := R.isPGroup'.exists_card_eq
  have hk1 : k ≠ 0 := by
    intro h0
    apply hRnc
    have : Subsingleton ↥(R : Subgroup H) := by
      have h1 : Nat.card ↥(R : Subgroup H) = 1 := by rw [hk, h0, pow_zero]
      exact (Nat.card_eq_one_iff_unique.mp h1).1
    infer_instance
  have hr_dvd : r ∣ Nat.card H :=
    (dvd_pow_self r hk1).trans (hk ▸ Subgroup.card_subgroup_dvd_card (R : Subgroup H))
  have hrodd : Odd r := hodd.of_dvd_nat hr_dvd
  refine le_trans ?_ (pRank_le_rank r)
  by_contra hcon
  push Not at hcon
  exact hRnc (isCyclic_of_pRank_le_one R.isPGroup' hrodd
    (le_trans (pRank_le_of_injective (Subgroup.subtype_injective _)) (by omega)))

/-- **BG Lemma 10.4(b)** (mmd MISSING_PAGE, PDF p.74 = PDF page 87; recovered 2026-06-08):
`M ∈ ℳ`, `p ∈ π(M)`, `P` を `M` の Sylow `p`-部分群とし、`p ∉ σ(M)` かつ `M_α ≠ 1` とする。
このとき `x ∈ Ω₁(Z(P))^#` が存在して `{M} ≠ ℳ(C_G(x))` かつ `C_{M_α}(x)` は Z-群。

`{M} ≠ ℳ(C_G(x))` は正値に「`C_G(⟨x⟩)` を含む極大部分群 `L ≠ M` が存在する」とエンコード
(`ℳ(C_G(x)) ≠ ∅` ゆえ同値)。中心化群は `⟨x⟩ = zpowers x` 形で、BG Theorem 3.6
(`pLengthOne_commutator_of_zgroupCentralizer`) の `R₀`-interface と揃える。

証明 (BG p.74): 反例とする。`p ∉ σ(M)` より `u ∈ N_G(P) − M` が取れる。任意の
`y ∈ Ω₁(Z(P))^#` に対し反例仮定から「`C_{M_α}(y)` が Z-群でないか `{M} = ℳ(C_G(y))`」;
前者は Lemma 10.3 (`X = ⟨y⟩`, noncyclic Sylow ⟹ `r(C_{M_α}(y)) ≥ 2`) により後者へ昇格する。
これを `y` と `u y u⁻¹ ∈ Ω₁(Z(P))^#` に適用し共役で移すと `u⁻¹ M u = M`、つまり
`u ∈ N_G(M) = M` となり `u` の取り方に矛盾。 -/
theorem exists_mem_omega1_center_zgroupCentralizer [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime]
    (hpM : p ∈ (Nat.card ↥M).primeFactors) (hpσ : p ∉ sigma M) (hMα : Malpha M ≠ ⊥)
    (P : Sylow p ↥M) :
    ∃ x ∈ omega1CenterInG ((P : Subgroup ↥M).map M.subtype) p, x ≠ 1 ∧
      (∃ L ∈ maximalSubgroups G,
        Subgroup.centralizer (↑(Subgroup.zpowers x) : Set G) ≤ L ∧ L ≠ M) ∧
      _root_.IsZGroup ↥(Subgroup.centralizer (↑(Subgroup.zpowers x) : Set G) ⊓ Malpha M) := by
  classical
  set PG : Subgroup G := (P : Subgroup ↥M).map M.subtype with hPGdef
  by_contra hcon
  push Not at hcon
  -- Step 1: every `y ∈ Ω₁(Z(P))^#` has `M` as the *unique* maximal subgroup over `C_G(⟨y⟩)`.
  have key : ∀ y ∈ omega1CenterInG PG p, y ≠ 1 →
      ∀ L ∈ maximalSubgroups G,
        Subgroup.centralizer (↑(Subgroup.zpowers y) : Set G) ≤ L → L = M := by
    intro y hyΩ hy1
    have hyM : y ∈ M := Subgroup.map_subtype_le _ (omega1CenterInG_le PG p hyΩ)
    have hord : orderOf y = p :=
      orderOf_eq_prime (pow_eq_one_of_mem_omega1CenterInG hyΩ) hy1
    by_cases hZ : _root_.IsZGroup
        ↥(Subgroup.centralizer (↑(Subgroup.zpowers y) : Set G) ⊓ Malpha M)
    · -- Z-group case: the counterexample assumption denies any second maximal subgroup.
      intro L hL hCL
      by_contra hLM
      exact hcon y hyΩ hy1 ⟨L, hL, hCL, hLM⟩ hZ
    · -- non-Z-group case: a noncyclic Sylow `r`-subgroup forces `r(C_{M_α}(⟨y⟩)) ≥ 2`,
      -- and Lemma 10.3 makes `C_M(⟨y⟩)` uniquely maximal.
      have hC_le_M : Subgroup.centralizer (↑(Subgroup.zpowers y) : Set G) ⊓ Malpha M ≤ M :=
        inf_le_right.trans (Malpha_le M)
      have hCodd : Odd (Nat.card
          ↥(Subgroup.centralizer (↑(Subgroup.zpowers y) : Set G) ⊓ Malpha M)) :=
        hG.odd.of_dvd_nat
          ((Subgroup.card_dvd_of_le hC_le_M).trans (Subgroup.card_subgroup_dvd_card M))
      have h2 : 2 ≤ rank
          ↥(Subgroup.centralizer (↑(Subgroup.zpowers y) : Set G) ⊓ Malpha M) :=
        two_le_rank_of_not_isZGroup hCodd hZ
      have hUM := centralizer_isUniquelyMaximal_of_two_le_rank hG hM
        (X := Subgroup.zpowers y) (Subgroup.zpowers_le.mpr hyM)
        (fun s hs => by
          rw [Nat.card_zpowers, hord] at hs
          obtain ⟨hsp, hsd, -⟩ := Nat.mem_primeFactors.mp hs
          have hsP : s = p := (Nat.prime_dvd_prime_iff_eq hsp Fact.out).mp hsd
          subst hsP
          exact fun hsα => hpσ (alpha_subset_sigma hG hM hsα))
        h2
      intro L hL hCL
      exact hUM.eq_of_isCoatom_of_le (mem_maximalSubgroups.mp hL)
        (le_trans inf_le_left hCL) (mem_maximalSubgroups.mp hM) inf_le_right
  -- Step 2: `p ∉ σ(M)` supplies `u ∈ N_G(P) − M`.
  have hNP_not_le : ¬ Subgroup.normalizer (PG : Set G) ≤ M := by
    intro hle
    exact hpσ ⟨hpM, P, by rw [← hPGdef]; exact hle⟩
  obtain ⟨u, huN, huM⟩ := SetLike.not_le_iff_exists.mp hNP_not_le
  -- Step 3: `Ω₁(Z(P))^#` is nonempty (the `p`-group `P` is nontrivial since `p ∈ π(M)`).
  have hp_dvd_P : p ∣ Nat.card ↥(P : Subgroup ↥M) := by
    have hdvd : p ∣ Nat.card ↥(P : Subgroup ↥M) * (P : Subgroup ↥M).index := by
      rw [Subgroup.card_mul_index]
      exact (Nat.mem_primeFactors.mp hpM).2.1
    rcases (Nat.Prime.dvd_mul Fact.out).mp hdvd with h | h
    · exact h
    · exact absurd h P.not_dvd_index
  have hPG_pg : IsPGroup p ↥PG :=
    P.isPGroup'.of_equiv (Subgroup.equivMapOfInjective _ M.subtype M.subtype_injective)
  have : Nontrivial ↥PG := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    calc 1 < p := (Fact.out : p.Prime).one_lt
      _ ≤ Nat.card ↥(P : Subgroup ↥M) := Nat.le_of_dvd Nat.card_pos hp_dvd_P
      _ = Nat.card ↥PG := by
          rw [hPGdef, Subgroup.card_map_of_injective M.subtype_injective]
  obtain ⟨z, -, hzc, hz1, hzp⟩ :=
    exists_mem_omega1_center_of_normal_ne_bot hPG_pg (N := ⊤) top_ne_bot
  have hyΩ : (z : G) ∈ omega1CenterInG PG p :=
    Subgroup.mem_map.mpr ⟨z, mem_omega1OfAbelian.mpr ⟨hzc, hzp⟩, rfl⟩
  have hy1 : (z : G) ≠ 1 := fun h => hz1 (OneMemClass.coe_eq_one.mp h)
  -- Step 4: conjugate by `u` and apply `key` to both `y = ↑z` and `y' = u y u⁻¹`.
  have huNZ : u ∈ Subgroup.normalizer ((omega1CenterInG PG p : Subgroup G) : Set G) :=
    normalizer_le_normalizer_omega1CenterInG PG p huN
  have hy'Ω : u * (z : G) * u⁻¹ ∈ omega1CenterInG PG p :=
    (Subgroup.mem_normalizer_iff.mp huNZ (z : G)).mp hyΩ
  have hy'1 : u * (z : G) * u⁻¹ ≠ 1 := by
    intro h
    apply hy1
    have h2 : u * (z : G) * u⁻¹ = u * 1 * u⁻¹ := by rw [h]; group
    exact mul_left_cancel (mul_right_cancel h2)
  -- The centralizer of `⟨y'⟩` is proper (the center of the simple nonabelian `G` is trivial).
  have hcenter : Subgroup.center G = ⊥ := by
    rcases hG.simple.eq_bot_or_eq_top_of_normal (Subgroup.center G) inferInstance with h | h
    · exact h
    · exfalso
      refine hG.notSolvable (Group.isSolvable_of_comm fun a b => ?_)
      exact (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm
  have hCy'_lt : Subgroup.centralizer
      (↑(Subgroup.zpowers (u * (z : G) * u⁻¹)) : Set G) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hy'1
    have hy'c : u * (z : G) * u⁻¹ ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact (Subgroup.mem_centralizer_iff.mp (htop ▸ Subgroup.mem_top g) _
        (Subgroup.mem_zpowers _)).symm
    rwa [hcenter, Subgroup.mem_bot] at hy'c
  -- `C_G(⟨y'⟩) ≤ M` via `key` at `y'`.
  obtain ⟨L₀, hL₀co, hCy'L₀⟩ :=
    (eq_top_or_exists_le_coatom
      (Subgroup.centralizer (↑(Subgroup.zpowers (u * (z : G) * u⁻¹)) : Set G))).resolve_left
      hCy'_lt.ne
  have hCy'_le_M : Subgroup.centralizer
      (↑(Subgroup.zpowers (u * (z : G) * u⁻¹)) : Set G) ≤ M := by
    have hL₀M : L₀ = M :=
      key _ hy'Ω hy'1 L₀ (mem_maximalSubgroups.mpr hL₀co) hCy'L₀
    exact hL₀M ▸ hCy'L₀
  -- Transfer: `C_G(⟨y⟩) ≤ u⁻¹ M u`.
  have hCy_le : Subgroup.centralizer (↑(Subgroup.zpowers (z : G)) : Set G) ≤
      MulAut.conj u⁻¹ • M := by
    intro c hc
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have hsmul : (MulAut.conj u⁻¹)⁻¹ • c = u * c * u⁻¹ := by
      rw [map_inv, inv_inv]; rfl
    rw [hsmul]
    apply hCy'_le_M
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    have hyc : (z : G) ^ k * c = c * (z : G) ^ k :=
      Subgroup.mem_centralizer_iff.mp hc ((z : G) ^ k)
        (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k)
    rw [conj_zpow]
    calc u * (z : G) ^ k * u⁻¹ * (u * c * u⁻¹)
        = u * ((z : G) ^ k * c) * u⁻¹ := by group
      _ = u * (c * (z : G) ^ k) * u⁻¹ := by rw [hyc]
      _ = u * c * u⁻¹ * (u * (z : G) ^ k * u⁻¹) := by group
  -- `u⁻¹ M u` is maximal and contains `C_G(⟨y⟩)`, so it equals `M` by `key` at `y`.
  have hL₁co : IsCoatom (MulAut.conj u⁻¹ • M) := by
    rw [conjSmul_eq_map]
    exact (OrderIso.isCoatom_iff ((MulAut.conj u⁻¹).mapSubgroup) M).mpr
      (mem_maximalSubgroups.mp hM)
  have hL₁M : MulAut.conj u⁻¹ • M = M :=
    key _ hyΩ hy1 _ (mem_maximalSubgroups.mpr hL₁co) hCy_le
  -- Hence `u ∈ N_G(M) = M`, contradicting the choice of `u`.
  have huNM : u ∈ Subgroup.normalizer (M : Set G) := by
    apply mem_normalizer_of_conj_smul_eq_self
    calc MulAut.conj u • M = MulAut.conj u • (MulAut.conj u⁻¹ • M) := by rw [hL₁M]
      _ = M := by rw [map_inv, smul_inv_smul]
  rcases eq_or_lt_of_le (Subgroup.le_normalizer (H := M)) with heq | hlt
  · rw [← heq] at huNM
    exact huM huNM
  · have hnorm : M.Normal := Subgroup.normalizer_eq_top_iff.mp
      ((mem_maximalSubgroups.mp hM).2 _ hlt)
    rcases hG.simple.eq_bot_or_eq_top_of_normal M hnorm with hbot | htop
    · exact hMα (le_bot_iff.mp (hbot ▸ Malpha_le M))
    · exact (mem_maximalSubgroups.mp hM).1 htop

/-- `C_{↥M}(⟨x⟩) ⊓ H.subgroupOf M = (C_G(⟨↑x⟩) ⊓ H).subgroupOf M` for `H ≤ M`: the
centralizer of a cyclic subgroup generated inside `↥M` agrees with the ambient one. Used to
translate the conclusion of Lemma 10.4(b) into the `↥M`-coordinates of
`exists_prime_orderOf_zgroupCentralizer_of_complement`. -/
theorem centralizer_zpowers_inf_subgroupOf_eq (M : Subgroup G) {H : Subgroup G} (x : ↥M) :
    Subgroup.centralizer (↑(Subgroup.zpowers x) : Set ↥M) ⊓ H.subgroupOf M
      = (Subgroup.centralizer (↑(Subgroup.zpowers (x : G)) : Set G) ⊓ H).subgroupOf M := by
  ext m
  simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨hc, hH⟩
    refine ⟨fun h hh => ?_, hH⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    have := hc (x ^ k) (Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) k)
    have hcoe := congrArg (Subtype.val : ↥M → G) this
    simpa [SubgroupClass.coe_zpow] using hcoe
  · rintro ⟨hc, hH⟩
    refine ⟨fun h hh => ?_, hH⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    have := hc ((x : G) ^ k) (Subgroup.zpow_mem _ (Subgroup.mem_zpowers (x : G)) k)
    apply Subtype.ext
    simpa [SubgroupClass.coe_zpow] using this

end OddOrder.BG.Ch3.S10


