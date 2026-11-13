-- Prove2me | Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_Lemma1217
-- name    : OddOrder_BG_Ch3_MaximalSubgroups_S12_Lemma1217
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T08:16:19.194527+00:00
-- url     : https://prove2.me/theorems/f049e003-bc5d-4168-84d5-3e68d544cebb
-- title:
--   BG §12: Lemma 12.17, third clause ($M_\sigma\cap M^g$ is a $\beta(M)'$-group)
-- statement:
--   Adds the third clause of Lemma 12.17 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §12, to the first two clauses ($C_{M_\sigma}(E)\subseteq M_\sigma'$ and $[M_\sigma,E]=M_\sigma$) proved elsewhere: for $g\in G-M$, every prime dividing $|M_\sigma\cap M^g|$ avoids $\beta(M)$.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 3 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch3_MaximalSubgroups/S12_Lemma1217.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch3_MaximalSubgroups/S12_Lemma1217.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_Corollary1214

namespace OddOrder.BG.Ch3.S12

open OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **BG Lemma 12.17, third clause** (mmd L3478, `β(M)′`-group part): for every `g ∈ G − M`,
the intersection `M_σ ∩ M^g` is a `β(M)′`-group (every prime dividing its order avoids `β(M)`).

Consumed by Proposition 14.2(g): with `β(M) = σ(M)` it yields `M_σ ∩ M_σ^g = 1` for `g ∉ M`. -/
theorem Msigma_inf_conj_isBetaCompl [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {g : G} (hg : g ∉ M) :
    Subgroup.IsPiSubgroup (S10.beta M)ᶜ (S10.Msigma M ⊓ MulAut.conj g • M) := by
  classical
  intro p hp
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have : Fact p.Prime := ⟨hp_prime⟩
  have hpdvd : p ∣ Nat.card ↥(S10.Msigma M ⊓ MulAut.conj g • M) :=
    (Nat.mem_primeFactors.mp hp).2.1
  -- Cauchy: an element `w` of order `p` in `M_σ ∩ M^g`; `X := ⟨w⟩` is rank-one of order `p`.
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' p hpdvd
  have hXcard : Nat.card ↥(Subgroup.zpowers (w : G)) = p := by
    rw [Nat.card_zpowers]
    exact (orderOf_injective _ (S10.Msigma M ⊓ MulAut.conj g • M).subtype_injective w).trans hw
  have hXelem : Subgroup.zpowers (w : G) ∈ elemAbelianOfRank G p 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hXcard, by rw [hXcard, pow_one]⟩
  have hXle : Subgroup.zpowers (w : G) ≤ S10.Msigma M ⊓ MulAut.conj g • M :=
    Subgroup.zpowers_le.mpr w.2
  have hXMσ : Subgroup.zpowers (w : G) ≤ S10.Msigma M := hXle.trans inf_le_left
  have hXM : Subgroup.zpowers (w : G) ≤ M := hXMσ.trans (S10.Msigma_le M)
  have hXgM : Subgroup.zpowers (w : G) ≤ MulAut.conj g • M := hXle.trans inf_le_right
  have hXne : Subgroup.zpowers (w : G) ≠ ⊥ := ne_bot_of_mem_elemAbelianOfRank_one hXelem
  have hXp : IsPGroup p ↥(Subgroup.zpowers (w : G)) := hXelem.1.isPGroup
  -- `p ∈ σ(M)` since `X ≤ M_σ`.
  have hpσ : p ∈ S10.sigma M :=
    S10.Msigma_isPiGroup M p (Nat.mem_primeFactors.mpr
      ⟨hp_prime, hXcard ▸ Subgroup.card_dvd_of_le hXMσ, Nat.card_pos.ne'⟩)
  -- `N_G(M) = M` (maximal ⟹ self-normalizing).
  have hMne : M ≠ ⊥ := fun hbot => hXne (le_bot_iff.mp (hbot ▸ hXM))
  have hNM_eq : Subgroup.normalizer (M : Set G) = M := by
    have hlt := normalizer_lt_top_of_le_of_ne_bot hG hM le_rfl hMne
    by_contra hne
    exact hlt.ne ((mem_maximalSubgroups.mp hM).2 _
      (lt_of_le_of_ne Subgroup.le_normalizer (Ne.symm hne)))
  -- **Theorem 10.1(b)** ⟹ `C_G(X) ⊄ M`.
  have hCnotM : ¬ Subgroup.centralizer (↑(Subgroup.zpowers (w : G)) : Set G) ≤ M := by
    intro hCM
    obtain ⟨c, hcC, hc⟩ :=
      (S10.fusion_control_of_mem_sigma hG hM hpσ hXne hXp).2.1 1 g
        (by rw [map_one, one_smul]; exact hXM) hXgM
    rw [map_one, one_smul] at hc
    -- `conj c • M = conj g • M` ⟹ `c⁻¹g ∈ N_G(M) = M` ⟹ `g ∈ M`, contradicting `g ∉ M`.
    have hcg : MulAut.conj (c⁻¹ * g) • M = M := by
      rw [map_mul, mul_smul, ← hc, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
    have hcgM : c⁻¹ * g ∈ M := hNM_eq ▸ mem_normalizer_of_conj_smul_eq_self hcg
    have hgM' : g ∈ M := by
      have hmem : c * (c⁻¹ * g) ∈ M := M.mul_mem (hCM hcC) hcgM
      simpa using hmem
    exact hg hgM'
  -- `ℳ(C_G(X)) ≠ {M}` (else `C_G(X) ≤ M`).
  have hℳ : maximalSubgroupsContaining
      (Subgroup.centralizer (↑(Subgroup.zpowers (w : G)) : Set G)) ≠ {M} := by
    intro hsing
    exact hCnotM (mem_maximalSubgroupsContaining.mp
      (by rw [hsing]; exact Set.mem_singleton M)).2
  -- **Corollary 12.14** contrapositive: `ℳ(C_G(X)) ≠ {M}` ⟹ `p ∉ β(M)`.
  rw [Set.mem_compl_iff]
  intro hpβ
  exact hℳ (Cor1214.maximalContaining_centralizer_and_someSylow_eq_singleton hG hM hpσ hXelem hXM
    (Or.inl hpβ)).1

/-- **Core σ-uniqueness fact for `M_σ ∩ M^g`** (`g ∉ M`), the engine of BG Lemma 12.17's third
clause (Coq `not_sCX_M` inside `sigma_compl_embedding`, BGsection12 L2476): for a nontrivial
`p`-subgroup `X ≤ M_σ ∩ M^g` with `p ∈ σ(M)`, the centralizer `C_G(X)` is **not** contained in `M`.

Theorem 10.1(b) (`fusion_control_of_mem_sigma`, σ-fusion transitivity) yields `c ∈ C_G(X)` with
`M^c = M^g`; were `C_G(X) ≤ M`, then `c⁻¹g ∈ N_G(M) = M`, hence `g ∈ M`, contradicting `g ∉ M`. -/
theorem centralizer_not_le_of_isPGroup_le_Msigma_inf_conj [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {g : G} (hg : g ∉ M)
    {p : ℕ} [Fact p.Prime] (hpσ : p ∈ S10.sigma M) {X : Subgroup G}
    (hXp : IsPGroup p ↥X) (hXne : X ≠ ⊥)
    (hXle : X ≤ S10.Msigma M ⊓ MulAut.conj g • M) :
    ¬ Subgroup.centralizer (X : Set G) ≤ M := by
  intro hCM
  have hXM : X ≤ M := (hXle.trans inf_le_left).trans (S10.Msigma_le M)
  have hXgM : X ≤ MulAut.conj g • M := hXle.trans inf_le_right
  -- Theorem 10.1(b): some `c ∈ C_G(X)` conjugates `M` to `M^g`.
  obtain ⟨c, hcC, hc⟩ :=
    (S10.fusion_control_of_mem_sigma hG hM hpσ hXne hXp).2.1 1 g
      (by rw [map_one, one_smul]; exact hXM) hXgM
  rw [map_one, one_smul] at hc
  -- `N_G(M) = M` (maximal ⟹ self-normalizing).
  have hMne : M ≠ ⊥ := fun hbot => hXne (le_bot_iff.mp (hbot ▸ hXM))
  have hNM_eq : Subgroup.normalizer (M : Set G) = M := by
    have hlt := normalizer_lt_top_of_le_of_ne_bot hG hM le_rfl hMne
    by_contra hne
    exact hlt.ne ((mem_maximalSubgroups.mp hM).2 _
      (lt_of_le_of_ne Subgroup.le_normalizer (Ne.symm hne)))
  have hcg : MulAut.conj (c⁻¹ * g) • M = M := by
    rw [map_mul, mul_smul, ← hc, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  have hcgM : c⁻¹ * g ∈ M := hNM_eq ▸ mem_normalizer_of_conj_smul_eq_self hcg
  exact hg (by have := M.mul_mem (hCM hcC) hcgM; simpa using this)

/-- **BG Lemma 12.17, third clause (TI part)** (mmd L3478, Coq `tiMsMg_Ms'`, BGsection12 L2492): for
`g ∉ M` the intersection `M_σ ∩ M^g` meets the derived subgroup `M_σ'` trivially.

A nontrivial element of the meet provides a rank-one `X ≤ M_σ ∩ M^g` with `X ≤ M_σ'`; Corollary
12.14 (`Or.inr` disjunct) then forces `C_G(X) ≤ M`, contradicting
`centralizer_not_le_of_isPGroup_le_Msigma_inf_conj`. -/
theorem Msigma_inf_conj_inf_derived_eq_bot [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {g : G} (hg : g ∉ M) :
    S10.Msigma M ⊓ MulAut.conj g • M ⊓ derivedInG (S10.Msigma M) = ⊥ := by
  classical
  by_contra hne
  set K : Subgroup G := S10.Msigma M ⊓ MulAut.conj g • M ⊓ derivedInG (S10.Msigma M) with hKdef
  -- The meet is nontrivial: pick a prime `p` dividing its order and an order-`p` element `w`.
  have hKnt : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).mpr hne
  obtain ⟨p, hp_prime, hpdvd⟩ :=
    (Nat.card ↥K).exists_prime_and_dvd (by
      have := Finite.one_lt_card_iff_nontrivial.mpr hKnt; omega)
  have : Fact p.Prime := ⟨hp_prime⟩
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' p hpdvd
  have hXcard : Nat.card ↥(Subgroup.zpowers (w : G)) = p := by
    rw [Nat.card_zpowers]
    exact (orderOf_injective _ K.subtype_injective w).trans hw
  have hXelem : Subgroup.zpowers (w : G) ∈ elemAbelianOfRank G p 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hXcard, by rw [hXcard, pow_one]⟩
  have hXp : IsPGroup p ↥(Subgroup.zpowers (w : G)) := hXelem.1.isPGroup
  have hXne : Subgroup.zpowers (w : G) ≠ ⊥ := ne_bot_of_mem_elemAbelianOfRank_one hXelem
  have hXK : Subgroup.zpowers (w : G) ≤ K := Subgroup.zpowers_le.mpr w.2
  have hXmeet : Subgroup.zpowers (w : G) ≤ S10.Msigma M ⊓ MulAut.conj g • M :=
    hXK.trans inf_le_left
  have hXMσ' : Subgroup.zpowers (w : G) ≤ derivedInG (S10.Msigma M) := hXK.trans inf_le_right
  have hXMσ : Subgroup.zpowers (w : G) ≤ S10.Msigma M := hXmeet.trans inf_le_left
  have hXM : Subgroup.zpowers (w : G) ≤ M := hXMσ.trans (S10.Msigma_le M)
  -- `p ∈ σ(M)` from `X ≤ M_σ`.
  have hpσ : p ∈ S10.sigma M :=
    S10.Msigma_isPiGroup M p (Nat.mem_primeFactors.mpr
      ⟨hp_prime, hXcard ▸ Subgroup.card_dvd_of_le hXMσ, Nat.card_pos.ne'⟩)
  -- Corollary 12.14 (`Or.inr`): `ℳ(C_G(X)) = {M}` ⟹ `C_G(X) ≤ M`, contradicting the core.
  have hℳ := (Cor1214.maximalContaining_centralizer_and_someSylow_eq_singleton
    hG hM hpσ hXelem hXM (Or.inr hXMσ')).1
  have hCM : Subgroup.centralizer (↑(Subgroup.zpowers (w : G)) : Set G) ≤ M :=
    (mem_maximalSubgroupsContaining.mp (by rw [hℳ]; exact Set.mem_singleton M)).2
  exact centralizer_not_le_of_isPGroup_le_Msigma_inf_conj hG hM hg hpσ hXp hXne hXmeet hCM

end OddOrder.BG.Ch3.S12


