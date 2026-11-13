-- Prove2me | Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_Theorem125
-- name    : OddOrder_BG_Ch3_MaximalSubgroups_S12_Theorem125
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T07:27:42.321099+00:00
-- url     : https://prove2.me/theorems/0e8917cf-636c-40b8-b1f5-d988efe58270
-- title:
--   BG §12: Theorem 12.5, the $\tau_2$-case gateway
-- statement:
--   Formalizes Theorem 12.5 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §12: the main structure theorem when $\tau_2(M)\ne\emptyset$, which relays the results of §11 into the $\tau_2$-cascade 12.6–12.16, after which §11 is no longer referenced. It includes, for example, nilpotency of $M_\sigma$ when $\tau_2$ is nonempty.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 4 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch3_MaximalSubgroups/S12_Theorem125.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch3_MaximalSubgroups/S12_Theorem125.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_ExceptionalBridge

namespace OddOrder.BG.Ch3.S12

open OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- If `ℳ(N_G(X)) = {M}` for a nontrivial `X ≤ M`, then `N_G(X) ≤ M` (the proper
subgroup `N_G(X)` lies in some maximal subgroup, which must be `M`). -/
theorem normalizer_le_of_maximalSubgroupsContaining_eq_singleton [Finite G]
    (hG : IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {X : Subgroup G} (hXM : X ≤ M) (hXne : X ≠ ⊥)
    (hsingle : maximalSubgroupsContaining (Subgroup.normalizer (X : Set G)) = {M}) :
    Subgroup.normalizer (X : Set G) ≤ M := by
  have hNlt := normalizer_lt_top_of_le_of_ne_bot hG hM hXM hXne
  obtain ⟨Mst, hMst_co, hMst_le⟩ :=
    (eq_top_or_exists_le_coatom (Subgroup.normalizer (X : Set G))).resolve_left hNlt.ne
  have hmem : Mst ∈ maximalSubgroupsContaining (Subgroup.normalizer (X : Set G)) :=
    mem_maximalSubgroupsContaining.mpr ⟨hMst_co, hMst_le⟩
  rw [hsingle, Set.mem_singleton_iff] at hmem
  exact hmem ▸ hMst_le

/-- **Proposition 12.4(b), contrapositive form** (the §11 entry from `τ₂`): for
`p ∉ σ(M)` and `A ∈ ℰ_p²(M)`, some line `A₀ ∈ ℰ¹(A)` has `N_G(A₀) ≤ M`
(mmd L3168: "By Proposition 12.4, `N_G(A₀) ⊆ M` for some subgroup `A₀ ∈ ℰ¹(A)`
because `p ∉ σ(M)`"). -/
theorem exists_line_normalizer_le_of_notMem_sigma [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime]
    (hpσ : p ∉ S10.sigma M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2)
    (hAM : A ≤ M) :
    ∃ A₀ ∈ elemAbelianOfRank G p 1, A₀ ≤ A ∧
      Subgroup.normalizer (A₀ : Set G) ≤ M := by
  by_contra hno
  have hb : ∀ A₀ ∈ elemAbelianOfRank G p 1, A₀ ≤ A →
      maximalSubgroupsContaining (Subgroup.normalizer (A₀ : Set G)) ≠ {M} := by
    intro A₀ hA₀ hA₀A hsingle
    exact hno ⟨A₀, hA₀, hA₀A,
      normalizer_le_of_maximalSubgroupsContaining_eq_singleton hG hM (hA₀A.trans hAM)
        (ne_bot_of_mem_elemAbelianOfRank_one hA₀) hsingle⟩
  exact hpσ (mem_sigma_and_Malpha_eq_bot_of_forall_normalizer_ne hG hM hA hAM hb).1

/-- **BG Theorem 12.5(b), `Ω₁`-clause** (mmd L3162): for `p ∈ τ₂(M)` and `A ∈ ℰ_p²(M)`,
**every** Sylow `p`-subgroup `P` of `M` containing `A` satisfies `A = Ω₁(P)` and
`N_G(P) ⊄ M`. (The Sylow-independent strengthening of the `P`-clause of
`Msigma_nilpotent_of_tau2`; Corollary 11.6(a) transported along
`Hypothesis111.of_sylow`. Used in Corollary 12.6(a) to identify `ℰ_p¹(E) = ℰ¹(A)`.) -/
theorem omega1_eq_of_tau2 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAM : A ≤ M)
    {P : Subgroup G} (hPpg : IsPGroup p ↥P) (hAP : A ≤ P) (hPM : P ≤ M)
    (hPsyl : ∀ R : Subgroup G, P ≤ R → R ≤ M → IsPGroup p ↥R → R = P) :
    A = (Omega ↥P p 1).map P.subtype ∧ ¬ Subgroup.normalizer (P : Set G) ≤ M := by
  classical
  have hpσ : p ∉ S10.sigma M := tau2_subset_sigma_compl M hp
  obtain ⟨A₀, hA₀, hA₀A, hN⟩ :=
    exists_line_normalizer_le_of_notMem_sigma hG hM hpσ hA hAM
  obtain ⟨P₀, h111₀⟩ := S11.Hypothesis111.of_normalizer_le hG hM hpσ hA₀ hN hA hA₀A hAM
  have h111 := h111₀.of_sylow hPpg hAP hPM hPsyl
  exact ⟨(S11.omega1_eq_and_centralizer_trivial hG h111).1, h111.normalizer_P_not_le⟩

/-- **BG Theorem 12.5** (mmd L3159): suppose `p ∈ τ₂(M)` and `A ∈ ℰ_p²(M)`. Then
(a) `M_σ` is nilpotent; (b) `M` has abelian Sylow `p`-subgroups, and there is a Sylow
`p`-subgroup `P` of `M` containing `A` with `N_G(P) ⊄ M`; (c) `M_σ A ⊴ M`;
(d) `C_{M_σ}(A) = 1`; (e) `M_σ ∩ M* = 1` for every `M* ∈ ℳ(A) − {M}`; and
(f) there is `A₁ ∈ ℰ¹(A)` with `C_{M_σ}(A₁) = 1`.
(原典 (b) の `Ω₁(P) = A` は Omega の入れ子のため defer; `A = Ω₁(P)` 自体は
Corollary 11.6(a) として §11 に landed 済み。) -/
theorem Msigma_nilpotent_of_tau2 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAM : A ≤ M) :
    Group.IsNilpotent ↥(S10.Msigma M) ∧
    ((∀ P : Sylow p ↥M, IsMulCommutative (P : Subgroup ↥M)) ∧
      ∃ P : Subgroup G, P ≤ M ∧ IsPGroup p ↥P ∧ A ≤ P ∧
        (∀ T : Subgroup G, T ≤ M → IsPGroup p ↥T → P ≤ T → P = T) ∧
        ¬ (Subgroup.normalizer (P : Set G) ≤ M)) ∧
    M ≤ Subgroup.normalizer ((S10.Msigma M ⊔ A : Subgroup G) : Set G) ∧
    S10.Msigma M ⊓ Subgroup.centralizer (A : Set G) = ⊥ ∧
    (∀ Mstar ∈ maximalSubgroupsContaining A, Mstar ≠ M → S10.Msigma M ⊓ Mstar = ⊥) ∧
    (∃ A₁ ∈ elemAbelianOfRank G p 1, A₁ ≤ A ∧
      S10.Msigma M ⊓ Subgroup.centralizer (A₁ : Set G) = ⊥) := by
  classical
  have hpσ : p ∉ S10.sigma M := tau2_subset_sigma_compl M hp
  -- Proposition 12.4 (contrapositive of (b)): some `A₀ ∈ ℰ¹(A)` has `N_G(A₀) ≤ M`.
  obtain ⟨A₀, hA₀, hA₀A, hN⟩ :=
    exists_line_normalizer_le_of_notMem_sigma hG hM hpσ hA hAM
  -- Hypothesis 11.1 holds for `(M, p, A₀, A)`.
  obtain ⟨P, h111⟩ := S11.Hypothesis111.of_normalizer_le hG hM hpσ hA₀ hN hA hA₀A hAM
  -- (d) `C_{M_σ}(A) = 1` (Corollary 11.6(b)).
  have hd : S10.Msigma M ⊓ Subgroup.centralizer (A : Set G) = ⊥ := by
    rw [inf_comm]
    exact (S11.omega1_eq_and_centralizer_trivial hG h111).2
  -- (e) `M_σ ∩ M* = 1` for `M* ∈ ℳ(A) − {M}`.
  have he : ∀ Mstar ∈ maximalSubgroupsContaining A, Mstar ≠ M →
      S10.Msigma M ⊓ Mstar = ⊥ := by
    intro Mstar hMstar_mem hMne
    obtain ⟨hMst_co, hAMst⟩ := mem_maximalSubgroupsContaining.mp hMstar_mem
    have hMst : Mstar ∈ maximalSubgroups G := mem_maximalSubgroups.mpr hMst_co
    -- in either case `M_σ ∩ M* ≤ C_G(A)`:
    have hKC : S10.Msigma M ⊓ Mstar ≤ Subgroup.centralizer (A : Set G) := by
      rcases Classical.em (∃ A₀' ∈ elemAbelianOfRank G p 1, A₀' ≤ A ∧
          Subgroup.normalizer (A₀' : Set G) ≤ Mstar) with ⟨A₀', hA₀', hA₀'A, hN'⟩ | hno
      · -- a line normalized into `M*`: Lemma 12.3(a).
        exact le_centralizer_swap (elemAb_centralizes_Msigma_meet hG hM hMst hMne hpσ
          hA (le_inf hAM hAMst) hA₀' hA₀'A hN')
      · -- otherwise: Proposition 12.4(b) for `M*`; the Sylow closure collapses
        -- (`M*_α = ⊥`) to a normal Sylow `p`-subgroup `S ⊴ M*`.
        have hb' : ∀ A₀' ∈ elemAbelianOfRank G p 1, A₀' ≤ A →
            maximalSubgroupsContaining (Subgroup.normalizer (A₀' : Set G)) ≠ {Mstar} := by
          intro A₀' hA₀' hA₀'A hsingle
          exact hno ⟨A₀', hA₀', hA₀'A,
            normalizer_le_of_maximalSubgroupsContaining_eq_singleton hG hMst
              (hA₀'A.trans hAMst) (ne_bot_of_mem_elemAbelianOfRank_one hA₀') hsingle⟩
        obtain ⟨hpσ', hMα', -, -⟩ :=
          mem_sigma_and_Malpha_eq_bot_of_forall_normalizer_ne hG hMst hA hAMst hb'
        obtain ⟨SM, hASM⟩ := hA.1.isPGroup.comap_subtype.exists_le_sylow (G := Mstar)
        set S : Subgroup G := (SM : Subgroup ↥Mstar).map Mstar.subtype with hSdef
        have hAS : A ≤ S := by
          rw [hSdef, ← Subgroup.map_subgroupOf_eq_of_le hAMst]
          exact Subgroup.map_mono hASM
        have hT := normalizer_Malpha_sup_sylow_of_mem_sigma hG hMst hpσ' SM
        rw [hMα', bot_sup_eq, ← hSdef] at hT
        -- `A` normalizes `K = M_σ ∩ M*`:
        have hKinv : A ≤ Subgroup.normalizer ((S10.Msigma M ⊓ Mstar : Subgroup G) : Set G) :=
          le_normalizer_inf (hAM.trans (le_normalizer_opiCoreInG _ _))
            (hAMst.trans Subgroup.le_normalizer)
        -- `⁅A, K⁆ ≤ K ⊓ S`:
        have hcomm_le : ⁅A, (S10.Msigma M ⊓ Mstar : Subgroup G)⁆ ≤
            (S10.Msigma M ⊓ Mstar) ⊓ S := by
          rw [Subgroup.commutator_le]
          intro a ha k hk
          refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
          · have h2 : a * k * a⁻¹ ∈ S10.Msigma M ⊓ Mstar :=
              (Subgroup.mem_normalizer_iff.mp (hKinv ha) k).mp hk
            have h3 : a * k * a⁻¹ * k⁻¹ ∈ S10.Msigma M ⊓ Mstar :=
              Subgroup.mul_mem _ h2 (Subgroup.inv_mem _ hk)
            rwa [commutatorElement_def]
          · have hkM : k ∈ Mstar := hk.2
            have h2 : k * a⁻¹ * k⁻¹ ∈ S :=
              (Subgroup.mem_normalizer_iff.mp (hT hkM) a⁻¹).mp (S.inv_mem (hAS ha))
            have h3 : a * (k * a⁻¹ * k⁻¹) ∈ S := S.mul_mem (hAS ha) h2
            rw [commutatorElement_def]
            simpa [mul_assoc] using h3
        -- `K ⊓ S = ⊥` (a `p'`-group meets a `p`-group trivially):
        have hKS_bot : (S10.Msigma M ⊓ Mstar) ⊓ S = ⊥ := by
          rw [← Subgroup.card_eq_one]
          have hdvd_S : Nat.card ↥((S10.Msigma M ⊓ Mstar) ⊓ S : Subgroup G) ∣
              Nat.card ↥S := Subgroup.card_dvd_of_le inf_le_right
          have hnp : ¬ p ∣ Nat.card ↥((S10.Msigma M ⊓ Mstar) ⊓ S : Subgroup G) := by
            intro hdvd
            have h1 : p ∣ Nat.card ↥(S10.Msigma M) :=
              hdvd.trans (Subgroup.card_dvd_of_le (inf_le_left.trans inf_le_left))
            exact hpσ (S10.Msigma_isPiGroup M p
              (Nat.mem_primeFactors.mpr ⟨Fact.out, h1, Nat.card_pos.ne'⟩))
          obtain ⟨k, hk⟩ := (SM.isPGroup'.map Mstar.subtype).exists_card_eq
          rw [← hSdef] at hk
          rw [hk] at hdvd_S
          exact Nat.Coprime.eq_one_of_dvd
            (Nat.Coprime.pow_right k
              ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hnp).symm)
            hdvd_S
        have hbot : ⁅A, (S10.Msigma M ⊓ Mstar : Subgroup G)⁆ = ⊥ :=
          le_bot_iff.mp (hKS_bot ▸ hcomm_le)
        exact le_centralizer_swap
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot)
    rw [← le_bot_iff, ← hd]
    exact le_inf inf_le_left hKC
  -- (f) Corollary 11.6(c): a line `A₁` with trivial `M_σ`-centralizer.
  have hf : ∃ A₁ ∈ elemAbelianOfRank G p 1, A₁ ≤ A ∧
      S10.Msigma M ⊓ Subgroup.centralizer (A₁ : Set G) = ⊥ := by
    obtain ⟨A₁, A₂, hA₁A, -, -, hA₁card, -, -, -, hA₁cent, -⟩ :=
      S11.exists_distinct_conj_lines hG h111
    refine ⟨A₁, ⟨Subgroup.IsElementaryAbelian.of_card_prime hA₁card,
      by rw [hA₁card, pow_one]⟩, hA₁A, ?_⟩
    rw [inf_comm]
    exact hA₁cent
  refine ⟨S11.Msigma_isNilpotent hG h111,
    ⟨fun S => S11.sylow_p_isCommutative hG h111 S,
      P, h111.P_le, h111.P_pgroup, h111.A_le_P,
      fun T hTM hTp hPT => (h111.P_sylow T hPT hTM hTp).symm,
      h111.normalizer_P_not_le⟩,
    S11.MsigmaA_normal hG h111, hd, he, hf⟩

end OddOrder.BG.Ch3.S12


