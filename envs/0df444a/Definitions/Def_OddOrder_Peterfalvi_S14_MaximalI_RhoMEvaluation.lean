-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_RhoMEvaluation
-- name    : OddOrder_Peterfalvi_S14_MaximalI_RhoMEvaluation
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T15:01:57.288911+00:00
-- url     : https://prove2.me/theorems/479f330c-1f6c-41d9-b0ff-0235d9ad865d
-- title:
--   Peterfalvi (12.15): the $\rho_M$-evaluation on $K^\#$
-- statement:
--   Formalizes the first claim of Peterfalvi (12.15): for the counterexample maximal $M$ of (12.8) and the witness Dade character $\psi=\chi^{\tau_1}$ of (12.13), $\psi^{\rho_M}(g)=\psi(g)$ on $K^\#$.
--
--   Main declarations: `counterexample_psi_constant_on_signalizer_coset` (Peterfalvi (12.15), the coset-constancy core); `counterexample_chiRho_eval_of_mem_K_sharp` (Peterfalvi (12.15), first claim); `hypothesis71SharpKernel` (The (12.15) `ρ_M`-machinery over `A₁(M) = K^#`); `counterexample_chiRhoA1_eval_of_mem_K_sharp` (Peterfalvi (12.15), first claim, `A₁(M)`-form).
--
--   The bundle also proves 3 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S14_MaximalI/RhoMEvaluation.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S14_MaximalI/RhoMEvaluation.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_MinimalCounterexample
import Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_PairCoherence
import Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_DadeContradiction

namespace OddOrder.Peterfalvi.S14

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.15), the coset-constancy core**: `ψ` is constant on the signalizer coset
`g·H(g)` of any `g ∈ K^#` (`H(g) = ftSupportKernel`, the faithful (8.14) kernel).  This is the
`hconst` input of the `ρ`-collapse `chiRho_apply_eq_of_forall_coset`, isolated so that the
`A(M)`- and `A₁(M)`-based `ρ_M` evaluations can both consume it (the kernel does not depend on
the ambient support, `ftSupportKernel_restrict`). -/
theorem counterexample_psi_constant_on_signalizer_coset [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr)
    (hyp : Hypothesis data.L)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A)
    {chi0 : IrreducibleCharacter ↥data.L}
    (data0 : CharacterDecompositionData hyp (chi0 : ClassFunction ↥data.L ℂ))
    (hchi0 : chi0 ∈ data0.constituents)
    (hchi0_mem : (chi0 : ClassFunction ↥data.L ℂ) ∈ hyp.Sset)
    {ψ : ClassFunction G ℂ}
    (hpsi : ψ = coh.extension (chi0 : ClassFunction ↥data.L ℂ))
    (hypM : Hypothesis ctr.M)
    {g : G} (hgK : g ∈ ctr.K) (hg1 : g ≠ 1) :
    ∀ y ∈ OddOrder.Peterfalvi.S10.ftSupportKernel ctr.M
      (OddOrder.GroupTheory.typeIA ctr.M hypM.typeI) g, ψ (g * y) = ψ g := by
  classical
  intro y hyKer
  by_cases hesc : g ∈ OddOrder.GroupTheory.escapingCentralizerSet ctr.M
      (OddOrder.GroupTheory.typeIA ctr.M hypM.typeI)
  · -- Escaping branch.
    have hgKσ : g ∈ OddOrder.BG.Ch3.S10.Msigma ctr.M := MF_eq_Msigma hG ctr ▸ hgK
    have hgσs : g ∈ OddOrder.BG.Ch4.S14.sigmaSharp ctr.M := ⟨hgKσ, hg1⟩
    have hescC : ¬ Subgroup.centralizer ({g} : Set G) ≤ ctr.M := hesc.2
    -- the unique maximal `N₀ ⊇ C_G(g)` and the `FT_signalizerBase` pin
    obtain ⟨N₀, hN₀⟩ :=
      OddOrder.BG.Ch4.S16.maximalSubgroupsContaining_centralizer_eq_singleton_of_sigmaSharp_escape
        hG ctr.M_maximal hgσs hescC
    have hgt : 1 < (OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement g).ncard := by
      by_contra h
      push Not at h
      exact hescC
        (OddOrder.BG.Ch4.S16.centralizer_le_of_maximalSigma_le_one hG ctr.M_maximal hgKσ hg1 h)
    have hne : (OddOrder.GroupTheory.maximalSubgroupsContaining
        (Subgroup.centralizer ({g} : Set G))).Nonempty := by
      rw [hN₀]
      exact ⟨N₀, rfl⟩
    have hcond : 1 < (OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement g).ncard ∧
        (OddOrder.GroupTheory.maximalSubgroupsContaining
          (Subgroup.centralizer ({g} : Set G))).Nonempty := ⟨hgt, hne⟩
    have hbase : OddOrder.BG.Ch4.S16.FT_signalizerBase g = N₀ := by
      have hb : OddOrder.BG.Ch4.S16.FT_signalizerBase g = hcond.2.choose := dif_pos hcond
      have hch : hcond.2.choose ∈ ({N₀} : Set (Subgroup G)) :=
        (Set.ext_iff.mp hN₀ _).mp hcond.2.choose_spec
      exact hb.trans (Set.mem_singleton_iff.mp hch)
    -- the kernel is `N₀_σ ⊓ C_G(g)`
    have hker_eq : OddOrder.BG.Ch4.S16.FT_signalizer g
        = OddOrder.BG.Ch3.S10.Msigma N₀ ⊓ Subgroup.centralizer ({g} : Set G) := by
      rw [show OddOrder.BG.Ch4.S16.FT_signalizer g
          = OddOrder.BG.Ch3.S10.Msigma (OddOrder.BG.Ch4.S16.FT_signalizerBase g) ⊓
            Subgroup.centralizer ({g} : Set G) from rfl, hbase]
    rw [OddOrder.Peterfalvi.S10.ftSupportKernel_eq_of_escaping hesc, hker_eq] at hyKer
    -- Theorem D(4): the escape structure at `N`, pinned to `N₀`
    obtain ⟨R, -, N, ⟨hNmem, -, -, hASet, hNtype, -, hP2pkg⟩, -⟩ :=
      OddOrder.BG.Ch4.S16.exists_RData_escape_structure hG ctr.M_maximal hgσs hescC
    have hNN₀ : N = N₀ := by
      rw [hN₀] at hNmem
      exact hNmem
    subst hNN₀
    have hNmax : N ∈ maximalSubgroups G := by
      have := hN₀ ▸ (Set.mem_singleton N)
      exact (OddOrder.GroupTheory.mem_maximalSubgroupsContaining.mp this).1
    have hCgN : Subgroup.centralizer ({g} : Set G) ≤ N := by
      have := hN₀ ▸ (Set.mem_singleton N)
      exact (OddOrder.GroupTheory.mem_maximalSubgroupsContaining.mp this).2
    -- kill the `P₂` branch: it would make `M` Frobenius over `M_σ` with cyclic complement
    have hNF : OddOrder.BG.Ch4.S14.IsTypeF N := by
      rcases hNtype with h | h
      · exact h
      · exfalso
        obtain ⟨-, -, E, hEM, hEcyc, hEcompl, hEfrob⟩ := hP2pkg h
        exact counterexample_not_frobenius_MF hG ctr ⟨E, hEM, hEcyc, hEcompl, hEfrob⟩
    have hNtypeI : IsTypeI N := OddOrder.BG.Ch4.S16.isTypeI_of_isTypeF hG hNmax hNF
    have hNFeq : maxNilpotentNormalHall N = OddOrder.BG.Ch3.S10.Msigma N :=
      OddOrder.BG.Ch4.S16.maxNilpotentNormalHall_eq_Msigma_of_isTypeF_or_isTypeP2
        hG hNmax hNtype
    -- `g ∈ N ∖ N_F` and `C_{N_F}(g) ≠ 1`
    have hgN : g ∈ N := hCgN (Subgroup.mem_centralizer_iff.mpr
      (fun z hz => by rw [Set.mem_singleton_iff.mp hz]))
    have hgNF : g ∉ maxNilpotentNormalHall N := by
      rw [hNFeq]
      exact fun hmem => hASet.2 (SetLike.mem_coe.mpr hmem)
    have hRne : maxNilpotentNormalHall N ⊓ Subgroup.centralizer ({g} : Set G) ≠ ⊥ := by
      obtain ⟨N₁, ⟨hN₁max, hCN₁, hR₁ne, -, -, -, -⟩, -⟩ :=
        OddOrder.BG.Ch4.S16.signalizer_structure_of_mem_sigmaSharp hG ctr.M_maximal hgσs hgt
      have hN₁mem : N₁ ∈ OddOrder.GroupTheory.maximalSubgroupsContaining
          (Subgroup.centralizer ({g} : Set G)) := ⟨hN₁max, hCN₁⟩
      rw [hN₀] at hN₁mem
      rw [hNFeq]
      rw [Set.mem_singleton_iff] at hN₁mem
      rwa [hN₁mem] at hR₁ne
    -- `N` is not conjugate to the Frobenius witness `L`
    have hLN : ¬ ∃ c : G, MulAut.conj c • data.L = N :=
      witness_L_not_conj_of_kernel_centralizer_ne_bot hG hnoV data hgN hgNF hRne
    -- the N-side (12.4) supply
    obtain ⟨hypN⟩ := exists_typeI_hypothesis hG hNmax hNtypeI
    have data_N : ∀ χ ∈ hypN.Sset, CharacterDecompositionData hypN χ :=
      fun χ hχ => (character_decomposition_and_dade_domain hG hypN hχ).choose
    have horth : ∀ χ (hχ : χ ∈ hypN.Sset), ∀ α ∈ Rset (data_N χ hχ),
        ClassFunction.inner ψ α = 0 := by
      intro χ hχ α hα
      rw [hpsi]
      exact coherent_extension_constituent_orthogonal_Rset_of_nonconjugate hG hyp coh data0
        hchi0 hchi0_mem hypN hLN (data_N χ hχ) α hα
    have hgNhyp : g ∉ hypN.H := by
      intro hmem
      exact hgNF (hypN.typeI.typeF.H_eq ▸ hmem)
    -- (12.4): `ψ` is constant on `g·N_F ⊇ g·H(g)`
    have hconstN := orthogonal_character_constant_on_coset hG hypN data_N horth hgN hgNhyp
    have hyNF : y ∈ hypN.H := by
      have hyMσ : y ∈ OddOrder.BG.Ch3.S10.Msigma N := (Subgroup.mem_inf.mp hyKer).1
      have hyNF' : y ∈ maxNilpotentNormalHall N := hNFeq ▸ hyMσ
      change y ∈ hypN.typeI.typeF.H
      rw [hypN.typeI.typeF.H_eq]
      exact hyNF'
    exact hconstN y hyNF
  · -- Non-escaping branch: `H(g) = ⊥`, the coset is trivial.
    rw [OddOrder.Peterfalvi.S10.ftSupportKernel_eq_bot_of_not_escaping hesc,
      Subgroup.mem_bot] at hyKer
    rw [hyKer, mul_one]

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.15), first claim**: `ψ^{ρ_M}(g) = ψ(g)` for `g ∈ K^#`, where
`ψ = coh.extension χ₀` is the witness Dade character of (12.13) and `ρ_M` is the (7.1)
`ρ`-machinery of the counterexample `M` over the full support `A(M)`
(`hypM.toHypothesis71`). -/
theorem counterexample_chiRho_eval_of_mem_K_sharp [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr)
    (hyp : Hypothesis data.L)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A)
    {chi0 : IrreducibleCharacter ↥data.L}
    (data0 : CharacterDecompositionData hyp (chi0 : ClassFunction ↥data.L ℂ))
    (hchi0 : chi0 ∈ data0.constituents)
    (hchi0_mem : (chi0 : ClassFunction ↥data.L ℂ) ∈ hyp.Sset)
    {ψ : ClassFunction G ℂ}
    (hpsi : ψ = coh.extension (chi0 : ClassFunction ↥data.L ℂ))
    (hypM : Hypothesis ctr.M)
    {g : G} (hgK : g ∈ ctr.K) (hg1 : g ≠ 1) (hgM : g ∈ ctr.M) :
    hypM.toHypothesis71.chiRho ψ ⟨g, hgM⟩ = ψ g := by
  classical
  have hHK : hypM.typeI.typeF.H = ctr.K :=
    hypM.typeI.typeF.H_eq.trans ctr.K_eq_MF.symm
  have hgA : ((⟨g, hgM⟩ : ↥ctr.M) : G) ∈
      OddOrder.GroupTheory.typeIA ctr.M hypM.typeI := by
    refine sharpSubgroup_H_subset_typeIA hypM.typeI ⟨?_, ?_⟩
    · exact SetLike.mem_coe.mpr (hHK ▸ hgK)
    · simpa using hg1
  refine OddOrder.Peterfalvi.S09.Hypothesis71.chiRho_apply_eq_of_forall_coset
    hypM.toHypothesis71 ψ hgA ?_
  intro y hy
  refine counterexample_psi_constant_on_signalizer_coset hG hnoV data hyp coh data0 hchi0
    hchi0_mem hpsi hypM hgK hg1 y ?_
  rw [← hypM.dadeData.H_eq_ftSupportKernel ⟨g, hgA⟩]
  exact hy

/-- Conjugation by `M` preserves the sharp kernel `H_M^# = K^#` (the kernel is `subgroupOf`-normal
and conjugation fixes `≠ 1`) — the `L_normalizes_A` input of the `A₁(M)`-restricted Dade datum. -/
theorem sharpSubgroup_H_conj_mem [Finite G]
    {ctr : CounterexampleHypothesis (G := G)} (hypM : Hypothesis ctr.M) :
    ∀ (l : ↥ctr.M) ⦃a : G⦄, a ∈ sharpSubgroup hypM.typeI.typeF.H →
      (l : G) * a * (l : G)⁻¹ ∈ sharpSubgroup hypM.typeI.typeF.H := by
  intro l a ha
  have hnormal : ((hypM.typeI.typeF.H).subgroupOf ctr.M).Normal := by
    rw [hypM.typeI.typeF.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal ctr.M
  have haH : a ∈ hypM.typeI.typeF.H := ha.1
  have haM : a ∈ ctr.M := hypM.typeI.typeF.H_le haH
  refine ⟨?_, ?_⟩
  · -- conjugation stays in the normal `H`
    have hmem := hnormal.conj_mem ⟨a, haM⟩ (Subgroup.mem_subgroupOf.mpr haH) l
    have hcoe := Subgroup.mem_subgroupOf.mp hmem
    simpa using hcoe
  · -- conjugation preserves `≠ 1`
    intro h1
    refine ha.2 ?_
    rw [Set.mem_singleton_iff] at h1 ⊢
    calc a = (l : G)⁻¹ * ((l : G) * a * (l : G)⁻¹) * (l : G) := by group
      _ = (l : G)⁻¹ * 1 * (l : G) := by rw [h1]
      _ = 1 := by group

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The (12.15) `ρ_M`-machinery over `A₁(M) = K^#`** — the (7.1) data with `M` and `A₁(M)`
in place of `L` and `A`, exactly as Peterfalvi defines `ρ_M`.  Built by restricting the
counterexample's §10 Dade datum from `A(M)` to the `M`-stable subset `K^# = H_M^# ⊆ A(M)`
(`S04.Hypothesis.restrict` / `FullDadeIsometryData.restrict`, the
S12 type-`P` `toHypothesis71` pattern).  The `A₁`-based `ρ_M` is the one whose (7.3) norm bound
runs over the thickened `Ã₁(M)`, disjoint from `Ã₁(L)` by (8.17) — the (12.16) requirement. -/
noncomputable def hypothesis71SharpKernel [Finite G]
    {ctr : CounterexampleHypothesis (G := G)} (hypM : Hypothesis ctr.M) :
    OddOrder.Peterfalvi.S09.Hypothesis71 G
      (sharpSubgroup hypM.typeI.typeF.H) ctr.M :=
  { hyp := hypM.dadeData.dade.restrict (sharpSubgroup_H_subset_typeIA hypM.typeI)
      (sharpSubgroup_H_conj_mem hypM)
    τ := ((hypM.dadeData.dade.fullDadeIsometryData).restrict
      (sharpSubgroup_H_subset_typeIA hypM.typeI) (sharpSubgroup_H_conj_mem hypM)).toDadeMap
    isDadeMap := ((hypM.dadeData.dade.fullDadeIsometryData).restrict
      (sharpSubgroup_H_subset_typeIA hypM.typeI)
      (sharpSubgroup_H_conj_mem hypM)).toDadeIsometryData.isDadeMap }

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.15), first claim, `A₁(M)`-form**: the `A₁(M) = K^#`-based `ρ_M`
(`hypothesis71SharpKernel`) evaluates identically: `ψ^{ρ_M}(g) = ψ(g)` for `g ∈ K^#`.  Same
collapse as the `A(M)`-form — the restricted datum's local kernel at `g` is the same faithful
signalizer (`S04.Hypothesis.restrict` keeps the per-point `H`). -/
theorem counterexample_chiRhoA1_eval_of_mem_K_sharp [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr)
    (hyp : Hypothesis data.L)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A)
    {chi0 : IrreducibleCharacter ↥data.L}
    (data0 : CharacterDecompositionData hyp (chi0 : ClassFunction ↥data.L ℂ))
    (hchi0 : chi0 ∈ data0.constituents)
    (hchi0_mem : (chi0 : ClassFunction ↥data.L ℂ) ∈ hyp.Sset)
    {ψ : ClassFunction G ℂ}
    (hpsi : ψ = coh.extension (chi0 : ClassFunction ↥data.L ℂ))
    (hypM : Hypothesis ctr.M)
    {g : G} (hgK : g ∈ ctr.K) (hg1 : g ≠ 1) (hgM : g ∈ ctr.M) :
    (hypothesis71SharpKernel hypM).chiRho ψ ⟨g, hgM⟩ = ψ g := by
  classical
  have hHK : hypM.typeI.typeF.H = ctr.K :=
    hypM.typeI.typeF.H_eq.trans ctr.K_eq_MF.symm
  have hgA1 : ((⟨g, hgM⟩ : ↥ctr.M) : G) ∈ sharpSubgroup hypM.typeI.typeF.H := by
    refine ⟨?_, ?_⟩
    · exact SetLike.mem_coe.mpr (hHK ▸ hgK)
    · simpa using hg1
  refine OddOrder.Peterfalvi.S09.Hypothesis71.chiRho_apply_eq_of_forall_coset
    (hypothesis71SharpKernel hypM) ψ hgA1 ?_
  intro y hy
  refine counterexample_psi_constant_on_signalizer_coset hG hnoV data hyp coh data0 hchi0
    hchi0_mem hpsi hypM hgK hg1 y ?_
  -- the restricted datum's kernel at `g` is the original one (`restrict_H` is `rfl`)
  rw [← hypM.dadeData.H_eq_ftSupportKernel
    ⟨g, sharpSubgroup_H_subset_typeIA hypM.typeI hgA1⟩]
  exact hy

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.15), second claim**: the witness Dade character `ψ` is **constant on
`K − K′`** — the (12.5)-M constancy of `ψ^{ρ_M}` (`psi_constant_on_kernel_sub_derived_ofData`,
coherence-free, with the `(12.3)+(5.5)` cross-orthogonality supply from `L ≁ M`) transported to
`ψ` by the first claim (`counterexample_chiRho_eval_of_mem_K_sharp`). -/
theorem counterexample_psi_constant_on_K_sub_Kprime [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr)
    (hyp : Hypothesis data.L)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A)
    {chi0 : IrreducibleCharacter ↥data.L}
    (data0 : CharacterDecompositionData hyp (chi0 : ClassFunction ↥data.L ℂ))
    (hchi0 : chi0 ∈ data0.constituents)
    (hchi0_mem : (chi0 : ClassFunction ↥data.L ℂ) ∈ hyp.Sset)
    {ψ : ClassFunction G ℂ}
    (hpsi : ψ = coh.extension (chi0 : ClassFunction ↥data.L ℂ))
    (hypM : Hypothesis ctr.M)
    {g₁ g₂ : G} (hg₁K : g₁ ∈ ctr.K) (hg₁K' : g₁ ∉ ctr.Kprime)
    (hg₂K : g₂ ∈ ctr.K) (hg₂K' : g₂ ∉ ctr.Kprime) :
    ψ g₁ = ψ g₂ := by
  classical
  have hHK : hypM.typeI.typeF.H = ctr.K :=
    hypM.typeI.typeF.H_eq.trans ctr.K_eq_MF.symm
  have hLM : ¬ ∃ c : G, MulAut.conj c • data.L = ctr.M := witness_L_not_conj_M hG hnoV data
  have data_M : ∀ χ ∈ hypM.Sset, CharacterDecompositionData hypM χ :=
    fun χ hχ => (character_decomposition_and_dade_domain hG hypM hχ).choose
  have horth : ∀ χ (hχ : χ ∈ hypM.Sset), ∀ α ∈ Rset (data_M χ hχ),
      ClassFunction.inner ψ α = 0 := by
    intro χ hχ α hα
    rw [hpsi]
    exact coherent_extension_constituent_orthogonal_Rset_of_nonconjugate hG hyp coh data0
      hchi0 hchi0_mem hypM hLM (data_M χ hχ) α hα
  have heval : ∀ z : G, ∀ hz : z ∈ hypM.typeI.typeF.H, z ≠ 1 →
      hypM.toHypothesis71.chiRhoCF ψ
        (⟨z, hypM.typeI.typeF.H_le hz⟩ : ↥ctr.M) = ψ z := by
    intro z hz hz1
    rw [OddOrder.Peterfalvi.S09.Hypothesis71.chiRhoCF_apply]
    exact counterexample_chiRho_eval_of_mem_K_sharp hG hnoV data hyp coh data0 hchi0 hchi0_mem
      hpsi hypM (by rw [← hHK]; exact hz) hz1 (hypM.typeI.typeF.H_le hz)
  have hK' : derivedInG hypM.typeI.typeF.H = ctr.Kprime := by
    rw [hHK, ctr.Kprime_eq]
  exact psi_constant_on_kernel_sub_derived_ofData hypM data_M
    (sharpSubgroup_H_subset_typeIA hypM.typeI) (one_notMem_typeIA hypM.typeI) horth heval
    (by rw [hHK]; exact hg₁K) (by rw [hK']; exact hg₁K')
    (by rw [hHK]; exact hg₂K) (by rw [hK']; exact hg₂K')

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.16), the `hA` norm lower bound**:
`(|K| − |K′|)/|M| · mval² ≤ ‖ψ^{ρ_M}‖²` for the `A₁(M)`-based `ρ_M`.  The squared norm is
`|M|⁻¹ Σ_{m ∈ M} ‖ψ^{ρ_M}(m)‖²`; restricting the sum to the `|K| − |K′|` elements of `K − K′`,
where `ψ^{ρ_M} = ψ = mval` (the three (12.15) claims), gives the bound. -/
theorem counterexample_chiRhoA1_normSq_ge [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr)
    (hyp : Hypothesis data.L)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A)
    {chi0 : IrreducibleCharacter ↥data.L}
    (data0 : CharacterDecompositionData hyp (chi0 : ClassFunction ↥data.L ℂ))
    (hchi0 : chi0 ∈ data0.constituents)
    (hchi0_mem : (chi0 : ClassFunction ↥data.L ℂ) ∈ hyp.Sset)
    {ψ : ClassFunction G ℂ}
    (hpsi : ψ = coh.extension (chi0 : ClassFunction ↥data.L ℂ))
    (hypM : Hypothesis ctr.M)
    {mval : ℤ} {g0 : G} (hg0K : g0 ∈ ctr.K) (hg0K' : g0 ∉ ctr.Kprime)
    (hmval : ψ g0 = (mval : ℂ)) :
    ((Nat.card ↥ctr.K : ℝ) - (Nat.card ↥ctr.Kprime : ℝ)) / (Nat.card ↥ctr.M : ℝ)
        * (mval : ℝ) ^ 2
      ≤ (ClassFunction.inner ((hypothesis71SharpKernel hypM).chiRhoCF ψ)
          ((hypothesis71SharpKernel hypM).chiRhoCF ψ)).re := by
  classical
  set f : ClassFunction ↥ctr.M ℂ := (hypothesis71SharpKernel hypM).chiRhoCF ψ with hf
  have hKM : ctr.K ≤ ctr.M :=
    ctr.K_eq_MF ▸ OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le ctr.M
  have hK'K : ctr.Kprime ≤ ctr.K := ctr.Kprime_eq ▸ Subgroup.map_subtype_le _
  -- the squared norm as a real sum
  have hre : (ClassFunction.inner f f).re
      = (Nat.card ↥ctr.M : ℝ)⁻¹ * ∑ m : ↥ctr.M, ‖f m‖ ^ 2 := by
    have hinner : ClassFunction.inner f f = (Nat.card ↥ctr.M : ℂ)⁻¹ *
        ((∑ m : ↥ctr.M, ‖f m‖ ^ 2 : ℝ) : ℂ) := by
      rw [ClassFunction.inner_eq_inv_card_mul_innerSum, ClassFunction.innerSum, invOf_eq_inv]
      congr 1
      rw [Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have hcast : (Nat.card ↥ctr.M : ℂ)⁻¹ * ((∑ m : ↥ctr.M, ‖f m‖ ^ 2 : ℝ) : ℂ)
        = ((((Nat.card ↥ctr.M : ℝ))⁻¹ * ∑ m : ↥ctr.M, ‖f m‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hinner, hcast, Complex.ofReal_re]
  -- the `K − K′` sampling set
  set S : Finset ↥ctr.M :=
    Finset.univ.filter (fun m : ↥ctr.M => (m : G) ∈ ctr.K ∧ (m : G) ∉ ctr.Kprime) with hS
  -- each sampled value is `mval`
  have hval : ∀ m ∈ S, ‖f m‖ ^ 2 = (mval : ℝ) ^ 2 := by
    intro m hm
    obtain ⟨hmK, hmK'⟩ := (Finset.mem_filter.mp hm).2
    have hm1 : (m : G) ≠ 1 := fun h => hmK' (h ▸ ctr.Kprime.one_mem)
    have heval : f m = ψ (m : G) := by
      rw [hf, OddOrder.Peterfalvi.S09.Hypothesis71.chiRhoCF_apply]
      exact counterexample_chiRhoA1_eval_of_mem_K_sharp hG hnoV data hyp coh data0 hchi0
        hchi0_mem hpsi hypM hmK hm1 m.2
    have hconst : ψ (m : G) = ψ g0 :=
      counterexample_psi_constant_on_K_sub_Kprime hG hnoV data hyp coh data0 hchi0 hchi0_mem
        hpsi hypM hmK hmK' hg0K hg0K'
    rw [heval, hconst, hmval]
    rw [show ‖((mval : ℤ) : ℂ)‖ = |(mval : ℝ)| by
      rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]]
    exact sq_abs _
  -- `|S| = |K| − |K′|`
  have hcardS : S.card = Nat.card ↥ctr.K - Nat.card ↥ctr.Kprime := by
    have hsplit : S = (Finset.univ.filter (fun m : ↥ctr.M => (m : G) ∈ ctr.K)) \
        (Finset.univ.filter (fun m : ↥ctr.M => (m : G) ∈ ctr.Kprime)) := by
      ext m
      simp only [hS, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
    have hsubKK' : (Finset.univ.filter (fun m : ↥ctr.M => (m : G) ∈ ctr.Kprime)) ⊆
        (Finset.univ.filter (fun m : ↥ctr.M => (m : G) ∈ ctr.K)) := by
      intro m hm
      rw [Finset.mem_filter] at hm ⊢
      exact ⟨hm.1, hK'K hm.2⟩
    have hcardK : (Finset.univ.filter (fun m : ↥ctr.M => (m : G) ∈ ctr.K)).card
        = Nat.card ↥ctr.K := by
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
      exact Nat.card_congr
        ⟨fun m => ⟨(m.1 : G), m.2⟩, fun k => ⟨⟨(k : G), hKM k.2⟩, k.2⟩,
          fun m => by ext; rfl, fun k => by ext; rfl⟩
    have hcardK' : (Finset.univ.filter (fun m : ↥ctr.M => (m : G) ∈ ctr.Kprime)).card
        = Nat.card ↥ctr.Kprime := by
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
      exact Nat.card_congr
        ⟨fun m => ⟨(m.1 : G), m.2⟩, fun k => ⟨⟨(k : G), hKM (hK'K k.2)⟩, k.2⟩,
          fun m => by ext; rfl, fun k => by ext; rfl⟩
    rw [hsplit, Finset.card_sdiff, Finset.inter_eq_left.mpr hsubKK', hcardK, hcardK']
  -- assemble
  have hK'leK : Nat.card ↥ctr.Kprime ≤ Nat.card ↥ctr.K :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hK'K)
  have hlb : ((Nat.card ↥ctr.K : ℝ) - (Nat.card ↥ctr.Kprime : ℝ)) * (mval : ℝ) ^ 2
      ≤ ∑ m : ↥ctr.M, ‖f m‖ ^ 2 := by
    have h1 : ((Nat.card ↥ctr.K : ℝ) - (Nat.card ↥ctr.Kprime : ℝ)) * (mval : ℝ) ^ 2
        = ∑ _m ∈ S, (mval : ℝ) ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul, hcardS, Nat.cast_sub hK'leK]
    rw [h1, ← Finset.sum_congr rfl hval]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun m _ _ => by positivity)
  have hMpos : (0 : ℝ) < (Nat.card ↥ctr.M : ℝ) := by exact_mod_cast Nat.card_pos
  rw [hre]
  calc ((Nat.card ↥ctr.K : ℝ) - (Nat.card ↥ctr.Kprime : ℝ)) / (Nat.card ↥ctr.M : ℝ)
        * (mval : ℝ) ^ 2
      = (Nat.card ↥ctr.M : ℝ)⁻¹
        * (((Nat.card ↥ctr.K : ℝ) - (Nat.card ↥ctr.Kprime : ℝ)) * (mval : ℝ) ^ 2) := by
        ring
    _ ≤ (Nat.card ↥ctr.M : ℝ)⁻¹ * ∑ m : ↥ctr.M, ‖f m‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_left hlb (inv_nonneg.mpr hMpos.le)

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.15), third claim**: `ψ(g) ∈ ℤ` for `g ∈ K − K′` — the constancy of the
second claim fed into the rationality/integrality argument `rhoM_integer_values`. -/
theorem counterexample_psi_int_on_K_sub_Kprime [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr)
    (hyp : Hypothesis data.L)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A)
    {chi0 : IrreducibleCharacter ↥data.L}
    (data0 : CharacterDecompositionData hyp (chi0 : ClassFunction ↥data.L ℂ))
    (hchi0 : chi0 ∈ data0.constituents)
    (hchi0_mem : (chi0 : ClassFunction ↥data.L ℂ) ∈ hyp.Sset)
    {ψ : ClassFunction G ℂ}
    (hpsi : ψ = coh.extension (chi0 : ClassFunction ↥data.L ℂ))
    (hψZ : ψ ∈ ZIrr G)
    (hypM : Hypothesis ctr.M)
    {g : G} (hgK : g ∈ ctr.K) (hgK' : g ∉ ctr.Kprime) :
    ∃ z : ℤ, ψ g = (z : ℂ) :=
  rhoM_integer_values hψZ
    (fun _g₁ _g₂ h1 h2 h3 h4 =>
      counterexample_psi_constant_on_K_sub_Kprime hG hnoV data hyp coh data0 hchi0 hchi0_mem
        hpsi hypM h1 h2 h3 h4)
    g hgK hgK'

/-- **Monotonicity of the faithful thickened support** in the base set: `A₁ ⊆ A₂` implies
`Ã(M, A₁) ⊆ Ã(M, A₂)` — the per-point kernels agree (`ftSupportKernel_restrict`), so each
thickened coset over `A₁` is a thickened coset over `A₂`. -/
theorem ftThickenedSupport_mono {M : Subgroup G} {A₁ A₂ : Set G} (h : A₁ ⊆ A₂) :
    OddOrder.Peterfalvi.S10.ftThickenedSupport M A₁ ⊆
      OddOrder.Peterfalvi.S10.ftThickenedSupport M A₂ := by
  rintro g ⟨x, hx, hg⟩
  refine ⟨x, h hx, ?_⟩
  rwa [OddOrder.Peterfalvi.S10.ftSupportKernel_restrict h hx] at hg

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The restricted faithful Dade support lands in the restricted thickened support**: for a
faithful (8.15) datum on `A` and an `M`-stable `A₁ ⊆ A`, the §4 Dade support of the restricted
datum is contained in `Ã(M, A₁)`.  The restriction keeps the per-point kernels
(`S04.Hypothesis.restrict` / `ftSupportKernel_restrict`), so each support point is a conjugate
of a thickened `A₁`-coset.  (The `⊆` direction of `dadeSupport_eq_ftThickenedSupport` for the
restricted datum — all the `hC` integration needs.) -/
theorem dadeSupport_restrict_subset_ftThickenedSupport [Finite G] {M : Subgroup G}
    {A A₁ : Set G} (d : OddOrder.Peterfalvi.S10.DadeSupportHypothesisData M A)
    (hA₁A : A₁ ⊆ A)
    (hA₁norm : ∀ (l : ↥M) ⦃a : G⦄, a ∈ A₁ → (l : G) * a * (l : G)⁻¹ ∈ A₁) :
    (d.dade.restrict hA₁A hA₁norm).dadeSupport ⊆
      OddOrder.Peterfalvi.S10.ftThickenedSupport M A₁ := by
  intro g hg
  obtain ⟨a, h, hh, hconj⟩ := (d.dade.restrict hA₁A hA₁norm).mem_dadeSupport_iff.mp hg
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  refine ⟨a.1, a.2, ?_⟩
  rw [OddOrder.GroupTheory.mem_conjClassSet]
  refine ⟨a.1 * h, ⟨h, ?_, rfl⟩, c, hc⟩
  rw [SetLike.mem_coe, OddOrder.Peterfalvi.S10.ftSupportKernel_restrict hA₁A a.2,
    ← d.H_eq_ftSupportKernel ⟨a.1, hA₁A a.2⟩]
  exact hh

/-- **`A₁(M) = H_M^#` for a (12.1) Hypothesis**: the Peterfalvi (8.10) `A₁`-set of a type-I
maximal is the sharp kernel `H^#` (`H = M_F = mainSubgroup`), via the `H_eq` identification. -/
theorem A1_eq_sharpSubgroup_H {M : Subgroup G} (hyp : Hypothesis M) :
    A1 M PeterfalviType.I = sharpSubgroup hyp.typeI.typeF.H := by
  change sharpSubgroup (mainSubgroup M PeterfalviType.I) = _
  rw [show mainSubgroup M PeterfalviType.I = maxNilpotentNormalHall M from rfl,
    hyp.typeI.typeF.H_eq]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The `A₁(M)`-based `ρ_M` datum's Dade support lands in `Ã₁(M)`** — the
`hypothesis71SharpKernel` specialization of `dadeSupport_restrict_subset_ftThickenedSupport`,
in the `A1`-set shape that the (8.18.c) mixed disjointness
(`nonconjugate_thickened_mixed_disjoint_or_swap`) speaks. -/
theorem hypothesis71SharpKernel_dadeSupport_subset [Finite G]
    {ctr : CounterexampleHypothesis (G := G)} (hypM : Hypothesis ctr.M) :
    (hypothesis71SharpKernel hypM).hyp.dadeSupport ⊆
      OddOrder.Peterfalvi.S10.ftThickenedSupport ctr.M (A1 ctr.M PeterfalviType.I) := by
  rw [A1_eq_sharpSubgroup_H hypM]
  exact dadeSupport_restrict_subset_ftThickenedSupport hypM.dadeData
    (sharpSubgroup_H_subset_typeIA hypM.typeI) (sharpSubgroup_H_conj_mem hypM)

end OddOrder.Peterfalvi.S14


