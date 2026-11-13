-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S15_SSetMemberRFamily
-- name    : OddOrder_Peterfalvi_S15_SSetMemberRFamily
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T16:24:18.849782+00:00
-- url     : https://prove2.me/theorems/504ab685-899e-46f8-aaeb-fc488f885321
-- title:
--   Peterfalvi §9/§13: member $R$-families for the $S$-instance family
-- statement:
--   Formalizes the (5.2.d) orthonormal Dade $R$-families for each member of the honest §9 family $\mathcal{S}$ of the $S$-instance.
--
--   Main declarations: `Hypothesis.sSet_reducible_eq_muColumnSum` (Reducible `𝒮`-members are nonzero μ-column sums); `Hypothesis.sSet_reducible_columns_ne` (The two μ-columns of a reducible `𝒮`-member are distinct); `Hypothesis.sSet_member_conjDiff_supported` (Member−conjugate difference support); `Hypothesis.tauS_muColumn_diff_eq` (The honest Dade image of a reducible `𝒮`-member column difference).
--
--   The bundle also proves 1 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SSetMemberRFamily.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_SSetMemberRFamily.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_BridgeCharacter

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Reducible `𝒮`-members are nonzero μ-column sums** (Peterfalvi (9.8)/(9.11) reverse dichotomy,
`S`-instance).  A reducible member `η ∈ 𝒮 = sSet` bridges into the general kernel-filter family
`S(⊥) = inducedKernelFamily ((derivedInG S).subgroupOf S) ⊥` — the source `ξ ∈ 𝒳` is nontrivial
(`𝒳`: `H ⊄ Ker ξ`) and `induceHU = Ind_{HU}^S` (`induceHU_eq_induce`) — where the landed field
`mu_reducible_dichotomy` dispatches it to its μ-column `∃ j ≠ 0, η = ∑ᵢ μ_{ij}`. -/
theorem Hypothesis.sSet_reducible_eq_muColumnSum [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {η : ClassFunction ↥hyp.S ℂ} (hη : η ∈ sSet (hyp.toTypesIIIIIIVSetupS hG))
    (hirr : ¬ OddOrder.RepresentationTheory.IsIrreducibleCharacter η) :
    ∃ j : Fin hyp.p, j ≠ ⟨0, hyp.p_prime.pos⟩ ∧ η = ∑ i : Fin hyp.q, hyp.mu i j := by
  classical
  have := hyp.finiteG
  obtain ⟨ξ, hξ, rfl⟩ := hη
  -- `ξ ≠ trivial`: else `Ker ξ = univ ⊇ hInHu`, contradicting `ξ ∈ 𝒳`.
  have hξne : ξ ≠ trivialIrreducibleCharacter ↥(huSub (hyp.toTypesIIIIIIVSetupS hG)) := by
    intro htriv
    apply hξ
    rw [htriv]
    simp only [IrreducibleCharacter.coe_trivialIrreducibleCharacter,
      OddOrder.Peterfalvi.S03.characterKernel_trivialClassFunction]
    exact Set.subset_univ _
  -- membership in `S(⊥)` over `huSub`, then transported to `(derivedInG S).subgroupOf S`.
  have hmemHU : induceHU (hyp.toTypesIIIIIIVSetupS hG)
        (ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ)
      ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        (huSub (hyp.toTypesIIIIIIVSetupS hG)) (⊥ : Subgroup ↥hyp.S) := by
    refine ⟨ξ, hξne, ?_, (induceHU_eq_induce (hyp.toTypesIIIIIIVSetupS hG) _)⟩
    intro x hx
    have hx1 : x = 1 := by
      have h2 := Subgroup.mem_subgroupOf.mp (SetLike.mem_coe.mp hx)
      rw [Subgroup.mem_bot] at h2; exact Subtype.ext h2
    rw [hx1]
    exact OddOrder.Peterfalvi.S03.one_mem_characterKernel _
  have hKeq : huSub (hyp.toTypesIIIIIIVSetupS hG) = (derivedInG hyp.S).subgroupOf hyp.S :=
    huSub_eq_derivedInG_subgroupOf _
  have hmem : induceHU (hyp.toTypesIIIIIIVSetupS hG)
        (ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ)
      ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG hyp.S).subgroupOf hyp.S) (⊥ : Subgroup ↥hyp.S) := hKeq ▸ hmemHU
  exact hyp.mu_reducible_dichotomy hmem hirr

/-- **The conjugate of a reducible `𝒮`-member is reducible**: if `η̄` were irreducible then so
would be `η = η̄̄` (`IsIrreducibleCharacter.conj` + `conj_conj`). -/
theorem Hypothesis.sSet_reducible_conj_not_irr [Finite G] (hyp : Hypothesis (G := G))
    {η : ClassFunction ↥hyp.S ℂ}
    (hirr : ¬ OddOrder.RepresentationTheory.IsIrreducibleCharacter η) :
    ¬ OddOrder.RepresentationTheory.IsIrreducibleCharacter (η : ClassFunction ↥hyp.S ℂ).conj := by
  have := hyp.finiteG
  intro h
  apply hirr
  rw [← ClassFunction.conj_conj η]
  exact h.conj

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **The two μ-columns of a reducible `𝒮`-member are distinct**: col`(η) ≠ ` col`(η̄)`, else
`η̄ = ∑ᵢ μ_{i,col(η̄)} = ∑ᵢ μ_{i,col(η)} = η` makes `η` real, contradicting
`sSet_hasNoRealCharacters`
(the family is no-real by `oddCardS`). -/
theorem Hypothesis.sSet_reducible_columns_ne [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {η : ClassFunction ↥hyp.S ℂ} (hη : η ∈ sSet (hyp.toTypesIIIIIIVSetupS hG))
    (hirr : ¬ OddOrder.RepresentationTheory.IsIrreducibleCharacter η) :
    (hyp.sSet_reducible_eq_muColumnSum hG hη hirr).choose ≠
      (hyp.sSet_reducible_eq_muColumnSum hG
        (sSet_closedUnderConjugate (hyp.toTypesIIIIIIVSetupS hG) hη)
        (hyp.sSet_reducible_conj_not_irr hirr)).choose := by
  intro he
  have hnonreal : ¬ ClassFunction.IsReal η :=
    sSet_hasNoRealCharacters (hyp.toTypesIIIIIIVSetupS hG) (hyp.oddCardS hG) hη
  apply hnonreal
  have hjeq := (hyp.sSet_reducible_eq_muColumnSum hG hη hirr).choose_spec.2
  have hkeq := (hyp.sSet_reducible_eq_muColumnSum hG
    (sSet_closedUnderConjugate (hyp.toTypesIIIIIIVSetupS hG) hη)
    (hyp.sSet_reducible_conj_not_irr hirr)).choose_spec.2
  change (η : ClassFunction ↥hyp.S ℂ).conj = η
  rw [hkeq, ← he, ← hjeq]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Member−conjugate difference support** (Clifford-case-agnostic; issue 1017): for any member
`η ∈ 𝒮 = sSet`, `(η̄ − η).support ⊆ A(S)`.  Since `η = Ind_{HU}^S ξ` (`ξ ∈ 𝒳`) this is the landed
`sSet_member_diffsupp`, which holds for *both* Clifford cases: a member and its conjugate always
share
the real, positive degree `η̄(1) = η(1)`, so `1 ∉ Supp(η̄ − η)`.  This frees the `R`-family
diff-support input from the caseB-uniformity route `sSet_caseB_member_diff_supported` (which derives
the
equal degree from `caseB`), so the *same* per-member `R`-family serves caseA and caseB. -/
theorem Hypothesis.sSet_member_conjDiff_supported [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {η : ClassFunction ↥hyp.S ℂ} (hη : η ∈ sSet (hyp.toTypesIIIIIIVSetupS hG)) :
    ((η : ClassFunction ↥hyp.S ℂ).conj - η).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S := by
  have := hyp.finiteG
  let : Fintype G := Fintype.ofFinite G
  obtain ⟨ξ, hξ, rfl⟩ := hη
  exact hyp.sSet_member_diffsupp hG hξ

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **The honest Dade image of a reducible `𝒮`-member column difference** (route B, the core of the
reducible caseB `R`-family): for a reducible `η = ∑ᵢ μ_{ij} ∈ 𝒮` with conjugate `η̄ = ∑ᵢ μ_{ik}`
(`j ≠ k`, both `≠ 0`), the honest `'A(S)`-Dade image is `τ_S(η − η̄) = ∑ᵢ(η_{ij} − η_{ik})`.

The column difference `η − η̄` is `A(S)`-supported (`sSet_caseB_member_diff_supported`), so the
honest
`τ_S` (`dadeHypS`) agrees there with `Ind_S^G` (`sInstance_dade_eq_induce`) and hence with the
`'A0`-Dade `τ_S⁰` (`dadeHypS0`, `sInstance_dade0_eq_induce`, since `A(S) ⊆ A₀(S)`); the per-row
prime-`TI` cross-relation `tauS_mu_cross` then evaluates `τ_S⁰(μ_{ij} − μ_{ik}) = η_{ij} − η_{ik}`,
summed by `ℤ`-linearity of the Dade map. -/
theorem Hypothesis.tauS_muColumn_diff_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    {j k : Fin hyp.p} (hj0 : j ≠ ⟨0, hyp.p_prime.pos⟩) (hk0 : k ≠ ⟨0, hyp.p_prime.pos⟩)
    (hjk : j ≠ k)
    {η : ClassFunction ↥hyp.S ℂ} (hη : η ∈ sSet (hyp.toTypesIIIIIIVSetupS hG))
    (_hηconj : (η : ClassFunction ↥hyp.S ℂ).conj ∈ sSet (hyp.toTypesIIIIIIVSetupS hG))
    (hjeq : η = ∑ i : Fin hyp.q, hyp.mu i j)
    (hkeq : (η : ClassFunction ↥hyp.S ℂ).conj = ∑ i : Fin hyp.q, hyp.mu i k) :
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
        ((hyp.dadeHypS hG).fullDadeIsometryData)
        (η - (η : ClassFunction ↥hyp.S ℂ).conj)
      = ∑ i : Fin hyp.q, (hyp.eta i j - hyp.eta i k) := by
  classical
  have := hyp.finiteG
  let : Fintype ↥hyp.S := Fintype.ofFinite _
  -- `η − η̄ = ∑ᵢ(μ_{ij} − μ_{ik})`.
  have hsub : (η - (η : ClassFunction ↥hyp.S ℂ).conj)
      = ∑ i : Fin hyp.q, (hyp.mu i j - hyp.mu i k) := by
    rw [hkeq, hjeq, ← Finset.sum_sub_distrib]
  -- `A(S)`-support of the column difference (both members of `𝒮`).
  have hAsupp : (η - (η : ClassFunction ↥hyp.S ℂ).conj).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S :=
    by
      rw [show (η - (η : ClassFunction ↥hyp.S ℂ).conj)
          = -((η : ClassFunction ↥hyp.S ℂ).conj - η) from by abel,
        ClassFunction.support_neg]
      exact hyp.sSet_member_conjDiff_supported hG hη
  have hA0supp : (η - (η : ClassFunction ↥hyp.S ℂ).conj).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore0 hyp.S hyp.Sdata) hyp.S :=
    hAsupp.trans (OddOrder.Peterfalvi.S04.supportInSubgroup_mono
      (S10.typePACore_subset_A0Set hyp.Sdata))
  -- the honest `'A`-Dade agrees with the `'A0`-Dade on the `A(S)`-supported column difference.
  have hτeq : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
        ((hyp.dadeHypS hG).fullDadeIsometryData)
        (η - (η : ClassFunction ↥hyp.S ℂ).conj)
      = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
          ((hyp.dadeHypS0 hG).fullDadeIsometryData)
          (η - (η : ClassFunction ↥hyp.S ℂ).conj) := by
    rw [hyp.sInstance_dade_eq_induce hG hnoV hAsupp, hyp.sInstance_dade0_eq_induce hG hnoV hA0supp]
  rw [hτeq, hsub, map_sum]
  refine Finset.sum_congr rfl fun i _ => tauS_mu_cross hG hnoV hyp i hj0 hk0 hjk

open scoped FiniteInduce in
/-- **μ-column degree** (Peterfalvi (13.3.a), case-agnostic): `(∑ᵢ μ_{ij})(1) = q·u` for `j ≠ 0`.
Each per-entry `μ_{ij}(1) = u` (`mu_apply_one_eq_u`), independent of the Clifford case — the
mixed-degree members of `𝒮` are the *irreducible* `q·a`-degree ones, never the reducible
`μ`-columns. -/
theorem Hypothesis.muColumn_apply_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (j : Fin hyp.p) (hj : j ≠ ⟨0, hyp.p_prime.pos⟩) :
    ((∑ i : Fin hyp.q, hyp.mu i j : ClassFunction ↥hyp.S ℂ) : ↥hyp.S → ℂ) 1
      = (hyp.q : ℂ) * (hyp.u : ℂ) := by
  rw [ClassFunction.finset_sum_apply,
    Finset.sum_congr rfl (fun i _ => hyp.mu_apply_one_eq_u hG i j hj),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

open scoped FiniteInduce in
/-- **μ-column self/cross inner product**: `⟨∑ᵢ μ_{ij}, ∑ᵢ μ_{ik}⟩ = q·[j = k]`, from the full-grid
orthonormality `mu_orthonormal`. -/
theorem Hypothesis.muColumn_inner [Finite G] (hyp : Hypothesis (G := G)) (j k : Fin hyp.p) :
    ClassFunction.inner (∑ i : Fin hyp.q, hyp.mu i j) (∑ i : Fin hyp.q, hyp.mu i k)
      = if j = k then (hyp.q : ℂ) else 0 := by
  by_cases hjk : j = k
  · subst hjk; rw [if_pos rfl]; exact hyp.muColumn_inner_self j
  · rw [if_neg hjk, OddOrder.RepresentationTheory.inner_sum_left]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [OddOrder.RepresentationTheory.inner_sum_right]
    exact Finset.sum_eq_zero fun i' _ => by
      rw [hyp.mu_orthonormal i i' j k, if_neg (fun h => hjk h.2)]

open scoped FiniteInduce in
/-- **η-column self/cross inner product**: `⟨∑ᵢ η_{ij}, ∑ᵢ η_{ik}⟩ = q·[j = k]`, from the grid
orthonormality `eta_orthonormal`. -/
theorem Hypothesis.etaColumn_inner [Finite G] (hyp : Hypothesis (G := G)) (j k : Fin hyp.p) :
    ClassFunction.inner (∑ i : Fin hyp.q, hyp.eta i j) (∑ i : Fin hyp.q, hyp.eta i k)
      = if j = k then (hyp.q : ℂ) else 0 := by
  by_cases hjk : j = k
  · subst hjk; rw [if_pos rfl]; exact hyp.etaColumn_inner_self j
  · rw [if_neg hjk, OddOrder.RepresentationTheory.inner_sum_left]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [OddOrder.RepresentationTheory.inner_sum_right]
    exact Finset.sum_eq_zero fun i' _ => by
      rw [OddOrder.Peterfalvi.S16.eta_orthonormal hyp i i' j k, if_neg (fun h => hjk h.2)]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **μ-column differences are `A(S)`-supported** (case-agnostic).  Both columns have degree `q·u`
(`muColumn_apply_one`), so `μ_j − μ_k` vanishes at `1`; each column lies in `𝒮`
(`mu_colSum_mem_sOf_H0` + `sOf_subset_sSet`) whose members are supported on `A(S) ∪ {1}`
(`sSet_member_support_subset`), so the difference avoids `{1}` and lands in `A(S)`.  The
arbitrary-column, Clifford-case-agnostic analogue of `sSet_caseB_member_diff_supported`. -/
theorem Hypothesis.muColumn_diff_supported [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    {j k : Fin hyp.p} (hj : j ≠ ⟨0, hyp.p_prime.pos⟩) (hk : k ≠ ⟨0, hyp.p_prime.pos⟩) :
    ((∑ i : Fin hyp.q, hyp.mu i j) - (∑ i : Fin hyp.q, hyp.mu i k)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S := by
  intro z hz
  have hz0 : ((∑ i : Fin hyp.q, hyp.mu i j) - (∑ i : Fin hyp.q, hyp.mu i k)) z ≠ 0 := hz
  have hxmem : (∑ i : Fin hyp.q, hyp.mu i j) ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) :=
    sOf_subset_sSet _ chief.H0 (hyp.mu_colSum_mem_sOf_H0 hG chief j hj)
  have hymem : (∑ i : Fin hyp.q, hyp.mu i k) ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) :=
    sOf_subset_sSet _ chief.H0 (hyp.mu_colSum_mem_sOf_H0 hG chief k hk)
  have hdeg : ((∑ i : Fin hyp.q, hyp.mu i j : ClassFunction ↥hyp.S ℂ) : ↥hyp.S → ℂ) 1
      = ((∑ i : Fin hyp.q, hyp.mu i k : ClassFunction ↥hyp.S ℂ) : ↥hyp.S → ℂ) 1 := by
    rw [hyp.muColumn_apply_one hG j hj, hyp.muColumn_apply_one hG k hk]
  rcases ClassFunction.support_sub_subset _ _ hz with h | h
  · rcases hyp.sSet_member_support_subset hG hxmem h with h' | h'
    · exact h'
    · exfalso; rw [Set.mem_singleton_iff] at h'; subst h'
      exact hz0 (by rw [ClassFunction.sub_apply, hdeg, sub_self])
  · rcases hyp.sSet_member_support_subset hG hymem h with h' | h'
    · exact h'
    · exfalso; rw [Set.mem_singleton_iff] at h'; subst h'
      exact hz0 (by rw [ClassFunction.sub_apply, hdeg, sub_self])

open scoped FiniteInduce in
/-- **General-column `dadeHypS` cross-relation**: for distinct nonzero columns `j ≠ k`,
`τ_S(∑ᵢ μ_{ij} − ∑ᵢ μ_{ik}) = ∑ᵢ(η_{ij} − η_{ik})`.  The arbitrary-column generalization of
`tauS_muColumn_diff_eq` (which fixes `k` = conjugate of `j`): the honest `A(S)`-Dade agrees with the
`A₀`-Dade on the `A(S)`-supported column difference (`sInstance_dade_eq_induce` /
`sInstance_dade0_eq_induce`), and the per-row prime-`TI` `tauS_mu_cross` evaluates each summand. -/
theorem Hypothesis.dadeHypS_muColumn_diff [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    {j k : Fin hyp.p} (hj : j ≠ ⟨0, hyp.p_prime.pos⟩) (hk : k ≠ ⟨0, hyp.p_prime.pos⟩)
    (hjk : j ≠ k) :
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
        ((hyp.dadeHypS hG).fullDadeIsometryData)
        ((∑ i : Fin hyp.q, hyp.mu i j) - (∑ i : Fin hyp.q, hyp.mu i k))
      = ∑ i : Fin hyp.q, (hyp.eta i j - hyp.eta i k) := by
  classical
  have := hyp.finiteG
  let : Fintype ↥hyp.S := Fintype.ofFinite _
  have hAsupp := hyp.muColumn_diff_supported hG chief hj hk
  have hA0supp := hAsupp.trans (OddOrder.Peterfalvi.S04.supportInSubgroup_mono
    (S10.typePACore_subset_A0Set hyp.Sdata))
  have hτeq : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
        ((hyp.dadeHypS hG).fullDadeIsometryData)
        ((∑ i : Fin hyp.q, hyp.mu i j) - (∑ i : Fin hyp.q, hyp.mu i k))
      = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
          ((hyp.dadeHypS0 hG).fullDadeIsometryData)
          ((∑ i : Fin hyp.q, hyp.mu i j) - (∑ i : Fin hyp.q, hyp.mu i k)) := by
    rw [hyp.sInstance_dade_eq_induce hG hnoV hAsupp, hyp.sInstance_dade0_eq_induce hG hnoV hA0supp]
  rw [hτeq, show ((∑ i : Fin hyp.q, hyp.mu i j) - (∑ i : Fin hyp.q, hyp.mu i k))
      = ∑ i : Fin hyp.q, (hyp.mu i j - hyp.mu i k) from by rw [Finset.sum_sub_distrib], map_sum]
  refine Finset.sum_congr rfl fun i _ => tauS_mu_cross hG hnoV hyp i hj hk hjk

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **The reducible `𝒮`-member `R`-family at EXPLICIT columns `j, k`** (route B core; the
column-parametrized form of `sSet_reducible_memberRFamily`).  For a reducible member
`η = ∑ᵢ μ_{ij} ∈ 𝒮` with conjugate `η̄ = ∑ᵢ μ_{ik}` (`j ≠ k`, both `≠ 0`), the (5.2.d) orthonormal
Dade image family is the `2q`-element signed `η`-grid family
`R(η) = {η_{ij} : i} ∪ {−η_{ik} : i}` (`imageSet = Finset.image (Sum.elim …) univ`), with
`τ_S(η − η̄) = ∑ᵢ(η_{ij} − η_{ik}) = ∑_{α ∈ R(η)} α` (`tauS_muColumn_diff_eq`), orthonormal by
`eta_orthonormal` (distinct columns `j ≠ k`), and in `ℤ[Irr G]` by `eta_mem_ZIrr`.  Exposing
`j, k` as explicit parameters keeps `imageSet` a clean structure literal — its reduction
(`…_ofColumns_imageSet`) is `rfl`, which the (5.2.e) cross-orthogonality
(`sSet_memberRFamily_orthogonal`) needs to destructure the family element-wise. -/
noncomputable def Hypothesis.sSet_reducible_memberRFamily_ofColumns [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    {η : ClassFunction ↥hyp.S ℂ} (hη : η ∈ sSet (hyp.toTypesIIIIIIVSetupS hG))
    (hηconj : (η : ClassFunction ↥hyp.S ℂ).conj ∈ sSet (hyp.toTypesIIIIIIVSetupS hG))
    {j k : Fin hyp.p} (hj0 : j ≠ ⟨0, hyp.p_prime.pos⟩) (hk0 : k ≠ ⟨0, hyp.p_prime.pos⟩)
    (hjk : j ≠ k)
    (hjeq : η = ∑ i : Fin hyp.q, hyp.mu i j)
    (hkeq : (η : ClassFunction ↥hyp.S ℂ).conj = ∑ i : Fin hyp.q, hyp.mu i k) :
    OddOrder.Peterfalvi.S07.OrthonormalCharacterImageFamily
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
        ((hyp.dadeHypS hG).fullDadeIsometryData)) η := by
  classical
  haveI := hyp.finiteG
  letI : Fintype ↥hyp.S := Fintype.ofFinite _
  -- the honest Dade image `τ_S(η − η̄) = ∑ᵢ(η_{ij} − η_{ik})`.
  have hcross := hyp.tauS_muColumn_diff_eq hG hnoV hj0 hk0 hjk hη hηconj hjeq hkeq
  -- the `2q`-element signed `η`-grid family.
  set g : Fin hyp.q ⊕ Fin hyp.q → ClassFunction G ℂ :=
    Sum.elim (fun i => hyp.eta i j) (fun i => -hyp.eta i k) with hg
  have hg_inner : ∀ x y : Fin hyp.q ⊕ Fin hyp.q,
      ClassFunction.inner (g x) (g y) = if x = y then (1 : ℂ) else 0 := by
    intro x y
    rcases x with a | a <;> rcases y with b | b <;>
      simp only [hg, Sum.elim_inl, Sum.elim_inr]
    · rw [OddOrder.Peterfalvi.S16.eta_orthonormal hyp a b j j]
      by_cases hab : a = b <;> simp [hab, Sum.inl.injEq]
    · rw [ClassFunction.inner_neg_right, OddOrder.Peterfalvi.S16.eta_orthonormal hyp a b j k,
        if_neg (fun h => hjk h.2)]
      simp
    · rw [ClassFunction.inner_neg_left, OddOrder.Peterfalvi.S16.eta_orthonormal hyp a b k j,
        if_neg (fun h => hjk h.2.symm)]
      simp
    · rw [ClassFunction.inner_neg_left, ClassFunction.inner_neg_right, neg_neg,
        OddOrder.Peterfalvi.S16.eta_orthonormal hyp a b k k]
      by_cases hab : a = b <;> simp [hab, Sum.inr.injEq]
  have hg_inj : Function.Injective g := by
    intro x y hxy
    have h1 := hg_inner x y
    rw [hxy, hg_inner y y, if_pos rfl] at h1
    by_contra hne
    rw [if_neg hne] at h1
    exact one_ne_zero h1
  exact
    { imageSet := Finset.image g Finset.univ
      mem_ZIrr := by
        intro α hα
        rw [Finset.mem_image] at hα
        obtain ⟨x, -, rfl⟩ := hα
        rcases x with a | a <;> simp only [hg, Sum.elim_inl, Sum.elim_inr]
        · exact OddOrder.Peterfalvi.S16.eta_mem_ZIrr hyp a j
        · exact Submodule.neg_mem _ (OddOrder.Peterfalvi.S16.eta_mem_ZIrr hyp a k)
      orthonormal := by
        intro α hα β hβ
        rw [Finset.mem_image] at hα hβ
        obtain ⟨x, -, rfl⟩ := hα
        obtain ⟨y, -, rfl⟩ := hβ
        rw [hg_inner x y]
        by_cases hxy : x = y
        · rw [if_pos hxy, if_pos (by rw [hxy])]
        · rw [if_neg hxy, if_neg (fun h => hxy (hg_inj h))]
      image_eq := by
        -- `τ_S(η − η̄) = ∑_{α ∈ R(η)} α`.
        rw [hcross, Finset.sum_image (fun x _ y _ h => hg_inj h), Fintype.sum_sum_type]
        simp only [hg, Sum.elim_inl, Sum.elim_inr, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
        abel }

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
open scoped Classical in
/-- **`imageSet` of the column-parametrized reducible `R`-family** (`rfl`).  The signed `η`-grid
family `R(η) = {η_{ij}} ∪ {−η_{ik}}` as `Finset.image (Sum.elim (η·ⱼ) (−η·ₖ)) univ`. -/
theorem Hypothesis.sSet_reducible_memberRFamily_ofColumns_imageSet [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    {η : ClassFunction ↥hyp.S ℂ} (hη : η ∈ sSet (hyp.toTypesIIIIIIVSetupS hG))
    (hηconj : (η : ClassFunction ↥hyp.S ℂ).conj ∈ sSet (hyp.toTypesIIIIIIVSetupS hG))
    {j k : Fin hyp.p} (hj0 : j ≠ ⟨0, hyp.p_prime.pos⟩) (hk0 : k ≠ ⟨0, hyp.p_prime.pos⟩)
    (hjk : j ≠ k)
    (hjeq : η = ∑ i : Fin hyp.q, hyp.mu i j)
    (hkeq : (η : ClassFunction ↥hyp.S ℂ).conj = ∑ i : Fin hyp.q, hyp.mu i k) :
    (hyp.sSet_reducible_memberRFamily_ofColumns hG hnoV hη hηconj hj0 hk0 hjk
        hjeq hkeq).imageSet
      = Finset.image (Sum.elim (fun i : Fin hyp.q => hyp.eta i j)
          (fun i : Fin hyp.q => -hyp.eta i k)) Finset.univ :=
  rfl

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Per-member orthonormal Dade `R`-family for a REDUCIBLE `𝒮`-member** (route B; the honest
`S`-instance analogue of the M-side column branch of `caseB_sOf_memberRFamily`).  The thin wrapper
over `…_ofColumns` that dispatches `η, η̄` to their μ-columns `j = ` col`(η)`, `k = ` col`(η̄)` via
the
(9.11) reverse dichotomy `sSet_reducible_eq_muColumnSum` (`.choose`), with `j ≠ k` from
non-realness.  See `…_ofColumns` for the family content. -/
noncomputable def Hypothesis.sSet_reducible_memberRFamily [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    {η : ClassFunction ↥hyp.S ℂ} (hη : η ∈ sSet (hyp.toTypesIIIIIIVSetupS hG))
    (hirr : ¬ OddOrder.RepresentationTheory.IsIrreducibleCharacter η) :
    OddOrder.Peterfalvi.S07.OrthonormalCharacterImageFamily
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
        ((hyp.dadeHypS hG).fullDadeIsometryData)) η :=
  hyp.sSet_reducible_memberRFamily_ofColumns hG hnoV hη
    (sSet_closedUnderConjugate (hyp.toTypesIIIIIIVSetupS hG) hη)
    (hyp.sSet_reducible_eq_muColumnSum hG hη hirr).choose_spec.1
    (hyp.sSet_reducible_eq_muColumnSum hG
      (sSet_closedUnderConjugate (hyp.toTypesIIIIIIVSetupS hG) hη)
      (hyp.sSet_reducible_conj_not_irr hirr)).choose_spec.1
    (hyp.sSet_reducible_columns_ne hG hη hirr)
    (hyp.sSet_reducible_eq_muColumnSum hG hη hirr).choose_spec.2
    (hyp.sSet_reducible_eq_muColumnSum hG
      (sSet_closedUnderConjugate (hyp.toTypesIIIIIIVSetupS hG) hη)
      (hyp.sSet_reducible_conj_not_irr hirr)).choose_spec.2

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Per-member orthonormal Dade `R`-family over `𝒮 = sSet`** (issue 1017, the `R` input of the
(5.7)
coherence engine `uniform_degree_coherence_of_families`, the honest `S`-instance analogue of the
M-instance `caseB_sOf_memberRFamily`, `S13_MaximalIII_IV.lean:546`).  **Clifford-case-agnostic**:
the
construction depends on nothing beyond `η ∈ 𝒮` and its conjugate (the two Clifford cases were only
ever
threaded to obtain the member+conjugate equal-degree fact, which is automatic — `η̄(1) = η(1)`), so
the
*same* `R`-family feeds both the caseB Galois engine (`sSet_coherent_dade_caseB`) and the caseA
non-Galois (9.11.7)–(9.11.8) coherent-pair budget. Every member is dispatched to its (5.2.d)
`R`-datum:

* **irreducible member `η`** — the 2-element signed Dade image family
  `dadeOrthonormalCharacterImageFamilyOfDiff` (`η^τ − η̄^τ = ε·(μ − ν)`), assembled sorry-free from
  the landed inputs: non-realness (`sSet_hasNoRealCharacters` via `oddCardS`) and the conjugate
  difference support `(η̄ − η).support ⊆ A(S)` (`sSet_member_conjDiff_supported`, case-agnostic);
* **reducible member `η = μ_j` (a nonzero μ-column sum)** — the `2q`-element signed-`η` family
  `R(η) = {η_{ij}} ∪ {−η_{ik}}`, **built sorry-free by route B** (`sSet_reducible_memberRFamily`,
  above): the (9.11) reverse dichotomy `mu_reducible_dichotomy` gives the columns `j, k` of `η, η̄`,
  and `τ_S(η − η̄) = ∑ᵢ(η_{ij} − η_{ik})` from the honest all-rows prime-`TI` cross-relation
  `tauS_mu_cross` (itself `S16.eta_diff_rigidity`, sorry-free from the abstract fields).

**Route A vs route B** (correcting the prior 748e6a27 record): route A (`certainTypeR @ hyp46S`)
is genuinely inapplicable on the S-side — the abstract `hyp.mu` (from `certainTypeS`) is *not*
grounded to `residueS.mu2`, and `certainTypeR` is over `dadeHypS0` not `dadeHypS`.  But route B
(the abstract generalization of the proven `tauS_mu_row0_cross`) **is** buildable and needs **no**
`prTIirr_id`/9014 content: the cross-relation is discharged entirely from the abstract `Hypothesis`
grid fields (`mu_apply_of_not_mem_W2`, `mu_orthonormal`, `eta_orthonormal`, `eta_diff_rigidity`).
The only architectural cost is that route B lives **downstream of `S16_GridExpansion`**, hence this
whole caseB coherence chain was relocated here from `S15_SAndT_Setup.HypothesisBasics`. -/
noncomputable def Hypothesis.sSet_memberRFamily [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    {η : ClassFunction ↥hyp.S ℂ} (hη : η ∈ sSet (hyp.toTypesIIIIIIVSetupS hG)) :
    OddOrder.Peterfalvi.S07.OrthonormalCharacterImageFamily
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
        ((hyp.dadeHypS hG).fullDadeIsometryData)) η := by
  classical
  by_cases hirr : OddOrder.RepresentationTheory.IsIrreducibleCharacter η
  · -- irreducible member: the 2-element signed Dade image family (assembled sorry-free)
    refine OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff
      (hyp.dadeHypS hG) ⟨η, hirr⟩ ?_ ?_
    · exact sSet_hasNoRealCharacters (hyp.toTypesIIIIIIVSetupS hG) (hyp.oddCardS hG) hη
    · exact hyp.sSet_member_conjDiff_supported hG hη
  · -- reducible member (`η = μ_j`): the `2q`-element signed-η `R`-family, built above by route B
    -- (`sSet_reducible_memberRFamily`), verified sorry-free (`tauS_mu_cross` +
    -- `mu_reducible_dichotomy`).  Route A (`certainTypeR`) is genuinely inapplicable on the S-side
    -- (`hyp.mu` from `certainTypeS`, ungrounded), but route B is buildable from the abstract fields
    -- —
    -- refuting the prior (748e6a27) "9014-blocked" record.
    exact hyp.sSet_reducible_memberRFamily hG hnoV hη hirr

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Distinct μ-columns from a vanishing cross inner product**: if `⟨∑ᵢ μ_{ia}, ∑ᵢ μ_{ib}⟩ = 0`
then `a ≠ b` (else the self-norm `⟨∑ᵢ μ_{ia}, ∑ᵢ μ_{ia}⟩ = q ≠ 0` by `mu_orthonormal`). -/
theorem Hypothesis.mu_colSum_ne_of_inner_zero [Finite G] (hyp : Hypothesis (G := G))
    {a b : Fin hyp.p}
    (h : ClassFunction.inner (∑ i : Fin hyp.q, hyp.mu i a)
      (∑ i : Fin hyp.q, hyp.mu i b) = 0) :
    a ≠ b := by
  classical
  have := hyp.finiteG
  rintro rfl
  have hself : ClassFunction.inner (∑ i : Fin hyp.q, hyp.mu i a)
      (∑ i : Fin hyp.q, hyp.mu i a) = (hyp.q : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_sum_left]
    calc ∑ i : Fin hyp.q, ClassFunction.inner (hyp.mu i a) (∑ i' : Fin hyp.q, hyp.mu i' a)
        = ∑ i : Fin hyp.q, ∑ i' : Fin hyp.q,
            ClassFunction.inner (hyp.mu i a) (hyp.mu i' a) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [OddOrder.RepresentationTheory.inner_sum_right]
      _ = ∑ i : Fin hyp.q, ∑ i' : Fin hyp.q, if i = i' then (1 : ℂ) else 0 := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
          rw [hyp.mu_orthonormal i i' a a]; simp
      _ = ∑ _i : Fin hyp.q, (1 : ℂ) := by
          refine Finset.sum_congr rfl fun i _ => ?_; simp
      _ = (hyp.q : ℂ) := by simp
  rw [hself] at h
  exact absurd h (Nat.cast_ne_zero.mpr hyp.q_prime.pos.ne')

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **The honest `'A0`-Dade image of an `A(S)`-supported class function vanishes on the regular
set**
(the vanishing core of `S15.coherentIndS_image_inner_eta_eq_zero`, generalized from `ζ − ζ̄` to any
`A(S)`-supported `f`).  For `f.support ⊆ A(S) = S10.typePACore S` and a regular `W`-element
`x ∈ conjClassSet (W ∖ (W₁ ∪ W₂))` (a `typePV`-point of the `S`-data, hence in `A₀(S)`), the Dade
map reads the source at the representative `w`, which is `0` because `A(S) ⊆ S' = derivedInG S`
while a regular `W`-element lies outside `S'` (`typePData_typePV_not_mem_derived`). -/
theorem Hypothesis.dadeS0_apply_eq_zero_of_regular [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd
    G)
    (hyp : Hypothesis (G := G))
    {f : ClassFunction ↥hyp.S ℂ}
    (hf : f.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S)
    {x : G} (hx : x ∈ OddOrder.GroupTheory.conjClassSet
      ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G)))) :
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
        ((hyp.dadeHypS0 hG).fullDadeIsometryData) f x = 0 := by
  classical
  have hA0supp : f.support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore0 hyp.S hyp.Sdata) hyp.S :=
    hf.trans (OddOrder.Peterfalvi.S04.supportInSubgroup_mono
      (S10.typePACore_subset_A0Set hyp.Sdata))
  obtain ⟨w, hw, g, hg⟩ := OddOrder.GroupTheory.mem_conjClassSet.mp hx
  rw [← (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
    ((hyp.dadeHypS0 hG).fullDadeIsometryData) f).of_isConj
      (isConj_iff.mpr ⟨g, hg⟩)]
  have hwV : w ∈ OddOrder.GroupTheory.typePV hyp.S hyp.Sdata := by
    refine ⟨?_, ?_⟩
    · have hWeq : (hyp.Sdata.W : Set G) = (hyp.W : Set G) := by
        rw [hyp.Sdata.W_eq, hyp.Sdata_W1_eq, hyp.Sdata_W2_eq, ← hyp.W_eq_join]
      rw [hWeq]; exact hw.1
    · rw [hyp.Sdata_W1_eq, hyp.Sdata_W2_eq]; exact hw.2
  have hwA0 : w ∈ S10.typePACore0 hyp.S hyp.Sdata :=
    Or.inr (OddOrder.GroupTheory.subset_conjClassSetIn hwV)
  rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support (hyp.dadeHypS0 hG)
    ((hyp.dadeHypS0 hG).fullDadeIsometryData) hA0supp]
  let a : {a : G // a ∈ S10.typePACore0 hyp.S hyp.Sdata} := ⟨w, hwA0⟩
  have hwh : w ∈ (hyp.dadeHypS0 hG).hCoset a :=
    ⟨1, (hyp.dadeHypS0 hG).H a |>.one_mem, by simp [a]⟩
  rw [(hyp.dadeHypS0 hG).isDadeMap_dadeMap.map_eq_of_mem_hCoset _ a hwh]
  by_contra hne
  have hwSupp : (⟨w, (hyp.dadeHypS0 hG).mem_L hwA0⟩ : ↥hyp.S) ∈ f.support :=
    ClassFunction.mem_support.mpr hne
  have hwA : w ∈ S10.typePACore hyp.S := hf hwSupp
  have hwDeriv : w ∈ derivedInG hyp.S := S10.typePACore_subset_derived hwA
  exact (OddOrder.Peterfalvi.S10.typePData_typePV_not_mem_derived hyp.Sdata hwV) hwDeriv

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **`imageSet`-reduction of the caseB dispatcher, irreducible branch**: for an irreducible member
`η`, `(sSet_memberRFamily …).imageSet = (dadeOrthonormalCharacterImageFamilyOfDiff …).imageSet`
(the specific realness/support proofs exposed existentially, as on the M-side
`caseB_sOf_memberRFamily_imageSet_of_irr`). -/
theorem Hypothesis.sSet_memberRFamily_imageSet_of_irr [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    {η : ClassFunction ↥hyp.S ℂ} (hη : η ∈ sSet (hyp.toTypesIIIIIIVSetupS hG))
    (hirr : OddOrder.RepresentationTheory.IsIrreducibleCharacter η) :
    ∃ (hr : ¬ ClassFunction.IsReal (η : ClassFunction ↥hyp.S ℂ))
      (hs : ((η : ClassFunction ↥hyp.S ℂ).conj - (η : ClassFunction ↥hyp.S ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S),
      (hyp.sSet_memberRFamily hG hnoV hη).imageSet =
        (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff (hyp.dadeHypS hG)
            ⟨η, hirr⟩ hr hs).imageSet := by
  refine ⟨sSet_hasNoRealCharacters (hyp.toTypesIIIIIIVSetupS hG) (hyp.oddCardS hG) hη,
    hyp.sSet_member_conjDiff_supported hG hη, ?_⟩
  unfold Hypothesis.sSet_memberRFamily
  rw [dif_pos hirr]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
open scoped Classical in
/-- **`imageSet`-reduction of the caseB dispatcher, reducible branch**: for a reducible member
`η = ∑ᵢ μ_{ij}`, `(sSet_memberRFamily …).imageSet` is the signed `η`-grid family
`{η_{ij}} ∪ {−η_{ik}}`, with the columns `j = ` col`(η)`, `k = ` col`(η̄)` and the μ-column
identities `η = ∑ᵢ μ_{ij}`, `η̄ = ∑ᵢ μ_{ik}` exposed (the (5.2.e) column-disjointness inputs). -/
theorem Hypothesis.sSet_memberRFamily_imageSet_of_red [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    {η : ClassFunction ↥hyp.S ℂ} (hη : η ∈ sSet (hyp.toTypesIIIIIIVSetupS hG))
    (hirr : ¬ OddOrder.RepresentationTheory.IsIrreducibleCharacter η) :
    ∃ (j k : Fin hyp.p), η = ∑ i : Fin hyp.q, hyp.mu i j ∧
      (η : ClassFunction ↥hyp.S ℂ).conj = ∑ i : Fin hyp.q, hyp.mu i k ∧
      (hyp.sSet_memberRFamily hG hnoV hη).imageSet =
        Finset.image (Sum.elim (fun i : Fin hyp.q => hyp.eta i j)
          (fun i : Fin hyp.q => -hyp.eta i k)) Finset.univ := by
  refine ⟨(hyp.sSet_reducible_eq_muColumnSum hG hη hirr).choose,
    (hyp.sSet_reducible_eq_muColumnSum hG
      (sSet_closedUnderConjugate (hyp.toTypesIIIIIIVSetupS hG) hη)
      (hyp.sSet_reducible_conj_not_irr hirr)).choose,
    (hyp.sSet_reducible_eq_muColumnSum hG hη hirr).choose_spec.2,
    (hyp.sSet_reducible_eq_muColumnSum hG
      (sSet_closedUnderConjugate (hyp.toTypesIIIIIIVSetupS hG) hη)
      (hyp.sSet_reducible_conj_not_irr hirr)).choose_spec.2, ?_⟩
  rw [show (hyp.sSet_memberRFamily hG hnoV hη).imageSet
        = (hyp.sSet_reducible_memberRFamily hG hnoV hη hirr).imageSet from by
    unfold Hypothesis.sSet_memberRFamily; rw [dif_neg hirr]]
  exact hyp.sSet_reducible_memberRFamily_ofColumns_imageSet hG hnoV hη
    (sSet_closedUnderConjugate (hyp.toTypesIIIIIIVSetupS hG) hη)
    (hyp.sSet_reducible_eq_muColumnSum hG hη hirr).choose_spec.1
    (hyp.sSet_reducible_eq_muColumnSum hG
      (sSet_closedUnderConjugate (hyp.toTypesIIIIIIVSetupS hG) hη)
      (hyp.sSet_reducible_conj_not_irr hirr)).choose_spec.1
    (hyp.sSet_reducible_columns_ne hG hη hirr)
    (hyp.sSet_reducible_eq_muColumnSum hG hη hirr).choose_spec.2
    (hyp.sSet_reducible_eq_muColumnSum hG
      (sSet_closedUnderConjugate (hyp.toTypesIIIIIIVSetupS hG) hη)
      (hyp.sSet_reducible_conj_not_irr hirr)).choose_spec.2

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **The irreducible member's Dade `R`-family is orthogonal to the whole `η`-grid** (the irr×red /
red×irr core; the (13.19.b) rigidity engine applied to the `S`-instance Dade image constituents).
For an irreducible `φ ∈ 𝒮`, the two constituents `ε·μ, −ε·ν` of `τ_S(φ − φ̄)`
(`dadeOrthonormalCharacterImageFamilyOfDiff.imageSet`) are norm-one virtual characters whose signed
difference `τ_S(φ − φ̄)` vanishes on the regular set `Ŵ^G` (`dadeS0_apply_eq_zero_of_regular` after
the `'A→'A0`-Dade bridge), so `eta_orthogonal_of_norm_one_pair_vanish` gives `⟨η_{ij}, α⟩ = 0` for
every `α ∈ R(φ)`. -/
theorem Hypothesis.sSet_irr_memberRFamily_eta_inner [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    {φ : ClassFunction ↥hyp.S ℂ} (_hφ : φ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG))
    (hφirr : OddOrder.RepresentationTheory.IsIrreducibleCharacter φ)
    (hr : ¬ ClassFunction.IsReal (φ : ClassFunction ↥hyp.S ℂ))
    (hs : ((φ : ClassFunction ↥hyp.S ℂ).conj - (φ : ClassFunction ↥hyp.S ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S)
    {α : ClassFunction G ℂ}
    (hα : α ∈ (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff (hyp.dadeHypS
        hG) ⟨φ, hφirr⟩ hr hs).imageSet)
    (i : Fin hyp.q) (j : Fin hyp.p) :
    ClassFunction.inner (hyp.eta i j) α = 0 := by
  classical
  -- capture the two-element `CharacterDifferenceImage` `cd` (`R(φ) = {ε·μ, −ε·ν}`).
  obtain ⟨cd, hcd⟩ :
      ∃ cd : OddOrder.Peterfalvi.S07.CharacterDifferenceImage (G := G)
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
          ((hyp.dadeHypS hG).fullDadeIsometryData))
        (φ : ClassFunction ↥hyp.S ℂ),
        OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff (hyp.dadeHypS hG) ⟨φ,
            hφirr⟩ hr hs = cd.toOrthonormalImage := ⟨_, rfl⟩
  rw [hcd] at hα
  simp only [OddOrder.Peterfalvi.S07.CharacterDifferenceImage.toOrthonormalImage,
    Finset.mem_insert, Finset.mem_singleton] at hα
  -- `μ, ν` norms / `ZIrr` facts.
  have hμZ : cd.muClassFunction ∈ ZIrr G := cd.mu.mem_ZIrr
  have hνZ : cd.nuClassFunction ∈ ZIrr G := cd.nu.mem_ZIrr
  have hμ1 : ClassFunction.inner cd.muClassFunction cd.muClassFunction = 1 := by
    have h := OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite cd.mu cd.mu
    rwa [if_pos rfl] at h
  have hν1 : ClassFunction.inner cd.nuClassFunction cd.nuClassFunction = 1 := by
    have h := OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite cd.nu cd.nu
    rwa [if_pos rfl] at h
  have hμν : ClassFunction.inner cd.muClassFunction cd.nuClassFunction = 0 := by
    have h := OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite cd.mu cd.nu
    rwa [if_neg cd.distinct] at h
  have hνμ : ClassFunction.inner cd.nuClassFunction cd.muClassFunction = 0 := by
    have h := OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite cd.nu cd.mu
    rwa [if_neg (Ne.symm cd.distinct)] at h
  have hsign : (cd.sign : ℂ) * (cd.sign : ℂ) = 1 := by
    have := cd.sign_mul_self; exact_mod_cast congrArg (Int.cast : ℤ → ℂ) this
  -- `φ − φ̄` is `A(S)`-supported (`hs` up to sign), hence `A₀(S)`-supported.
  have hdiffsupp' : ((φ : ClassFunction ↥hyp.S ℂ) - (φ : ClassFunction ↥hyp.S ℂ).conj).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S := by
    rw [show (φ : ClassFunction ↥hyp.S ℂ) - (φ : ClassFunction ↥hyp.S ℂ).conj =
        -((φ : ClassFunction ↥hyp.S ℂ).conj - (φ : ClassFunction ↥hyp.S ℂ)) by abel,
      ClassFunction.support_neg]
    exact hs
  have hA0supp' : ((φ : ClassFunction ↥hyp.S ℂ) - (φ : ClassFunction ↥hyp.S ℂ).conj).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore0 hyp.S hyp.Sdata) hyp.S :=
    hdiffsupp'.trans (OddOrder.Peterfalvi.S04.supportInSubgroup_mono
      (S10.typePACore_subset_A0Set hyp.Sdata))
  -- the signed difference `ε·μ − ε·ν = τ_S(φ − φ̄) = τ_S⁰(φ − φ̄)` (the `'A→'A0`-Dade bridge).
  have hcdimg : (cd.sign : ℂ) • cd.muClassFunction - (cd.sign : ℂ) • cd.nuClassFunction
      = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
          ((hyp.dadeHypS0 hG).fullDadeIsometryData)
          ((φ : ClassFunction ↥hyp.S ℂ) - (φ : ClassFunction ↥hyp.S ℂ).conj) := by
    rw [hyp.sInstance_dade0_eq_induce hG hnoV hA0supp',
      ← hyp.sInstance_dade_eq_induce hG hnoV hdiffsupp',
      cd.image_eq, smul_sub, Int.cast_smul_eq_zsmul ℂ, Int.cast_smul_eq_zsmul ℂ]
  -- the difference vanishes on the regular set.
  have hvanish : ∀ y ∈ OddOrder.GroupTheory.conjClassSet
      ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
      ((cd.sign : ℂ) • cd.muClassFunction - (cd.sign : ℂ) • cd.nuClassFunction) y = 0 := by
    intro y hy
    rw [hcdimg]
    exact hyp.dadeS0_apply_eq_zero_of_regular hG hdiffsupp' hy
  have hvanish' : ∀ y ∈ OddOrder.GroupTheory.conjClassSet
      ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
      ((cd.sign : ℂ) • cd.nuClassFunction - (cd.sign : ℂ) • cd.muClassFunction) y = 0 := by
    intro y hy
    rw [show (cd.sign : ℂ) • cd.nuClassFunction - (cd.sign : ℂ) • cd.muClassFunction
        = -((cd.sign : ℂ) • cd.muClassFunction - (cd.sign : ℂ) • cd.nuClassFunction) by abel,
      ClassFunction.neg_apply, hvanish y hy, neg_zero]
  -- `ZIrr` / norm inputs for the (13.19.b) rigidity engine.
  have hpsiZ : (cd.sign : ℂ) • cd.muClassFunction ∈ ZIrr G := by
    rw [Int.cast_smul_eq_zsmul ℂ]; exact (ZIrr G).smul_mem cd.sign hμZ
  have hconjZ : (cd.sign : ℂ) • cd.nuClassFunction ∈ ZIrr G := by
    rw [Int.cast_smul_eq_zsmul ℂ]; exact (ZIrr G).smul_mem cd.sign hνZ
  have hpsi1 : ClassFunction.inner ((cd.sign : ℂ) • cd.muClassFunction)
      ((cd.sign : ℂ) • cd.muClassFunction) = 1 := by
    rw [ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right, hμ1,
      mul_one, star_intCast]; exact hsign
  have hconj1 : ClassFunction.inner ((cd.sign : ℂ) • cd.nuClassFunction)
      ((cd.sign : ℂ) • cd.nuClassFunction) = 1 := by
    rw [ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right, hν1,
      mul_one, star_intCast]; exact hsign
  have hcross : ClassFunction.inner ((cd.sign : ℂ) • cd.muClassFunction)
      ((cd.sign : ℂ) • cd.nuClassFunction) = 0 := by
    rw [ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right, hμν,
      mul_zero, mul_zero]
  have hcross' : ClassFunction.inner ((cd.sign : ℂ) • cd.nuClassFunction)
      ((cd.sign : ℂ) • cd.muClassFunction) = 0 := by
    rw [ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right, hνμ,
      mul_zero, mul_zero]
  have hvpsi := OddOrder.Peterfalvi.S16.eta_orthogonal_of_norm_one_pair_vanish hyp
    hpsiZ hconjZ hpsi1 hconj1 hcross hvanish i j
  have hvconj := OddOrder.Peterfalvi.S16.eta_orthogonal_of_norm_one_pair_vanish hyp
    hconjZ hpsiZ hconj1 hpsi1 hcross' hvanish' i j
  rcases hα with rfl | rfl
  · rw [← Int.cast_smul_eq_zsmul ℂ]; exact hvpsi
  · rw [← Int.cast_smul_eq_zsmul ℂ, Int.cast_neg, neg_smul, ClassFunction.inner_neg_right, hvconj,
      neg_zero]

set_option maxHeartbeats 1600000 in
-- the `dadeHypS`-support defeq (through the isometry data) is feasible but expensive; discharged
-- once here so the `2×2` `hRorth` split in `sSet_memberRFamily_orthogonal` need not re-pay it.
open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **irr × irr `R`-family orthogonality, `S`-instance form**: the (5.2.e)
`dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal` (`S08_YsetInner`) specialized to the honest
`S`-instance Dade `dadeHypS hG` with the `A(S)` supports, isolating the (feasible-but-expensive)
`dadeHypS`-support defeq in one focused lemma (so the (5.2.e) `2×2` case split in
`sSet_memberRFamily_orthogonal` does not re-pay it under its large local context — the
`S`-instance analogue of the M-side `dadeOfDiff_orthogonal_dadeOfDiff_typeP`). -/
theorem Hypothesis.dadeOfDiff_orthogonal_typeP_S [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (x χ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.S)
    (hxreal : ¬ ClassFunction.IsReal (x : ClassFunction ↥hyp.S ℂ))
    (hxdiffsupp : ((x : ClassFunction ↥hyp.S ℂ).conj - (x : ClassFunction ↥hyp.S ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S)
    (hχreal : ¬ ClassFunction.IsReal (χ : ClassFunction ↥hyp.S ℂ))
    (hχdiffsupp : ((χ : ClassFunction ↥hyp.S ℂ).conj - (χ : ClassFunction ↥hyp.S ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S)
    (hxχ : ClassFunction.inner (x : ClassFunction ↥hyp.S ℂ) (χ : ClassFunction ↥hyp.S ℂ) = 0)
    (hxχbar :
      ClassFunction.inner (x : ClassFunction ↥hyp.S ℂ) (χ : ClassFunction ↥hyp.S ℂ).conj = 0)
    (hxbarχ :
      ClassFunction.inner (x : ClassFunction ↥hyp.S ℂ).conj (χ : ClassFunction ↥hyp.S ℂ) = 0)
    (hxbarχbar : ClassFunction.inner (x : ClassFunction ↥hyp.S ℂ).conj
      (χ : ClassFunction ↥hyp.S ℂ).conj = 0) :
    (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff (hyp.dadeHypS hG) x
        hxreal hxdiffsupp).Orthogonal
      (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff (hyp.dadeHypS hG) χ
          hχreal hχdiffsupp) :=
  OddOrder.Peterfalvi.S08.dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal
    (hyp.dadeHypS hG) hxreal hxdiffsupp hχreal hχdiffsupp
    hxχ hxχbar hxbarχ hxbarχbar

set_option maxHeartbeats 1600000 in
-- the irr×irr branch matches the dispatched families against the (5.2.e) `dadeOfDiff` orthogonality
-- through the `dadeHypS` isometry-data defeq; the whole `2×2` split runs above the default budget.
open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **(5.2.e) cross-orthogonality of the caseB per-member `R`-families** (issue 1017, the `hRorth`
input of `uniform_degree_coherence_of_families`, the honest `S`-instance analogue of the M-instance
`caseB_sOf_memberRFamily_orthogonal`).  For members `φ, ξ ∈ 𝒮` with `⟨φ, ξ⟩ = 0` and `⟨φ, ξ̄⟩ = 0`
(distinct non-conjugate members), the Dade image families `R(φ)`, `R(ξ)` are orthogonal.

A `2×2` case split on the member dichotomy (irreducible / reducible-column), on the `imageSet`
reductions `sSet_memberRFamily_imageSet_of_{irr,red}`:

* **irr × irr** — the landed (5.2.e) `dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal`
  (`S08_YsetInner`), with the two extra scalars `⟨φ̄, ξ⟩`, `⟨φ̄, ξ̄⟩` the `star`-conjugates of
  `⟨φ, ξ̄⟩`, `⟨φ, ξ⟩` (`inner_conj_conj`), so `0`;
* **irr × red** / **red × irr** — `sSet_irr_memberRFamily_eta_inner` (`⟨η-grid, R(irr)⟩ = 0`
  from the (13.19.b) rigidity engine), transported by `inner_conj_symm` / `inner_neg`;
* **red × red** — `eta_orthonormal`, the four columns pairwise distinct
(`mu_colSum_ne_of_inner_zero`
  on `⟨φ, ξ⟩ = ⟨φ, ξ̄⟩ = ⟨φ̄, ξ⟩ = ⟨φ̄, ξ̄⟩ = 0`, so `{jφ, kφ} ∩ {jξ, kξ} = ∅`). -/
theorem Hypothesis.sSet_memberRFamily_orthogonal [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    {φ ξ : ClassFunction ↥hyp.S ℂ}
    (hφ : φ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG)) (hξ : ξ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG))
    (h1 : ClassFunction.inner φ ξ = 0)
    (h2 : ClassFunction.inner φ ξ.conj = 0) :
    (hyp.sSet_memberRFamily hG hnoV hφ).Orthogonal
      (hyp.sSet_memberRFamily hG hnoV hξ) := by
  classical
  -- the two extra vanishing inners `⟨φ̄, ξ⟩ = ⟨φ̄, ξ̄⟩ = 0` (`inner_conj_conj`).
  have hbφξ : ClassFunction.inner φ.conj ξ = 0 := by
    rw [← ClassFunction.conj_conj ξ, OddOrder.RepresentationTheory.inner_conj_conj, h2, star_zero]
  have hbφξb : ClassFunction.inner φ.conj ξ.conj = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_conj, h1, star_zero]
  intro α hα β hβ
  by_cases hφirr : OddOrder.RepresentationTheory.IsIrreducibleCharacter φ <;>
    by_cases hξirr : OddOrder.RepresentationTheory.IsIrreducibleCharacter ξ
  · -- irr × irr
    obtain ⟨hrφ, hsφ, hφeq⟩ := hyp.sSet_memberRFamily_imageSet_of_irr hG hnoV hφ hφirr
    obtain ⟨hrξ, hsξ, hξeq⟩ := hyp.sSet_memberRFamily_imageSet_of_irr hG hnoV hξ hξirr
    rw [hφeq] at hα
    rw [hξeq] at hβ
    exact hyp.dadeOfDiff_orthogonal_typeP_S hG ⟨φ, hφirr⟩ ⟨ξ, hξirr⟩ hrφ hsφ hrξ hsξ
      h1 h2 hbφξ hbφξb α hα β hβ
  · -- irr × red
    obtain ⟨hrφ, hsφ, hφeq⟩ := hyp.sSet_memberRFamily_imageSet_of_irr hG hnoV hφ hφirr
    obtain ⟨jξ, kξ, hjξeq, hkξeq, hξeq⟩ :=
      hyp.sSet_memberRFamily_imageSet_of_red hG hnoV hξ hξirr
    rw [hφeq] at hα
    rw [hξeq, Finset.mem_image] at hβ
    obtain ⟨y, -, rfl⟩ := hβ
    rcases y with b | b <;> simp only [Sum.elim_inl, Sum.elim_inr]
    · rw [OddOrder.RepresentationTheory.inner_conj_symm, star_eq_zero]
      exact hyp.sSet_irr_memberRFamily_eta_inner hG hnoV hφ hφirr hrφ hsφ hα b jξ
    · rw [ClassFunction.inner_neg_right, OddOrder.RepresentationTheory.inner_conj_symm,
        hyp.sSet_irr_memberRFamily_eta_inner hG hnoV hφ hφirr hrφ hsφ hα b kξ,
        star_zero, neg_zero]
  · -- red × irr
    obtain ⟨jφ, kφ, hjφeq, hkφeq, hφeq⟩ :=
      hyp.sSet_memberRFamily_imageSet_of_red hG hnoV hφ hφirr
    obtain ⟨hrξ, hsξ, hξeq⟩ := hyp.sSet_memberRFamily_imageSet_of_irr hG hnoV hξ hξirr
    rw [hξeq] at hβ
    rw [hφeq, Finset.mem_image] at hα
    obtain ⟨x, -, rfl⟩ := hα
    rcases x with a | a <;> simp only [Sum.elim_inl, Sum.elim_inr]
    · exact hyp.sSet_irr_memberRFamily_eta_inner hG hnoV hξ hξirr hrξ hsξ hβ a jφ
    · rw [ClassFunction.inner_neg_left,
        hyp.sSet_irr_memberRFamily_eta_inner hG hnoV hξ hξirr hrξ hsξ hβ a kφ,
        neg_zero]
  · -- red × red
    obtain ⟨jφ, kφ, hjφeq, hkφeq, hφeq⟩ :=
      hyp.sSet_memberRFamily_imageSet_of_red hG hnoV hφ hφirr
    obtain ⟨jξ, kξ, hjξeq, hkξeq, hξeq⟩ :=
      hyp.sSet_memberRFamily_imageSet_of_red hG hnoV hξ hξirr
    rw [hφeq, Finset.mem_image] at hα
    rw [hξeq, Finset.mem_image] at hβ
    have hne1 : jφ ≠ jξ :=
      hyp.mu_colSum_ne_of_inner_zero (by rw [← hjφeq, ← hjξeq]; exact h1)
    have hne2 : jφ ≠ kξ :=
      hyp.mu_colSum_ne_of_inner_zero (by rw [← hjφeq, ← hkξeq]; exact h2)
    have hne3 : kφ ≠ jξ :=
      hyp.mu_colSum_ne_of_inner_zero (by rw [← hkφeq, ← hjξeq]; exact hbφξ)
    have hne4 : kφ ≠ kξ :=
      hyp.mu_colSum_ne_of_inner_zero (by rw [← hkφeq, ← hkξeq]; exact hbφξb)
    obtain ⟨x, -, rfl⟩ := hα
    obtain ⟨y, -, rfl⟩ := hβ
    rcases x with a | a <;> rcases y with b | b <;> simp only [Sum.elim_inl, Sum.elim_inr]
    · rw [OddOrder.Peterfalvi.S16.eta_orthonormal hyp a b jφ jξ, if_neg (fun h => hne1 h.2)]
    · rw [ClassFunction.inner_neg_right, OddOrder.Peterfalvi.S16.eta_orthonormal hyp a b jφ kξ,
        if_neg (fun h => hne2 h.2), neg_zero]
    · rw [ClassFunction.inner_neg_left, OddOrder.Peterfalvi.S16.eta_orthonormal hyp a b kφ jξ,
        if_neg (fun h => hne3 h.2), neg_zero]
    · rw [ClassFunction.inner_neg_left, ClassFunction.inner_neg_right,
        OddOrder.Peterfalvi.S16.eta_orthonormal hyp a b kφ kξ, if_neg (fun h => hne4 h.2),
        neg_zero, neg_zero]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Peterfalvi (5.5) for a coherent subfamily of `𝒮 = sSet`** (issue 1017; the honest-Dade
`S`-instance of the M-side `S13.SOf_coherent_extension_eq_sum_memberRFamily`): a coherent
extension of `T ⊆ 𝒮` w.r.t. the honest `'A(S)`-Dade `τ_S` evaluates a member `ψ` (whose
conjugate is also in `T`) as a partial sum over the dispatched case-agnostic `R`-family
`sSet_memberRFamily`. -/
theorem Hypothesis.sSet_coherent_extension_eq_sum_memberRFamily [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    {T : Set (ClassFunction ↥hyp.S ℂ)} (hTsub : T ⊆ sSet (hyp.toTypesIIIIIIVSetupS hG))
    (c' : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
        ((hyp.dadeHypS hG).fullDadeIsometryData)) T
      (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S))
    {ψ : ClassFunction ↥hyp.S ℂ} (hψT : ψ ∈ T) (hψcT : ψ.conj ∈ T) :
    ∃ E ⊆ (hyp.sSet_memberRFamily hG hnoV (hTsub hψT)).imageSet,
      c'.extension ψ = ∑ α ∈ E, α := by
  have := hyp.finiteG
  classical
  have hne : ψ ≠ ψ.conj := fun h =>
    sSet_hasNoRealCharacters (hyp.toTypesIIIIIIVSetupS hG) (hyp.oddCardS hG)
      (hTsub hψT) h.symm
  have hχχbar : ClassFunction.inner ψ ψ.conj = 0 :=
    sSet_pairwiseOrthogonal (hyp.toTypesIIIIIIVSetupS hG) (hTsub hψT) (hTsub hψcT) hne
  have hdiffsupp : ((ψ - ψ.conj : ClassFunction ↥hyp.S ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S := by
    rw [show (ψ - ψ.conj : ClassFunction ↥hyp.S ℂ) = -(ψ.conj - ψ) from by abel,
      ClassFunction.support_neg]
    exact hyp.sSet_member_conjDiff_supported hG (hTsub hψT)
  have hle : OddOrder.Peterfalvi.S07.zSpan (L := ↥hyp.S)
      ({ψ - ψ.conj, ψ - 0} : Set (ClassFunction ↥hyp.S ℂ))
      ≤ OddOrder.Peterfalvi.S07.zSpan (L := ↥hyp.S) T :=
    Submodule.span_le.mpr (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Submodule.sub_mem _ (Submodule.subset_span hψT) (Submodule.subset_span hψcT)
      · exact Submodule.sub_mem _ (Submodule.subset_span hψT) (Submodule.zero_mem _))
  obtain ⟨-, hτ1ψ, E, hEsub, hXsum, -⟩ :=
    OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.eq_sum_of_psi_eq_zero
      (OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.ofProjection
        (hyp.sSet_memberRFamily hG hnoV (hTsub hψT)) c'.extension
        (fun φ ζ hφ hζ => c'.extension_inner_eq φ ζ (hle hφ) (hle hζ))
        (c'.extends_on_supported (ψ - ψ.conj)
          ⟨Submodule.sub_mem _ (Submodule.subset_span hψT) (Submodule.subset_span hψcT),
            hdiffsupp⟩)
        (by rw [sub_zero]; exact c'.extension_mem_ZIrr ψ (Submodule.subset_span hψT))
        (by rw [ClassFunction.inner_zero_right])
        (by rw [ClassFunction.inner_zero_right])
        hχχbar)
  exact ⟨E, hEsub, hτ1ψ.trans hXsum⟩

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Cross-orthogonality of coherent images on the honest `'A(S)`-Dade** (Coq `coherent_ortho`,
`PFsection5.v:986`; issue 1017, the `S`-instance of the M-side
`S13.coherent_extension_cross_orthogonal`): for coherent subfamilies `T₁, T₂ ⊆ 𝒮 = sSet` and
members `ψ ∈ T₁`, `λ ∈ T₂` with `ψ ∉ {λ, λ̄}` (so `⟨ψ, λ⟩ = ⟨ψ, λ̄⟩ = 0` by the family's
pairwise orthogonality), the coherent images are orthogonal: both are partial `R`-family sums
by (5.5) (`sSet_coherent_extension_eq_sum_memberRFamily`), and the case-agnostic `R`-families
are cross-orthogonal by (5.2.e) (`sSet_memberRFamily_orthogonal`). -/
theorem Hypothesis.sSet_coherent_extension_cross_orthogonal [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    {T₁ T₂ : Set (ClassFunction ↥hyp.S ℂ)}
    (hT₁sub : T₁ ⊆ sSet (hyp.toTypesIIIIIIVSetupS hG))
    (hT₂sub : T₂ ⊆ sSet (hyp.toTypesIIIIIIVSetupS hG))
    (c₁ : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
        ((hyp.dadeHypS hG).fullDadeIsometryData)) T₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S))
    (c₂ : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
        ((hyp.dadeHypS hG).fullDadeIsometryData)) T₂
      (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S))
    {ψ lam : ClassFunction ↥hyp.S ℂ}
    (hψT : ψ ∈ T₁) (hψcT : ψ.conj ∈ T₁) (hlamT : lam ∈ T₂) (hlamcT : lam.conj ∈ T₂)
    (hne1 : ψ ≠ lam) (hne2 : ψ ≠ lam.conj) :
    ClassFunction.inner (c₁.extension ψ) (c₂.extension lam) = 0 := by
  have := hyp.finiteG
  classical
  have h1 : ClassFunction.inner ψ lam = 0 :=
    sSet_pairwiseOrthogonal (hyp.toTypesIIIIIIVSetupS hG) (hT₁sub hψT) (hT₂sub hlamT) hne1
  have h2 : ClassFunction.inner ψ lam.conj = 0 :=
    sSet_pairwiseOrthogonal (hyp.toTypesIIIIIIVSetupS hG) (hT₁sub hψT) (hT₂sub hlamcT) hne2
  obtain ⟨E₁, hE₁sub, hE₁⟩ :=
    hyp.sSet_coherent_extension_eq_sum_memberRFamily hG hnoV hT₁sub c₁ hψT hψcT
  obtain ⟨E₂, hE₂sub, hE₂⟩ :=
    hyp.sSet_coherent_extension_eq_sum_memberRFamily hG hnoV hT₂sub c₂ hlamT hlamcT
  have horth := hyp.sSet_memberRFamily_orthogonal hG hnoV (hT₁sub hψT) (hT₂sub hlamT) h1 h2
  rw [hE₁, hE₂, OddOrder.RepresentationTheory.inner_sum_left]
  refine Finset.sum_eq_zero fun α hα => ?_
  rw [OddOrder.RepresentationTheory.inner_sum_right]
  exact Finset.sum_eq_zero fun β hβ => horth α (hE₁sub hα) β (hE₂sub hβ)

end OddOrder.Peterfalvi.S15


