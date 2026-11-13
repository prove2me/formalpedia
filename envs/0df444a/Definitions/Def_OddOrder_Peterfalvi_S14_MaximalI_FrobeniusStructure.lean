-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_FrobeniusStructure
-- name    : OddOrder_Peterfalvi_S14_MaximalI_FrobeniusStructure
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T14:07:54.05514+00:00
-- url     : https://prove2.me/theorems/289fe570-28da-465d-883e-e371befb4425
-- title:
--   Peterfalvi (12.6)–(12.7): type I Frobenius structure
-- statement:
--   Formalizes the Frobenius structure of type I maximal subgroups in Peterfalvi (12.6)–(12.7), including degree-sum and degree-square bounds for the witness family when it is not coherent.
--
--   Main declarations: `Sset_breakPair_fields` (Break-pair fields for `{ψ, ψ̄}`); `Sset_degreeSumBound_of_not_coherent` (Peterfalvi (6.2) member-family degree-sum bound over the witness `τ`); `Sset_degreeSqReBound_of_not_coherent` (Peterfalvi (6.2) member-family degree-square bound); `Sset_sum_re_sq_induce_kernelFilter_eq` (Peterfalvi (6.2) B2 — the `S(A)` degree-square identity).
--
--   The bundle also proves 4 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S14_MaximalI/FrobeniusStructure.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S14_MaximalI/FrobeniusStructure.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_RhoConstancy
import Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_FrobeniusStructureBasic

namespace OddOrder.Peterfalvi.S14

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
open OddOrder.Peterfalvi.S09.Cert in
/-- **Break-pair fields for `{ψ, ψ̄}`** — the witness analogue of the Sibley `sBreakPair_fields`,
the per-`ψ` inputs the (5.6) bound `coherentDegreeSumBound_of_not_coherent` consumes (in its
argument order): non-realness, conjugate-difference support, the `{ψ, ψ̄}` orthonormality, and the
orthogonality of `ψ`, `ψ̄` to every member of `S₁` (distinct irreducibles, since `ψ, ψ̄ ∉ S₁`). -/
theorem Sset_breakPair_fields [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    (hodd : Odd (Nat.card ↥L)) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {ψ : ClassFunction ↥L ℂ} (hψS : ψ ∈ hyp.Sset)
    {S₁ : Set (ClassFunction ↥L ℂ)} (hS₁sub : S₁ ⊆ hyp.Sset)
    (hψnotS1 : ψ ∉ S₁) (hψcnotS1 : ψ.conj ∉ S₁) :
    ¬ ClassFunction.IsReal ψ ∧
    (ψ.conj - ψ).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L ∧
    ClassFunction.inner ψ ψ = 1 ∧
    ClassFunction.inner ψ.conj ψ.conj = 1 ∧
    ClassFunction.inner ψ ψ.conj = 0 ∧
    ClassFunction.inner ψ.conj ψ = 0 ∧
    (∀ x ∈ S₁, ClassFunction.inner ψ x = 0) ∧
    (∀ x ∈ S₁, ClassFunction.inner ψ.conj x = 0) := by
  have hψconjS := Sset_closedUnderConjugate hyp hψS
  have hne : ψ ≠ ψ.conj := fun h => (Sset_hasNoRealCharacters hyp hodd hfrob hψS) h.symm
  refine ⟨Sset_hasNoRealCharacters hyp hodd hfrob hψS,
    Sset_conjDiff_supported hyp hfrob hAH hψS,
    Sset_inner_self_eq_one hyp hfrob hψS,
    Sset_inner_self_eq_one hyp hfrob hψconjS,
    Sset_pairwiseOrthogonal hyp hodd hfrob hψS hψconjS hne,
    Sset_pairwiseOrthogonal hyp hodd hfrob hψconjS hψS (fun h => hne h.symm), ?_, ?_⟩
  · intro x hx
    have hxne : ψ ≠ x := by rintro rfl; exact hψnotS1 hx
    have hite := OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite
      ⟨ψ, Sset_isIrreducibleCharacter hyp hfrob hψS⟩
      ⟨x, Sset_isIrreducibleCharacter hyp hfrob (hS₁sub hx)⟩
    rwa [if_neg (fun he => hxne
      (congrArg (fun c : IrreducibleCharacter ↥L => (c : ClassFunction ↥L ℂ)) he))] at hite
  · intro x hx
    have hxne : ψ.conj ≠ x := by rintro rfl; exact hψcnotS1 hx
    have hite := OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite
      ⟨ψ.conj, Sset_isIrreducibleCharacter hyp hfrob hψconjS⟩
      ⟨x, Sset_isIrreducibleCharacter hyp hfrob (hS₁sub hx)⟩
    rwa [if_neg (fun he => hxne
      (congrArg (fun c : IrreducibleCharacter ↥L => (c : ClassFunction ↥L ℂ)) he))] at hite

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
open OddOrder.Peterfalvi.S09.Cert in
/-- **Peterfalvi (6.2) member-family degree-sum bound over the witness `τ`** — the witness analogue
of the Sibley `sMember_degreeSumBound_of_not_coherent`, feeding the (5.6) core
`coherentDegreeSumBound_of_not_coherent` (over `hyp.dadeData.dade`, the same Dade datum as
`hyp.tau`).  Assembled from the six witness member-family helpers + the abstract §7 generation
bridges.  If `S₁` (coherent, containing a degree-`|L:K|` anchor `χ₁`) breaks against `{ψ, ψ̄}`, then
`∑ⱼ degⱼ² ≤ 2a` where `χmemⱼ(1) = degⱼ·χ₁(1)`, `ψ(1) = a·χ₁(1)`. -/
theorem Sset_degreeSumBound_of_not_coherent [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    (hodd : Odd (Nat.card ↥L)) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {S₁ : Set (ClassFunction ↥L ℂ)} (hS₁sub : S₁ ⊆ hyp.Sset)
    (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁) (hS₁fin : S₁.Finite)
    (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau S₁ hyp.A)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁S₁ : χ₁ ∈ S₁)
    (hχ₁deg : χ₁ 1 = (((hyp.typeI.typeF.H).subgroupOf L).index : ℂ))
    {ψ : ClassFunction ↥L ℂ} (hψS : ψ ∈ hyp.Sset) (hψirr : IsIrreducibleCharacter ψ)
    (hψnotS1 : ψ ∉ S₁) (hψcnotS1 : ψ.conj ∉ S₁)
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (S₁ ∪ {ψ, ψ.conj}) hyp.A)) :
    ∃ (k : ℕ) (χmem : Fin k → IrreducibleCharacter ↥L) (deg : Fin k → ℕ) (a : ℕ),
      Function.Injective χmem ∧
      Set.range (fun j => (χmem j : ClassFunction ↥L ℂ)) = S₁ ∧
      (∀ j, (χmem j : ClassFunction ↥L ℂ) 1 = (deg j : ℂ) * χ₁ 1) ∧
      ψ 1 = (a : ℂ) * χ₁ 1 ∧
      ∑ j : Fin k, ((deg j : ℝ)) ^ 2 ≤ 2 * (a : ℝ) := by
  classical
  obtain ⟨k, χmem, hχinj, hrange, hmemreal, hmemdiffsupp, hmemS1, hmembarS1, hmemconjortho,
      hmemortho⟩ := Sset_exists_orthonormalFamily hyp hodd hfrob hAH hS₁sub hS₁conj hS₁fin
  have hχ₁range : χ₁ ∈ Set.range (fun j => (χmem j : ClassFunction ↥L ℂ)) := by
    rw [hrange]; exact hχ₁S₁
  obtain ⟨i₁, hi₁eq0⟩ := hχ₁range
  have hi₁eq : (χmem i₁ : ClassFunction ↥L ℂ) = χ₁ := hi₁eq0
  have hmemS : ∀ j, (χmem j : ClassFunction ↥L ℂ) ∈ hyp.Sset := fun j => hS₁sub (hmemS1 j)
  have hanchordeg : (χmem i₁ : ClassFunction ↥L ℂ) 1 =
      (((hyp.typeI.typeF.H).subgroupOf L).index : ℂ) := by rw [hi₁eq]; exact hχ₁deg
  obtain ⟨deg, hdeg_i₁, _hdeg_pos, hdeg_eq, hmemdegdiffsupp⟩ :=
    Sset_exists_degreeData hyp hfrob hAH hmemS hanchordeg
  obtain ⟨hrealψ, hdiffsuppψ, hψψ, hψbarψbar, hψψbar, hψbarψ, hψ_S1, hψbar_S1⟩ :=
    Sset_breakPair_fields hyp hodd hfrob hAH hψS hS₁sub hψnotS1 hψcnotS1
  obtain ⟨a, _ha_pos, hψratio0⟩ := Sset_charValue_one_eq_mul_index hyp hψS
  have hψratio : ψ 1 = (a : ℂ) * (χmem i₁ : ClassFunction ↥L ℂ) 1 := by rw [hψratio0, ← hanchordeg]
  have hdiffasuppψ : (ψ - a • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L :=
    Sset_scaledDiff_supported hyp hfrob hAH hψS (hmemS i₁) hψratio
  have htau1ψ : hyp.tau (ψ - a • (χmem i₁ : ClassFunction ↥L ℂ)) ∈ ZIrr G :=
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
      hyp.dadeData.dade hdiffasuppψ
      (Submodule.sub_mem _ (IrreducibleCharacter.mem_ZIrr ⟨ψ, hψirr⟩)
        (nsmul_mem (IrreducibleCharacter.mem_ZIrr (χmem i₁)) a))
  have hcover : ∀ x ∈ S₁, ∃ j, j ∈ (Finset.univ : Finset (Fin k)) ∧
      (χmem j : ClassFunction ↥L ℂ) = x := by
    intro x hx; rw [← hrange] at hx; obtain ⟨j, hj⟩ := hx; exact ⟨j, Finset.mem_univ j, hj⟩
  have hSgen := OddOrder.Peterfalvi.S07.span_subset_span_zSupportedSpan_union_anchor_of_scaledDiffs
    (s := (Finset.univ : Finset (Fin k))) (χmem := fun j => (χmem j : ClassFunction ↥L ℂ))
    (deg := deg) (i₁ := i₁) hcover (Finset.mem_univ i₁) (fun j _ => hmemS1 j)
    (fun j _ => hmemdegdiffsupp j)
  have hbar1 : ψ.conj 1 = ψ 1 := by
    rw [ClassFunction.conj_apply]
    obtain ⟨n, -, hn1, -⟩ := hψirr.exists_natDegree_charValue_one_dvd_card
    rw [hn1, star_natCast]
  have hchi1_ne : (χmem i₁ : ClassFunction ↥L ℂ) 1 ≠ 0 := by
    rw [hanchordeg]; exact Nat.cast_ne_zero.mpr Subgroup.index_ne_zero_of_finite
  have h1A : (1 : ↥L) ∉ OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L :=
    one_not_mem_supportInSubgroup_sharp hyp.typeI.typeF.H hAH
  have hgen := OddOrder.Peterfalvi.S07.zSupportedSpan_adjoinPair_subset_span_of_anchorGeneration
    (χ := ψ) (chibar := ψ.conj) (chi1 := (χmem i₁ : ClassFunction ↥L ℂ)) (a := a)
    hSgen hψratio hbar1 hchi1_ne h1A
  refine ⟨k, χmem, deg, a, hχinj, hrange, fun j => by rw [hdeg_eq j, hi₁eq],
    by rw [hψratio, hi₁eq], ?_⟩
  have hbound := OddOrder.Peterfalvi.S08.coherentDegreeSumBound_of_not_coherent
    hyp.dadeData.dade hS₁coh ⟨ψ, hψirr⟩ hrealψ hdiffsuppψ hψψ hψbarψbar hψψbar hψbarψ
    hψ_S1 hψbar_S1 (Finset.univ : Finset (Fin k)) χmem deg i₁ (Finset.mem_univ i₁)
    (fun j _ => hmemreal j) (fun j _ => hmemdiffsupp j) (fun j _ => hmemdegdiffsupp j)
    (fun j _ => hmemS1 j) (fun j _ => hmembarS1 j) (fun j _ => hmemconjortho j)
    (fun i _ j _ => by rw [hmemortho i j]; rcases eq_or_ne i j with h | h <;> simp [h])
    hdiffasuppψ htau1ψ hdeg_i₁ hSgen hgen hnc
  simpa using hbound

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (6.2) member-family degree-square bound** (real form, witness `τ`) — rescales
`Sset_degreeSumBound_of_not_coherent`'s `∑ⱼ degⱼ² ≤ 2a` by the anchor degree `χ₁(1)` into the
character-degree-square sum `∑ⱼ (χⱼ(1).re)² ≤ 2·ψ(1).re·χ₁(1).re`.  Mirror of the Sibley
`sMember_degreeSqReBound_of_not_coherent`. -/
theorem Sset_degreeSqReBound_of_not_coherent [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    (hodd : Odd (Nat.card ↥L)) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {S₁ : Set (ClassFunction ↥L ℂ)} (hS₁sub : S₁ ⊆ hyp.Sset)
    (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁) (hS₁fin : S₁.Finite)
    (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau S₁ hyp.A)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁S₁ : χ₁ ∈ S₁)
    (hχ₁deg : χ₁ 1 = (((hyp.typeI.typeF.H).subgroupOf L).index : ℂ))
    {ψ : ClassFunction ↥L ℂ} (hψS : ψ ∈ hyp.Sset) (hψirr : IsIrreducibleCharacter ψ)
    (hψnotS1 : ψ ∉ S₁) (hψcnotS1 : ψ.conj ∉ S₁)
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (S₁ ∪ {ψ, ψ.conj}) hyp.A)) :
    ∃ (k : ℕ) (χmem : Fin k → IrreducibleCharacter ↥L),
      Function.Injective χmem ∧
      Set.range (fun j => (χmem j : ClassFunction ↥L ℂ)) = S₁ ∧
      (∀ j, (χmem j : ClassFunction ↥L ℂ) ∈ S₁) ∧
      ∑ j : Fin k, (((χmem j : ClassFunction ↥L ℂ) 1).re) ^ 2 ≤ 2 * (ψ 1).re * (χ₁ 1).re := by
  obtain ⟨k, χmem, deg, a, hχinj, hrange, hdeg_eq, hψ_eq, hbound⟩ :=
    Sset_degreeSumBound_of_not_coherent hyp hodd hfrob hAH hS₁sub hS₁conj hS₁fin hS₁coh hχ₁S₁
      hχ₁deg hψS hψirr hψnotS1 hψcnotS1 hnc
  have hmemS1 : ∀ j, (χmem j : ClassFunction ↥L ℂ) ∈ S₁ := by
    intro j; rw [← hrange]; exact ⟨j, rfl⟩
  refine ⟨k, χmem, hχinj, hrange, hmemS1, ?_⟩
  have hdegre : ∀ j, ((χmem j : ClassFunction ↥L ℂ) 1).re = (deg j : ℝ) * (χ₁ 1).re := by
    intro j; rw [hdeg_eq j, Complex.mul_re, Complex.natCast_re, Complex.natCast_im]; ring
  have hψre : (ψ 1).re = (a : ℝ) * (χ₁ 1).re := by
    rw [hψ_eq, Complex.mul_re, Complex.natCast_re, Complex.natCast_im]; ring
  have hre_nonneg : (0 : ℝ) ≤ (χ₁ 1).re ^ 2 := sq_nonneg _
  calc ∑ j : Fin k, (((χmem j : ClassFunction ↥L ℂ) 1).re) ^ 2
      = ∑ j : Fin k, ((deg j : ℝ) * (χ₁ 1).re) ^ 2 := by
        refine Finset.sum_congr rfl (fun j _ => ?_); rw [hdegre j]
    _ = (χ₁ 1).re ^ 2 * ∑ j : Fin k, (deg j : ℝ) ^ 2 := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun j _ => ?_); ring
    _ ≤ (χ₁ 1).re ^ 2 * (2 * (a : ℝ)) := mul_le_mul_of_nonneg_left hbound hre_nonneg
    _ = 2 * ((a : ℝ) * (χ₁ 1).re) * (χ₁ 1).re := by ring
    _ = 2 * (ψ 1).re * (χ₁ 1).re := by rw [hψre]

/-- **The witness kernel `K = (L_F).subgroupOf L` is normal in `↥L`** —
`L_F = maxNilpotentNormalHall L` whose `subgroupOf L` is normal
(`maxNilpotentNormalHall_subgroupOf_normal`).  Needed by the (6.2) B2 degree-sum identity and the
(6.5) engine's `hHnorm`. -/
theorem typeF_H_subgroupOf_normal [Finite G] {L : Subgroup G} (hyp : Hypothesis L) :
    ((hyp.typeI.typeF.H).subgroupOf L).Normal := by
  rw [hyp.typeI.typeF.H_eq]
  exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal L

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
open scoped Classical in
/-- **Peterfalvi (6.2) B2 — the `S(A)` degree-square identity** (witness form).  Mirror of the
Sibley `sum_re_sq_induce_kernelFilter_eq`: over the witness kernel `K = (L_F).subgroupOf L`, the
filtered induced family `{Ind_K^L θ | A ⊆ Ker θ, θ ≠ 1}` has degree-square sum `|L:K|·(|K:A| − 1)`,
via the abstract B2 `sum_div_normSq_induce_kernelFilter_eq` and that each member is irreducible
(`‖·‖² = 1`, `χ(1)` a real natural). -/
theorem Sset_sum_re_sq_induce_kernelFilter_eq [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    {A : Subgroup ↥L} [A.Normal] :
    ∑ χ ∈ (Finset.univ.filter
        (fun θ : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) =>
          (↑(A.subgroupOf ((hyp.typeI.typeF.H).subgroupOf L)) :
              Set ↥((hyp.typeI.typeF.H).subgroupOf L)) ⊆
            OddOrder.Peterfalvi.S03.characterKernel
              (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ) ∧
            θ ≠ trivialIrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L))).image
        (fun θ => ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L) θ.toClassFunction),
        ((χ 1).re) ^ 2
      = (((hyp.typeI.typeF.H).subgroupOf L).index : ℝ) *
        ((Nat.card (↥((hyp.typeI.typeF.H).subgroupOf L) ⧸
          A.subgroupOf ((hyp.typeI.typeF.H).subgroupOf L)) : ℝ) - 1) := by
  have := hyp.finiteG
  have : ((hyp.typeI.typeF.H).subgroupOf L).Normal := typeF_H_subgroupOf_normal hyp
  have hB2 := OddOrder.Peterfalvi.S08.sum_div_normSq_induce_kernelFilter_eq (G := ↥L)
    (H := (hyp.typeI.typeF.H).subgroupOf L) (A := A)
  have hsummand : ∀ χ ∈ (Finset.univ.filter
      (fun θ : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) =>
        (↑(A.subgroupOf ((hyp.typeI.typeF.H).subgroupOf L)) :
            Set ↥((hyp.typeI.typeF.H).subgroupOf L)) ⊆
          OddOrder.Peterfalvi.S03.characterKernel
            (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ) ∧
          θ ≠ trivialIrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L))).image
      (fun θ => ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L) θ.toClassFunction),
      χ 1 ^ 2 / ClassFunction.inner χ χ = ((((χ 1).re) ^ 2 : ℝ) : ℂ) := by
    intro χ hχ
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hχ
    have hθne : θ ≠ trivialIrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) :=
      (Finset.mem_filter.mp hθ).2.2
    have hχS : ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L)
        (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ) ∈ hyp.Sset := by
      simp only [Hypothesis.Sset, Set.mem_ofPred_eq]; exact ⟨θ, hθne, rfl⟩
    have hirr := Sset_isIrreducibleCharacter hyp hfrob hχS
    have hinner : ClassFunction.inner
        (ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L)
          (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ))
        (ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L)
          (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ)) = 1 := by
      simpa using OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite
        (⟨_, hirr⟩ : IrreducibleCharacter ↥L) ⟨_, hirr⟩
    obtain ⟨n, -, hn1, -⟩ := hirr.exists_natDegree_charValue_one_dvd_card
    rw [hinner, div_one, hn1, Complex.natCast_re]; push_cast; ring
  have key : ((∑ χ ∈ (Finset.univ.filter
        (fun θ : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) =>
          (↑(A.subgroupOf ((hyp.typeI.typeF.H).subgroupOf L)) :
              Set ↥((hyp.typeI.typeF.H).subgroupOf L)) ⊆
            OddOrder.Peterfalvi.S03.characterKernel
              (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ) ∧
            θ ≠ trivialIrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L))).image
        (fun θ => ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L) θ.toClassFunction),
        ((χ 1).re) ^ 2 : ℝ) : ℂ)
      = (((((hyp.typeI.typeF.H).subgroupOf L).index : ℝ) *
        ((Nat.card (↥((hyp.typeI.typeF.H).subgroupOf L) ⧸
          A.subgroupOf ((hyp.typeI.typeF.H).subgroupOf L)) : ℝ) - 1)) : ℝ) := by
    rw [Complex.ofReal_sum, Finset.sum_congr rfl (fun χ hχ => (hsummand χ hχ).symm), hB2]
    push_cast; ring
  exact Complex.ofReal_inj.mp key

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
open scoped Classical in
/-- **Peterfalvi (6.2) per-step index bound** (witness form) — if `S(A) ⊆ S₁` (coherent, with a
degree-`|L:K|` anchor `χ₁`) breaks against `{ψ, ψ̄}`, then `|K:A| − 1 ≤ 2·ψ(1).re`.  The `S(A)`
degree-square sum `|L:K|·(|K:A|−1)` (B2, `Sset_sum_re_sq_induce_kernelFilter_eq`) is bounded by the
full enumerated `S₁`-family sum, which the (5.6) bound `Sset_degreeSqReBound_of_not_coherent` caps
by
`2·ψ(1).re·χ₁(1).re`; dividing by `χ₁(1).re = |L:K|`.  Mirror of `sMember_index_le_two_psi`. -/
theorem Sset_index_le_two_psi [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    (hodd : Odd (Nat.card ↥L)) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {A : Subgroup ↥L} [A.Normal]
    {S₁ : Set (ClassFunction ↥L ℂ)} (hS₁sub : S₁ ⊆ hyp.Sset)
    (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁) (hS₁fin : S₁.Finite)
    (hSA_S1 : hyp.SsubFiltration A ⊆ S₁)
    (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau S₁ hyp.A)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁S₁ : χ₁ ∈ S₁)
    (hχ₁deg : χ₁ 1 = (((hyp.typeI.typeF.H).subgroupOf L).index : ℂ))
    {ψ : ClassFunction ↥L ℂ} (hψS : ψ ∈ hyp.Sset) (hψirr : IsIrreducibleCharacter ψ)
    (hψnotS1 : ψ ∉ S₁) (hψcnotS1 : ψ.conj ∉ S₁)
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (S₁ ∪ {ψ, ψ.conj}) hyp.A)) :
    (Nat.card (↥((hyp.typeI.typeF.H).subgroupOf L) ⧸
      A.subgroupOf ((hyp.typeI.typeF.H).subgroupOf L)) : ℝ) - 1 ≤ 2 * (ψ 1).re := by
  obtain ⟨k, χmem, hχinj, hrange, hmemS1, hfambound⟩ :=
    Sset_degreeSqReBound_of_not_coherent hyp hodd hfrob hAH hS₁sub hS₁conj hS₁fin hS₁coh hχ₁S₁
      hχ₁deg hψS hψirr hψnotS1 hψcnotS1 hnc
  have hcfinj : Function.Injective (fun j => (χmem j : ClassFunction ↥L ℂ)) :=
    fun a b h => hχinj (Subtype.ext h)
  have hB2 := Sset_sum_re_sq_induce_kernelFilter_eq hyp hfrob (A := A)
  set SA := (Finset.univ.filter
      (fun θ : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) =>
        (↑(A.subgroupOf ((hyp.typeI.typeF.H).subgroupOf L)) :
            Set ↥((hyp.typeI.typeF.H).subgroupOf L)) ⊆
          OddOrder.Peterfalvi.S03.characterKernel
            (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ) ∧
          θ ≠ trivialIrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L))).image
      (fun θ => ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L) θ.toClassFunction)
    with hSAdef
  have hsub : SA ⊆ (Set.range (fun j => (χmem j : ClassFunction ↥L ℂ))).toFinset := by
    intro χ hχ
    rw [Set.mem_toFinset, hrange]
    rw [hSAdef] at hχ
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hχ
    obtain ⟨-, hker, hne⟩ := Finset.mem_filter.mp hθ
    apply hSA_S1
    simp only [Hypothesis.SsubFiltration, Set.mem_ofPred_eq]
    exact ⟨θ, hne, hker, rfl⟩
  have hchain : (((hyp.typeI.typeF.H).subgroupOf L).index : ℝ) *
      ((Nat.card (↥((hyp.typeI.typeF.H).subgroupOf L) ⧸
        A.subgroupOf ((hyp.typeI.typeF.H).subgroupOf L)) : ℝ) - 1) ≤
      2 * (ψ 1).re * (χ₁ 1).re := by
    rw [← hB2]
    calc ∑ χ ∈ SA, ((χ 1).re) ^ 2
        ≤ ∑ χ ∈ (Set.range (fun j => (χmem j : ClassFunction ↥L ℂ))).toFinset, ((χ 1).re) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
      _ = ∑ j : Fin k, (((χmem j : ClassFunction ↥L ℂ) 1).re) ^ 2 :=
          OddOrder.Peterfalvi.S08.sum_toFinset_range_eq hcfinj (fun χ => (χ 1).re ^ 2)
      _ ≤ 2 * (ψ 1).re * (χ₁ 1).re := hfambound
  have hχ₁re : (χ₁ 1).re = (((hyp.typeI.typeF.H).subgroupOf L).index : ℝ) := by
    rw [hχ₁deg, Complex.natCast_re]
  rw [hχ₁re] at hchain
  have hidx_pos : (0 : ℝ) < (((hyp.typeI.typeF.H).subgroupOf L).index : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have key : (((hyp.typeI.typeF.H).subgroupOf L).index : ℝ) *
      ((Nat.card (↥((hyp.typeI.typeF.H).subgroupOf L) ⧸
        A.subgroupOf ((hyp.typeI.typeF.H).subgroupOf L)) : ℝ) - 1) ≤
      (((hyp.typeI.typeF.H).subgroupOf L).index : ℝ) * (2 * (ψ 1).re) := by
    calc (((hyp.typeI.typeF.H).subgroupOf L).index : ℝ) *
          ((Nat.card (↥((hyp.typeI.typeF.H).subgroupOf L) ⧸
            A.subgroupOf ((hyp.typeI.typeF.H).subgroupOf L)) : ℝ) - 1)
        ≤ 2 * (ψ 1).re * (((hyp.typeI.typeF.H).subgroupOf L).index : ℝ) := hchain
      _ = (((hyp.typeI.typeF.H).subgroupOf L).index : ℝ) * (2 * (ψ 1).re) := by ring
  exact le_of_mul_le_mul_left key hidx_pos

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`Sset` is finite** — a subset of the (finite) range of `θ ↦ Ind_K^L θ`. -/
theorem Sset_finite [Finite G] {L : Subgroup G} (hyp : Hypothesis L) : hyp.Sset.Finite := by
  have := hyp.finiteG
  have := finite_irreducibleCharacter (G := ↥((hyp.typeI.typeF.H).subgroupOf L))
  have hsub : hyp.Sset ⊆ Set.range
      (fun θ : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) =>
        ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L) θ.toClassFunction) := by
    rintro χ ⟨θ, _, rfl⟩; exact ⟨θ, rfl⟩
  exact (Set.finite_range _).subset hsub

/-- **Every filtration level `S(A)` is finite** (subset of the finite `Sset`) — the finiteness input
of `exists_coherentBreakPair` (h56). -/
theorem SsubFiltration_finite [Finite G] {L : Subgroup G} (hyp : Hypothesis L) (A : Subgroup ↥L) :
    (hyp.SsubFiltration A).Finite :=
  (Sset_finite hyp).subset hyp.SsubFiltration_subset_Sset

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Every filtration level `S(A)` is closed under conjugation** (kernel preserved by
`characterKernel_conj`) — the conjugation-closure input of `exists_coherentBreakPair` (h56).
General `A` version of `SsubFiltration_commutator_closedUnderConjugate`. -/
theorem SsubFiltration_closedUnderConjugate [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    (A : Subgroup ↥L) : OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.SsubFiltration A) := by
  classical
  intro χ hχ
  simp only [Hypothesis.SsubFiltration, Set.mem_ofPred_eq] at hχ ⊢
  obtain ⟨θ, hθ_ne, hker, hφeq⟩ := hχ
  refine ⟨⟨(θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ).conj,
    θ.isIrreducible.conj⟩, ?_, ?_, ?_⟩
  · intro h
    apply hθ_ne
    have hcoe : (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ).conj
        = trivialClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) := by
      simpa using congrArg
        (fun c : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) =>
          (c : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ)) h
    apply Subtype.ext
    change (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ)
      = trivialClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L)
    rw [← ClassFunction.conj_conj
      (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ), hcoe]
    exact trivialClassFunction_isReal
  · rw [show ((⟨(θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ).conj,
          θ.isIrreducible.conj⟩ : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L)) :
          ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ)
        = (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ).conj from rfl,
      OddOrder.Peterfalvi.S03.characterKernel_conj]
    exact hker
  · rw [hφeq]
    simpa using ClassFunction.induce_conj ((hyp.typeI.typeF.H).subgroupOf L)
      (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Every filtration level `S(A)` has no real characters** — the no-real input of
`exists_coherentBreakPair` (h56).  Each `S(A)` member is a non-real `Sset` member. -/
theorem SsubFiltration_hasNoRealCharacters [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    (hodd : Odd (Nat.card ↥L)) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (A : Subgroup ↥L) :
    OddOrder.Peterfalvi.S03.HasNoRealCharacters (hyp.SsubFiltration A) := by
  intro χ hχ
  exact Sset_hasNoRealCharacters hyp hodd hfrob (hyp.SsubFiltration_subset_Sset hχ)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`S(A)` contains a member of degree `|L:K|`** (the anchor `χ₁` of the (6.2) index bound).  When
`K/(A.subgroupOf K)` is not perfect, it has a nontrivial degree-`1` character trivial on `A`
(`exists_irreducibleCharacter_ne_trivial_subset_kernel_of_commutator_ne_top`); its induction
`Ind_K^L θ ∈ S(A)` has degree `|L:K|·1 = |L:K|` (`induce_apply_one`). -/
theorem exists_mem_SsubFiltration_degree_index [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    {A : Subgroup ↥L} [A.Normal]
    (h : commutator (↥((hyp.typeI.typeF.H).subgroupOf L) ⧸
      A.subgroupOf ((hyp.typeI.typeF.H).subgroupOf L)) ≠ ⊤) :
    ∃ φ, φ ∈ hyp.SsubFiltration A ∧
      φ 1 = (((hyp.typeI.typeF.H).subgroupOf L).index : ℂ) := by
  have := hyp.finiteG
  have : (A.subgroupOf ((hyp.typeI.typeF.H).subgroupOf L)).Normal := (‹A.Normal›).subgroupOf _
  obtain ⟨θ, hθne, hθker, hθdeg⟩ :=
   OddOrder.Peterfalvi.S08.exists_irreducibleCharacter_ne_trivial_subset_kernel_of_commutator_ne_top
      (A.subgroupOf ((hyp.typeI.typeF.H).subgroupOf L)) h
  refine ⟨ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L) θ.toClassFunction, ?_, ?_⟩
  · simp only [Hypothesis.SsubFiltration, Set.mem_ofPred_eq]; exact ⟨θ, hθne, hθker, rfl⟩
  · rw [ClassFunction.induce_apply_one, hθdeg, mul_one]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (6.2) index bound = h56** (witness form, `∃θ`) — the (5.6) break-member oracle the
(6.5) engine `nonempty_coherent_SOf_bot_of_index_dvd` consumes.  If `S(A) ⊆ S(B)` (`A`-filtration
inside `B`-filtration), `K/(A.subgroupOf K)` not perfect (`hAcomm`), `S(A)` coherent and `S(B)` not,
then a break member `ψ = Ind_K^L θ ∈ S(B)` (`B ⊆ Ker θ`) satisfies `|K:A| − 1 ≤ 2·ψ(1).re`.
Combines
`exists_coherentBreakPair`, the degree-`|L:K|` anchor (`exists_mem_SsubFiltration_degree_index`),
and
`Sset_index_le_two_psi`.  Mirror of the Sibley `six_two_index_bound`. -/
theorem Sset_six_two_index_bound [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    (hodd : Odd (Nat.card ↥L)) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {A B : Subgroup ↥L} [A.Normal]
    (hAB : hyp.SsubFiltration A ⊆ hyp.SsubFiltration B)
    (hAcomm : commutator (↥((hyp.typeI.typeF.H).subgroupOf L) ⧸
      A.subgroupOf ((hyp.typeI.typeF.H).subgroupOf L)) ≠ ⊤)
    (hSAcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration A) hyp.A))
    (hSBncoh :
      ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration B) hyp.A)) :
    ∃ θ : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L),
      (↑(B.subgroupOf ((hyp.typeI.typeF.H).subgroupOf L)) :
          Set ↥((hyp.typeI.typeF.H).subgroupOf L)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel
          (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ) ∧
      (Nat.card (↥((hyp.typeI.typeF.H).subgroupOf L) ⧸
        A.subgroupOf ((hyp.typeI.typeF.H).subgroupOf L)) : ℝ) - 1 ≤
        2 * (ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L)
          (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ) 1).re := by
  obtain ⟨S₁, ψ, hS₁conj, hAS₁, hS₁B, hψB, hψnotS1, hψcnotS1, hS₁coh, hncoh⟩ :=
    OddOrder.Peterfalvi.S08.exists_coherentBreakPair hyp.tau hAB (SsubFiltration_finite hyp B)
      (SsubFiltration_closedUnderConjugate hyp B)
      (SsubFiltration_hasNoRealCharacters hyp hodd hfrob B)
      (fun φ hφ => Sset_isIrreducibleCharacter hyp hfrob (hyp.SsubFiltration_subset_Sset hφ))
      (SsubFiltration_closedUnderConjugate hyp A) hSAcoh hSBncoh
  obtain ⟨χ₁, hχ₁SA, hχ₁deg⟩ := exists_mem_SsubFiltration_degree_index hyp hAcomm
  have hψS : ψ ∈ hyp.Sset := hyp.SsubFiltration_subset_Sset hψB
  have hbound := Sset_index_le_two_psi hyp hodd hfrob hAH
    (hS₁B.trans hyp.SsubFiltration_subset_Sset) hS₁conj ((SsubFiltration_finite hyp B).subset hS₁B)
    hAS₁ hS₁coh.some (hAS₁ hχ₁SA) hχ₁deg hψS (Sset_isIrreducibleCharacter hyp hfrob hψS)
    hψnotS1 hψcnotS1 hncoh
  simp only [Hypothesis.SsubFiltration, Set.mem_ofPred_eq] at hψB
  obtain ⟨θ, hθne, hθker, hψeq⟩ := hψB
  refine ⟨θ, hθker, ?_⟩
  rw [hψeq] at hbound
  exact hbound

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
open OddOrder.Peterfalvi.S09.Cert in
/-- **`S(H′)` member differences are `A(L)`-supported** — the `hab`-free subfamily analogue of
`Sset_diff_supported` for the (6.5.c) `hcoh`.  Members of `S(⁅K,K⁆)` vanish off `H` (as `Sset`
members, `Sset_vanishes_off_H`) and share the constant degree `|L:K|` at `1`
(`SsubFiltration_commutator_apply_one_eq_index`, replacing the case-(b) `Sset_apply_one_eq_index`
that needs `H` abelian), so their difference is supported on `H^# = A(L)`. -/
theorem SsubFiltration_commutator_diff_supported [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {a b : ClassFunction ↥L ℂ}
    (ha : a ∈ hyp.SsubFiltration
      ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆)
    (hb : b ∈ hyp.SsubFiltration
      ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆) :
    (a - b).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L := by
  intro x hx
  have hx0 : (a - b) x ≠ 0 := ClassFunction.mem_support.mp hx
  rw [ClassFunction.sub_apply] at hx0
  have haS : a ∈ hyp.Sset := hyp.SsubFiltration_subset_Sset ha
  have hbS : b ∈ hyp.Sset := hyp.SsubFiltration_subset_Sset hb
  have hxH : (x : G) ∈ hyp.H := by
    by_contra h
    exact hx0 (by rw [Sset_vanishes_off_H hyp haS h, Sset_vanishes_off_H hyp hbS h, sub_zero])
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hx0 (by
      rw [SsubFiltration_commutator_apply_one_eq_index hyp ha,
          SsubFiltration_commutator_apply_one_eq_index hyp hb, sub_self])
  exact (mem_supportInSubgroup_sharp_subgroupOf_iff hyp.typeI.typeF.H hAH x).mpr
    ⟨Subgroup.mem_subgroupOf.mpr hxH, hx1⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The witness Dade map is a difference-isometry on `S(H′)`** (`hab`-free), mirroring
`Sset_tau_isometry_diff` via `SsubFiltration_commutator_diff_supported`. Standalone
member-difference
fact; the `S07.Hypothesis` field is discharged in its (0099) `zSupportedSpan` form via
`dadeIntegralCharacterMap_inner_eq_of_supported`. -/
theorem SsubFiltration_commutator_tau_isometry_diff [Finite G] {L : Subgroup G}
    (hyp : Hypothesis L) (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {a b c d : ClassFunction ↥L ℂ}
    (ha : a ∈ hyp.SsubFiltration
      ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆)
    (hb : b ∈ hyp.SsubFiltration
      ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆)
    (hc : c ∈ hyp.SsubFiltration
      ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆)
    (hd : d ∈ hyp.SsubFiltration
      ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆) :
    ClassFunction.inner (hyp.tau (a - b)) (hyp.tau (c - d))
      = ClassFunction.inner (a - b) (c - d) := by
  have hS : ∀ s ∈ ({a - b, c - d} : Set (ClassFunction ↥L ℂ)),
      s.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact SsubFiltration_commutator_diff_supported hyp hAH ha hb
    · exact SsubFiltration_commutator_diff_supported hyp hAH hc hd
  exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
    hyp.dadeData.dade hS (Submodule.subset_span (Set.mem_insert _ _))
    (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The witness Dade map is a difference-isometry on `S`** (issue 9001).  For members
`a, b, c, d ∈ S`, both differences are `A(L)`-supported (`Sset_diff_supported`), so the genuine §10
Dade isometry preserves their inner product (`dadeIntegralCharacterMap_inner_eq_on_supported_span`).
No global isometry is used.  Standalone member-difference fact; the `S07.Hypothesis` field is
discharged in its (0099) `zSupportedSpan` form via
`dadeIntegralCharacterMap_inner_eq_of_supported`. -/
theorem Sset_tau_isometry_diff [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    (hab : IsMulCommutative ↥hyp.typeI.typeF.H)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {a b c d : ClassFunction ↥L ℂ} (ha : a ∈ hyp.Sset) (hb : b ∈ hyp.Sset)
    (hc : c ∈ hyp.Sset) (hd : d ∈ hyp.Sset) :
    ClassFunction.inner (hyp.tau (a - b)) (hyp.tau (c - d))
      = ClassFunction.inner (a - b) (c - d) := by
  have hS : ∀ s ∈ ({a - b, c - d} : Set (ClassFunction ↥L ℂ)),
      s.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact Sset_diff_supported hyp hab hAH ha hb
    · exact Sset_diff_supported hyp hab hAH hc hd
  exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
    hyp.dadeData.dade hS (Submodule.subset_span (Set.mem_insert _ _))
    (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Witness member differences map into `ℤ[Irr G]`** — the `hZIrr` input of
`coherent_of_constant_degree`.  Each member is irreducible (`Sset_isIrreducibleCharacter`), so
`a − b ∈ ℤ[Irr L]`, and it is `A(L)`-supported (`Sset_diff_supported`), so the Dade image is a
virtual character of `G` (`dadeIntegralCharacterMap_mem_ZIrr_of_supported`). -/
theorem Sset_tau_diff_mem_ZIrr [Finite G] {L : Subgroup G} (hyp : Hypothesis L) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (hab : IsMulCommutative ↥hyp.typeI.typeF.H)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {a b : ClassFunction ↥L ℂ} (ha : a ∈ hyp.Sset) (hb : b ∈ hyp.Sset) :
    hyp.tau (a - b) ∈ ZIrr G := by
  refine OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
    hyp.dadeData.dade (Sset_diff_supported hyp hab hAH ha hb) ?_
  exact Submodule.sub_mem _
    (IrreducibleCharacter.mem_ZIrr ⟨a, Sset_isIrreducibleCharacter hyp hfrob ha⟩)
    (IrreducibleCharacter.mem_ZIrr ⟨b, Sset_isIrreducibleCharacter hyp hfrob hb⟩)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (5.2.d) difference image for a witness member** — the `difference_image` field of
the `S07.Hypothesis`.  Each `χ ∈ S` is a non-real irreducible (`Sset_isIrreducibleCharacter`,
`Sset_hasNoRealCharacters`) whose conjugate-difference `χ̄ − χ` is `A(L)`-supported
(`Sset_diff_supported`), so the genuine Dade map sends `χ − χ̄` to a signed difference of two
irreducibles of `G` (`dadeCharacterDifferenceImageOfDiff`). -/
noncomputable def Sset_differenceImage [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    (hodd : Odd (Nat.card ↥L)) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (hab : IsMulCommutative ↥hyp.typeI.typeF.H)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Sset) :
    OddOrder.Peterfalvi.S07.CharacterDifferenceImage hyp.tau χ :=
  OddOrder.Peterfalvi.S07.dadeCharacterDifferenceImageOfDiff hyp.dadeData.dade
    ⟨χ, Sset_isIrreducibleCharacter hyp hfrob hχ⟩
    (Sset_hasNoRealCharacters hyp hodd hfrob hχ)
    (Sset_diff_supported hyp hab hAH (Sset_closedUnderConjugate hyp hχ) hχ)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (5.2.e) orthogonality of witness difference images** — the
`difference_images_orthogonal` field.  For members `φ, χ ∈ S` with `⟨φ,χ⟩ = ⟨φ,χ̄⟩ = 0`, the signed
Dade images `(φ−φ̄)^τ`, `(χ−χ̄)^τ` are orthogonal: the conjugate-differences are `A(L)`-supported,
so
the Dade isometry (`Sset_tau_isometry_diff`) reduces the pairing to the source
`⟨φ−φ̄, χ−χ̄⟩`, which expands to the four cross terms — all zero by orthogonality and irreducibility
(`Sset_pairwiseOrthogonal`, `Sset_inner_self_eq_one`). -/
theorem Sset_differenceImages_orthogonal [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    (hodd : Odd (Nat.card ↥L)) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (hab : IsMulCommutative ↥hyp.typeI.typeF.H)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {φ χ : ClassFunction ↥L ℂ} (hφ : φ ∈ hyp.Sset) (hχ : χ ∈ hyp.Sset)
    (h1 : ClassFunction.inner φ χ = 0) (h2 : ClassFunction.inner φ χ.conj = 0) :
    (Sset_differenceImage hyp hodd hfrob hab hAH hφ).Orthogonal
      (Sset_differenceImage hyp hodd hfrob hab hAH hχ) := by
  have hφc := Sset_closedUnderConjugate hyp hφ
  have hχc := Sset_closedUnderConjugate hyp hχ
  refine
    OddOrder.Peterfalvi.S07.CharacterDifferenceImage.orthogonal_of_signedDifference_inner_eq_zero
    _ _ ?_
  rw [← (Sset_differenceImage hyp hodd hfrob hab hAH hφ).image_conjugateDifference,
      ← (Sset_differenceImage hyp hodd hfrob hab hAH hχ).image_conjugateDifference]
  change ClassFunction.inner (hyp.tau (φ - φ.conj)) (hyp.tau (χ - χ.conj)) = 0
  rw [Sset_tau_isometry_diff hyp hab hAH hφ hφc hχ hχc]
  have hne1 : φ.conj ≠ χ := by
    intro heq
    have hcc : χ.conj = φ := by rw [← heq, ClassFunction.conj_conj]
    rw [hcc, Sset_inner_self_eq_one hyp hfrob hφ] at h2
    exact one_ne_zero h2
  have hne2 : φ.conj ≠ χ.conj := by
    intro heq
    have hpc : φ = χ := by
      have h := congrArg ClassFunction.conj heq
      rwa [ClassFunction.conj_conj, ClassFunction.conj_conj] at h
    rw [hpc, Sset_inner_self_eq_one hyp hfrob hχ] at h1
    exact one_ne_zero h1
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right, ClassFunction.inner_sub_right,
    h1, h2, Sset_pairwiseOrthogonal hyp hodd hfrob hφc hχ hne1,
    Sset_pairwiseOrthogonal hyp hodd hfrob hφc hχc hne2]
  ring

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`S(H′)` is closed under conjugation** — the `conjugate_closed` field for the subfamily
`S07.Hypothesis`.  Mirrors `Sset_closedUnderConjugate` (`χ.conj = Ind_K^L θ̄`, `θ̄ ≠ 1`), with the
extra `S(H′)`-kernel condition preserved because `Ker θ̄ = Ker θ` (`characterKernel_conj`). -/
theorem SsubFiltration_commutator_closedUnderConjugate [Finite G] {L : Subgroup G}
    (hyp : Hypothesis L) {χ : ClassFunction ↥L ℂ}
    (hχ : χ ∈ hyp.SsubFiltration
      ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆) :
    χ.conj ∈ hyp.SsubFiltration
      ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆ := by
  classical
  simp only [Hypothesis.SsubFiltration, Set.mem_ofPred_eq] at hχ ⊢
  obtain ⟨θ, hθ_ne, hker, hφeq⟩ := hχ
  refine ⟨⟨(θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ).conj,
    θ.isIrreducible.conj⟩, ?_, ?_, ?_⟩
  · intro h
    apply hθ_ne
    have hcoe : (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ).conj
        = trivialClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) := by
      simpa using congrArg
        (fun c : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) =>
          (c : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ)) h
    apply Subtype.ext
    change (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ)
      = trivialClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L)
    rw [← ClassFunction.conj_conj
      (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ), hcoe]
    exact trivialClassFunction_isReal
  · rw [show ((⟨(θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ).conj,
          θ.isIrreducible.conj⟩ : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L)) :
          ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ)
        = (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ).conj from rfl,
      OddOrder.Peterfalvi.S03.characterKernel_conj]
    exact hker
  · rw [hφeq]
    simpa using ClassFunction.induce_conj ((hyp.typeI.typeF.H).subgroupOf L)
      (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`S(H′)` member differences map into `ℤ[Irr G]`** — the `hZIrr` input for the subfamily
`coherent_of_constant_degree`.  `hab`-free mirror of `Sset_tau_diff_mem_ZIrr` via
`SsubFiltration_commutator_diff_supported`; irreducibility is inherited from `Sset`. -/
theorem SsubFiltration_commutator_tau_diff_mem_ZIrr [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {a b : ClassFunction ↥L ℂ}
    (ha : a ∈ hyp.SsubFiltration
      ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆)
    (hb : b ∈ hyp.SsubFiltration
      ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆) :
    hyp.tau (a - b) ∈ ZIrr G := by
  refine OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
    hyp.dadeData.dade (SsubFiltration_commutator_diff_supported hyp hAH ha hb) ?_
  exact Submodule.sub_mem _
    (IrreducibleCharacter.mem_ZIrr
      ⟨a, Sset_isIrreducibleCharacter hyp hfrob (hyp.SsubFiltration_subset_Sset ha)⟩)
    (IrreducibleCharacter.mem_ZIrr
      ⟨b, Sset_isIrreducibleCharacter hyp hfrob (hyp.SsubFiltration_subset_Sset hb)⟩)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(5.2.d) difference image for an `S(H′)` member** — the `difference_image` field, `hab`-free
mirror of `Sset_differenceImage` via `SsubFiltration_commutator_diff_supported` and the subfamily
conjugation-closure. -/
noncomputable def SsubFiltration_commutator_differenceImage [Finite G] {L : Subgroup G}
    (hyp : Hypothesis L) (hodd : Odd (Nat.card ↥L)) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {χ : ClassFunction ↥L ℂ}
    (hχ : χ ∈ hyp.SsubFiltration
      ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆) :
    OddOrder.Peterfalvi.S07.CharacterDifferenceImage hyp.tau χ :=
  OddOrder.Peterfalvi.S07.dadeCharacterDifferenceImageOfDiff hyp.dadeData.dade
    ⟨χ, Sset_isIrreducibleCharacter hyp hfrob (hyp.SsubFiltration_subset_Sset hχ)⟩
    (Sset_hasNoRealCharacters hyp hodd hfrob (hyp.SsubFiltration_subset_Sset hχ))
    (SsubFiltration_commutator_diff_supported hyp hAH
      (SsubFiltration_commutator_closedUnderConjugate hyp hχ) hχ)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(5.2.e) orthogonality of `S(H′)` difference images** — the `difference_images_orthogonal`
field, `hab`-free mirror of `Sset_differenceImages_orthogonal`. -/
theorem SsubFiltration_commutator_differenceImages_orthogonal [Finite G] {L : Subgroup G}
    (hyp : Hypothesis L) (hodd : Odd (Nat.card ↥L)) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {φ χ : ClassFunction ↥L ℂ}
    (hφ : φ ∈ hyp.SsubFiltration
      ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆)
    (hχ : χ ∈ hyp.SsubFiltration
      ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆)
    (h1 : ClassFunction.inner φ χ = 0) (h2 : ClassFunction.inner φ χ.conj = 0) :
    (SsubFiltration_commutator_differenceImage hyp hodd hfrob hAH hφ).Orthogonal
      (SsubFiltration_commutator_differenceImage hyp hodd hfrob hAH hχ) := by
  have hφc := SsubFiltration_commutator_closedUnderConjugate hyp hφ
  have hχc := SsubFiltration_commutator_closedUnderConjugate hyp hχ
  have hφS := hyp.SsubFiltration_subset_Sset hφ
  have hχS := hyp.SsubFiltration_subset_Sset hχ
  have hφcS := hyp.SsubFiltration_subset_Sset hφc
  have hχcS := hyp.SsubFiltration_subset_Sset hχc
  refine
    OddOrder.Peterfalvi.S07.CharacterDifferenceImage.orthogonal_of_signedDifference_inner_eq_zero
    _ _ ?_
  rw [← (SsubFiltration_commutator_differenceImage hyp hodd hfrob hAH hφ).image_conjugateDifference,
      ← (SsubFiltration_commutator_differenceImage hyp hodd hfrob hAH hχ).image_conjugateDifference]
  change ClassFunction.inner (hyp.tau (φ - φ.conj)) (hyp.tau (χ - χ.conj)) = 0
  rw [SsubFiltration_commutator_tau_isometry_diff hyp hAH hφ hφc hχ hχc]
  have hne1 : φ.conj ≠ χ := by
    intro heq
    have hcc : χ.conj = φ := by rw [← heq, ClassFunction.conj_conj]
    rw [hcc, Sset_inner_self_eq_one hyp hfrob hφS] at h2
    exact one_ne_zero h2
  have hne2 : φ.conj ≠ χ.conj := by
    intro heq
    have hpc : φ = χ := by
      have h := congrArg ClassFunction.conj heq
      rwa [ClassFunction.conj_conj, ClassFunction.conj_conj] at h
    rw [hpc, Sset_inner_self_eq_one hyp hfrob hχS] at h1
    exact one_ne_zero h1
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right, ClassFunction.inner_sub_right,
    h1, h2, Sset_pairwiseOrthogonal hyp hodd hfrob hφcS hχS hne1,
    Sset_pairwiseOrthogonal hyp hodd hfrob hφcS hχcS hne2]
  ring

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.6) case (b): abelian rank-2 kernel → equal-degree coherence (5.7).**
When `H = L_F` is abelian (Def (8.3) case (b)), every `θ ∈ Irr H` is linear, so every member
`Ind_H^L θ ∈ S` has the same degree `[L:H]`; `S` is then coherent by (5.7).  The witness
`S07.Hypothesis hyp.Sset hyp.A` is assembled from the ten witness lemmas above (all seven §5.2
fields
plus the `coherent_of_constant_degree` inputs), and the coherence is produced by the now
lattice-relative `coherent_of_constant_degree` (issue 9001, no global isometry needed).
Nonemptiness of `S` (`hcard`) comes from the nontrivial abelian kernel `H` having a nontrivial
irreducible `θ`, whose induced pair `{Ind θ, Ind θ̄}` is two distinct non-real members. -/
theorem frobenius_typeI_coherent_of_abelianKernel [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G}
    (hyp : Hypothesis L)
    (hfrob' : ∃ C : Subgroup ↥L,
      OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L (hyp.H.subgroupOf L) C)
    (hab' : IsMulCommutative ↥hyp.typeI.typeF.H ∧ rank ↥hyp.typeI.typeF.H = 2) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A) := by
  classical
  obtain ⟨C, hfrob⟩ := hfrob'
  have hab := hab'.1
  have hodd : Odd (Nat.card ↥L) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card L)
  have hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1} :=
    hyp.typeIA_eq_sharp_of_frobenius hfrob
  -- `S` is finite: a subset of the (finite) range of `θ ↦ Ind_H^L θ`.
  have hSfin : hyp.Sset.Finite := by
    have := finite_irreducibleCharacter (G := ↥((hyp.typeI.typeF.H).subgroupOf L))
    have hsub : hyp.Sset ⊆ Set.range
        (fun θ : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) =>
          ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L) θ.toClassFunction) := by
      rintro χ ⟨θ, _, rfl⟩
      refine ⟨θ, ?_⟩
      rfl
    exact (Set.finite_range _).subset hsub
  -- the abelian kernel is nontrivial, so it has a nontrivial irreducible `θ`.
  have hHsub_ne : ((hyp.typeI.typeF.H).subgroupOf L) ≠ ⊥ := by
    rw [Ne, Subgroup.subgroupOf_eq_bot]
    intro hdisj
    have h := disjoint_iff.mp hdisj
    rw [inf_of_le_left hyp.typeI.typeF.H_le] at h
    exact hyp.typeI.typeF.H_nontrivial h
  have : Nontrivial ↥((hyp.typeI.typeF.H).subgroupOf L) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hHsub_ne
  obtain ⟨g, hg⟩ := exists_ne (1 : ↥((hyp.typeI.typeF.H).subgroupOf L))
  have : Nontrivial (ConjClasses ↥((hyp.typeI.typeF.H).subgroupOf L)) :=
    ⟨ConjClasses.mk g, ConjClasses.mk 1,
      fun h => hg (isConj_one_left.mp (ConjClasses.mk_eq_mk_iff_isConj.mp h))⟩
  have := finite_irreducibleCharacter (G := ↥((hyp.typeI.typeF.H).subgroupOf L))
  have : Nontrivial (IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L)) :=
    Finite.one_lt_card_iff_nontrivial.mp
      (by rw [card_irreducibleCharacter_eq];
          exact Finite.one_lt_card_iff_nontrivial.mpr inferInstance)
  obtain ⟨θ, hθ⟩ := exists_ne (trivialIrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L))
  set χ0 := ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L) θ.toClassFunction with hχ0
  have hχ0S : χ0 ∈ hyp.Sset := by
    simp only [hχ0, Hypothesis.Sset, Set.mem_ofPred_eq]
    refine ⟨θ, hθ, ?_⟩
    rfl
  have hχ0cS : χ0.conj ∈ hyp.Sset := Sset_closedUnderConjugate hyp hχ0S
  have hne : χ0 ≠ χ0.conj := fun h => (Sset_hasNoRealCharacters hyp hodd hfrob hχ0S) h.symm
  have hcard : 2 ≤ hyp.Sset.ncard := by
    calc 2 = ({χ0, χ0.conj} : Set (ClassFunction ↥L ℂ)).ncard := (Set.ncard_pair hne).symm
      _ ≤ hyp.Sset.ncard :=
          Set.ncard_le_ncard (by rintro x (rfl | rfl); exacts [hχ0S, hχ0cS]) hSfin
  -- assemble the §5.2 hypothesis and invoke the equal-degree coherence producer.
  refine OddOrder.Peterfalvi.S07.coherent_of_constant_degree
    { tau := hyp.tau
      tau_isometry_diff := fun _ _ hφ hψ =>
        OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported
          hyp.dadeData.dade hφ.2 hψ.2
      conjugate_closed := Sset_closedUnderConjugate hyp
      no_real_characters := Sset_hasNoRealCharacters hyp hodd hfrob
      pairwise_orthogonal := Sset_pairwiseOrthogonal hyp hodd hfrob
      difference_image := fun _ hχ => Sset_differenceImage hyp hodd hfrob hab hAH hχ
      difference_images_orthogonal := fun _ _ hφ hχ h1 h2 =>
        Sset_differenceImages_orthogonal hyp hodd hfrob hab hAH hφ hχ h1 h2 }
    hSfin hcard ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun ζ hζ => Sset_inner_self_eq_one hyp hfrob hζ
  · exact fun a ha b hb => Sset_tau_diff_mem_ZIrr hyp hfrob hab hAH ha hb
  · exact fun a ha b hb => by
      rw [Sset_apply_one_eq_index hyp hab ha, Sset_apply_one_eq_index hyp hab hb]
  · exact fun a ha => by
      rw [Sset_apply_one_eq_index hyp hab ha]
      exact Nat.cast_ne_zero.mpr Subgroup.index_ne_zero_of_finite
  · exact OddOrder.Peterfalvi.S09.Cert.one_not_mem_supportInSubgroup_sharp hyp.typeI.typeF.H hAH
  · exact fun a ha b hb => Sset_diff_supported hyp hab hAH ha hb

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
open OddOrder.RepresentationTheory in
/-- **`S(H′)` is coherent** — the `hcoh` input of the (6.5.c) engine
`nonempty_coherent_SOf_bot_of_index_dvd`.  `S(⁅K,K⁆)` (`K = (L_F).subgroupOf L`) is a
constant-degree family of degree `|L:K|` (`SsubFiltration_commutator_apply_one_eq_index`), coherent
by (5.7).  All seven §5.2 fields hold `hab`-free (the subfamily lemmas above); `2 ≤ |S(H′)|` because
the nontrivial abelianization `K/⁅K,K⁆` (`K` nilpotent nontrivial) has a nontrivial character whose
inflation `θ0` gives a member `Ind θ0` and its (distinct) conjugate. -/
theorem SsubFiltration_commutator_coherent [Finite G] {L : Subgroup G}
    (hyp : Hypothesis L) (hodd : Odd (Nat.card ↥L)) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    [Group.IsNilpotent ↥((hyp.typeI.typeF.H).subgroupOf L)] :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (hyp.SsubFiltration ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆)
      hyp.A) := by
  classical
  have := hyp.finiteG
  -- `S(H′) ⊆ Sset` is finite.
  have hSsetfin : hyp.Sset.Finite := by
    have := finite_irreducibleCharacter (G := ↥((hyp.typeI.typeF.H).subgroupOf L))
    have hsub : hyp.Sset ⊆ Set.range
        (fun θ : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) =>
          ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L) θ.toClassFunction) := by
      rintro χ ⟨θ, _, rfl⟩; exact ⟨θ, rfl⟩
    exact (Set.finite_range _).subset hsub
  have hSfin : (hyp.SsubFiltration
      ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆).Finite :=
    hSsetfin.subset hyp.SsubFiltration_subset_Sset
  -- `K` is nontrivial.
  have hHsub_ne : ((hyp.typeI.typeF.H).subgroupOf L) ≠ ⊥ := by
    rw [Ne, Subgroup.subgroupOf_eq_bot]
    intro hdisj
    have h := disjoint_iff.mp hdisj
    rw [inf_of_le_left hyp.typeI.typeF.H_le] at h
    exact hyp.typeI.typeF.H_nontrivial h
  have : Nontrivial ↥((hyp.typeI.typeF.H).subgroupOf L) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hHsub_ne
  -- `K/⁅K,K⁆` is nontrivial (`K` nilpotent nontrivial is not perfect).
  have hcomm_lt : commutator ↥((hyp.typeI.typeF.H).subgroupOf L) < ⊤ :=
    Group.IsSolvable.commutator_lt_top_of_nontrivial ↥((hyp.typeI.typeF.H).subgroupOf L)
  have : Nontrivial (↥((hyp.typeI.typeF.H).subgroupOf L) ⧸
      commutator ↥((hyp.typeI.typeF.H).subgroupOf L)) := by
    rw [QuotientGroup.nontrivial_iff]; exact hcomm_lt.ne
  -- a nontrivial character of the abelianization, inflated to a member `θ0` of `S(H′)`.
  have := finite_irreducibleCharacter (G := ↥((hyp.typeI.typeF.H).subgroupOf L) ⧸
    commutator ↥((hyp.typeI.typeF.H).subgroupOf L))
  obtain ⟨g, hg⟩ := exists_ne (1 : ↥((hyp.typeI.typeF.H).subgroupOf L) ⧸
    commutator ↥((hyp.typeI.typeF.H).subgroupOf L))
  have : Nontrivial (ConjClasses (↥((hyp.typeI.typeF.H).subgroupOf L) ⧸
      commutator ↥((hyp.typeI.typeF.H).subgroupOf L))) :=
    ⟨ConjClasses.mk g, ConjClasses.mk 1,
      fun h => hg (isConj_one_left.mp (ConjClasses.mk_eq_mk_iff_isConj.mp h))⟩
  have : Nontrivial (IrreducibleCharacter (↥((hyp.typeI.typeF.H).subgroupOf L) ⧸
      commutator ↥((hyp.typeI.typeF.H).subgroupOf L))) :=
    Finite.one_lt_card_iff_nontrivial.mp
      (by rw [card_irreducibleCharacter_eq]
          exact Finite.one_lt_card_iff_nontrivial.mpr inferInstance)
  obtain ⟨χbar, hχbar⟩ := exists_ne (trivialIrreducibleCharacter
    (↥((hyp.typeI.typeF.H).subgroupOf L) ⧸ commutator ↥((hyp.typeI.typeF.H).subgroupOf L)))
  have hθ0ne : inflate (commutator ↥((hyp.typeI.typeF.H).subgroupOf L)) χbar
      ≠ trivialIrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) := fun h =>
    hχbar (inflate_injective (N := commutator ↥((hyp.typeI.typeF.H).subgroupOf L))
      (h.trans (inflate_trivial (N := commutator ↥((hyp.typeI.typeF.H).subgroupOf L))).symm))
  set χ0 := ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L)
    ((inflate (commutator ↥((hyp.typeI.typeF.H).subgroupOf L)) χbar).toClassFunction) with hχ0def
  have hχ0S : χ0 ∈ hyp.SsubFiltration
      ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆ := by
    simp only [Hypothesis.SsubFiltration, Set.mem_ofPred_eq]
    refine ⟨inflate (commutator ↥((hyp.typeI.typeF.H).subgroupOf L)) χbar, hθ0ne, ?_, rfl⟩
    rw [OddOrder.Peterfalvi.S08.commutator_subgroupOf_self]
    exact subset_characterKernel_inflate (commutator ↥((hyp.typeI.typeF.H).subgroupOf L)) χbar
  have hχ0cS := SsubFiltration_commutator_closedUnderConjugate hyp hχ0S
  have hne : χ0 ≠ χ0.conj := fun h =>
    (Sset_hasNoRealCharacters hyp hodd hfrob (hyp.SsubFiltration_subset_Sset hχ0S)) h.symm
  have hcard : 2 ≤ (hyp.SsubFiltration
      ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆).ncard := by
    calc 2 = ({χ0, χ0.conj} : Set (ClassFunction ↥L ℂ)).ncard := (Set.ncard_pair hne).symm
      _ ≤ _ := Set.ncard_le_ncard (by rintro x (rfl | rfl); exacts [hχ0S, hχ0cS]) hSfin
  refine OddOrder.Peterfalvi.S07.coherent_of_constant_degree
    { tau := hyp.tau
      tau_isometry_diff := fun _ _ hφ hψ =>
        OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported
          hyp.dadeData.dade hφ.2 hψ.2
      conjugate_closed := fun _ hχ => SsubFiltration_commutator_closedUnderConjugate hyp hχ
      no_real_characters := fun _ hχ =>
        Sset_hasNoRealCharacters hyp hodd hfrob (hyp.SsubFiltration_subset_Sset hχ)
      pairwise_orthogonal := fun _ _ hφ hχ hne =>
        Sset_pairwiseOrthogonal hyp hodd hfrob (hyp.SsubFiltration_subset_Sset hφ)
          (hyp.SsubFiltration_subset_Sset hχ) hne
      difference_image := fun _ hχ =>
        SsubFiltration_commutator_differenceImage hyp hodd hfrob hAH hχ
      difference_images_orthogonal := fun _ _ hφ hχ h1 h2 =>
        SsubFiltration_commutator_differenceImages_orthogonal hyp hodd hfrob hAH hφ hχ h1 h2 }
    hSfin hcard ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun ζ hζ => Sset_inner_self_eq_one hyp hfrob (hyp.SsubFiltration_subset_Sset hζ)
  · exact fun a ha b hb => SsubFiltration_commutator_tau_diff_mem_ZIrr hyp hfrob hAH ha hb
  · exact fun a ha b hb => by
      rw [SsubFiltration_commutator_apply_one_eq_index hyp ha,
        SsubFiltration_commutator_apply_one_eq_index hyp hb]
  · exact fun a ha => by
      rw [SsubFiltration_commutator_apply_one_eq_index hyp ha]
      exact Nat.cast_ne_zero.mpr Subgroup.index_ne_zero_of_finite
  · exact OddOrder.Peterfalvi.S09.Cert.one_not_mem_supportInSubgroup_sharp hyp.typeI.typeF.H hAH
  · exact fun a ha b hb => SsubFiltration_commutator_diff_supported hyp hAH ha hb

/-- **The witness kernel `K = (L_F).subgroupOf L` is nilpotent** — the `[IsNilpotent ↥K]` input of
`SsubFiltration_commutator_coherent` (and the (6.5) engine).  `L_F = maxNilpotentNormalHall L` is
nilpotent (`maxNilpotentNormalHall_isNilpotent`), and `K ≃* L_F` (`subgroupOfEquivOfLe`, `L_F ≤ L`)
transfers nilpotency. -/
theorem typeF_H_subgroupOf_isNilpotent [Finite G] {L : Subgroup G} (hyp : Hypothesis L) :
    Group.IsNilpotent ↥((hyp.typeI.typeF.H).subgroupOf L) := by
  have := hyp.finiteG
  have : Group.IsNilpotent ↥(hyp.typeI.typeF.H) := by
    rw [hyp.typeI.typeF.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isNilpotent L
  exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hyp.typeI.typeF.H_le).symm

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.6) case (c): cyclic-quotient kernel → (6.5.c) coherence.** `sorry`-free.
Def (8.3) case (c): `exp(U) ∣ p − 1` for every `p ∣ |H|`; `S` is coherent by (6.5.c).

The proof feeds the abstract (6.5.c) engine `S08.nonempty_coherent_SOf_bot_of_index_dvd` on the
witness filtration `S(A) = SsubFiltration A` (`SOf`), `τ = tau`, `A0 = A`, kernel
`K = (L_F).subgroupOf L`:
* **abelian branch** (`K` commutative): `⁅K,K⁆ = ⊥`, so `S(⁅K,K⁆) = S(⊥) = S` is coherent directly
  by `hcoh` (the `S(H′)` coherence `SsubFiltration_commutator_coherent`);
* **non-abelian branch**: the engine derives "`K` is a `p`-group" internally (6.5.b) from the
  Frobenius structure and the (6.3) index bound, then closes by the (6.5.c) arithmetic; its two
  genuine character-theoretic inputs are `hcoh` and the **(5.6) break-member oracle**
  `Sset_six_two_index_bound` (`h56`).
The divisibility `[L:H] ∣ p − 1` (`hdvd`) comes from `_hexp`: the odd Frobenius complement `C` is a
Z-group (`S10.isZGroup_of_isFrobeniusGroup_of_odd`), Schur–Zassenhaus makes `C ≃ U`, so `U` is a
Z-group and `[L:H] = |U| = exp(U)` (Def (8.3.c)). Closes issue 2032 / hub issue 9001. -/
theorem frobenius_typeI_coherent_of_cyclicQuotient [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G}
    (hyp : Hypothesis L)
    (_hfrob : ∃ C : Subgroup ↥L,
      OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L (hyp.H.subgroupOf L) C)
    (_hexp : (∀ p : ℕ, p.Prime → p ∈ (Nat.card ↥hyp.typeI.typeF.H).primeFactors →
        Monoid.exponent hyp.typeI.typeF.U ∣ p - 1) ∧
      ∃ p : ℕ, p.Prime ∧ p ∈ (Nat.card ↥hyp.typeI.typeF.H).primeFactors ∧
        IsCyclic ↥(OddOrder.GroupTheory.opiCoreInG {p}ᶜ hyp.typeI.typeF.H)) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A) := by
  classical
  have := hyp.finiteG
  obtain ⟨C, hfrob⟩ := _hfrob
  have hfrobK : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L
      ((hyp.typeI.typeF.H).subgroupOf L) C := hfrob
  have hodd : Odd (Nat.card ↥L) := _hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card L)
  have hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1} :=
    hyp.typeIA_eq_sharp_of_frobenius hfrobK
  have hKnilp : Group.IsNilpotent ↥((hyp.typeI.typeF.H).subgroupOf L) :=
    typeF_H_subgroupOf_isNilpotent hyp
  have hKnorm : ((hyp.typeI.typeF.H).subgroupOf L).Normal := typeF_H_subgroupOf_normal hyp
  have hKntriv : Nontrivial ↥((hyp.typeI.typeF.H).subgroupOf L) := by
    rw [Subgroup.nontrivial_iff_ne_bot, Ne, Subgroup.subgroupOf_eq_bot]
    intro hdisj
    have h := disjoint_iff.mp hdisj
    rw [inf_of_le_left hyp.typeI.typeF.H_le] at h
    exact hyp.typeI.typeF.H_nontrivial h
  -- `⁅K,K⁆ ⊊ K` (nontrivial nilpotent kernel is not perfect).
  have hH'lt : (⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆
      : Subgroup ↥L) < (hyp.typeI.typeF.H).subgroupOf L := by
    have h1 : _root_.commutator ↥((hyp.typeI.typeF.H).subgroupOf L) < ⊤ :=
      Group.IsSolvable.commutator_lt_top_of_nontrivial _
    rw [← OddOrder.Peterfalvi.S08.commutator_subgroupOf_self] at h1
    refine lt_of_le_of_ne (Subgroup.commutator_le_left _ _) (fun heq => ?_)
    rw [heq, Subgroup.subgroupOf_self] at h1
    exact lt_irrefl _ h1
  have hcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (hyp.SsubFiltration ⁅(hyp.typeI.typeF.H).subgroupOf L,
        (hyp.typeI.typeF.H).subgroupOf L⁆) hyp.A) :=
    SsubFiltration_commutator_coherent hyp hodd hfrobK hAH
  -- `[L:H] ∣ p − 1` for every prime `p ∣ |H|`: the complement `C` is an odd Frobenius complement,
  -- hence a Z-group; by Schur–Zassenhaus `C ≃ U`, so `U` is a Z-group and
  -- `[L:H] = |U| = exp(U)` (Def (8.3.c), `_hexp`).
  have hdvd : ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥((hyp.typeI.typeF.H).subgroupOf L) →
      ((hyp.typeI.typeF.H).subgroupOf L).index ∣ p - 1 := by
    have hCodd : Odd (Nat.card ↥C) := Odd.of_dvd_nat hodd C.card_subgroup_dvd_card
    have hZC : _root_.IsZGroup ↥C :=
      OddOrder.Peterfalvi.S10.isZGroup_of_isFrobeniusGroup_of_odd hfrobK hCodd
    have hN : Nat.Coprime (Nat.card ↥((hyp.typeI.typeF.H).subgroupOf L))
        ((hyp.typeI.typeF.H).subgroupOf L).index := by
      rw [hfrobK.isComplement.symm.index_eq_card]
      exact hfrobK.coprime_card_kernel_complement
    obtain ⟨n, -, hconj⟩ := Subgroup.IsComplement'.exists_conj_of_coprime hN
      (Or.inl inferInstance) hfrobK.isComplement hyp.typeI.typeF.complement
    have e := Subgroup.equivMapOfInjective C (MulAut.conj n).toMonoidHom (MulAut.conj n).injective
    rw [hconj] at e
    have hZUsub : _root_.IsZGroup ↥((hyp.typeI.typeF.U).subgroupOf L) :=
      _root_.IsZGroup.of_injective (f := e.symm.toMonoidHom) e.symm.injective
    have hZU : _root_.IsZGroup ↥(hyp.typeI.typeF.U) :=
      _root_.IsZGroup.of_injective
        (f := (Subgroup.subgroupOfEquivOfLe hyp.typeI.typeF.U_le).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hyp.typeI.typeF.U_le).symm.injective
    have hidxU : ((hyp.typeI.typeF.H).subgroupOf L).index = Nat.card ↥(hyp.typeI.typeF.U) := by
      rw [hyp.typeI.typeF.complement.symm.index_eq_card,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.typeI.typeF.U_le).toEquiv]
    have hexpU : Monoid.exponent ↥(hyp.typeI.typeF.U) = Nat.card ↥(hyp.typeI.typeF.U) :=
      _root_.IsZGroup.exponent_eq_card (G := ↥hyp.typeI.typeF.U)
    intro p hp hpK
    have hpH : p ∣ Nat.card ↥(hyp.typeI.typeF.H) := by
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.typeI.typeF.H_le).toEquiv] at hpK
    have hmem : p ∈ (Nat.card ↥(hyp.typeI.typeF.H)).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, hpH, Nat.card_pos.ne'⟩
    have hdvd1 := _hexp.1 p hp hmem
    rwa [hidxU, ← hexpU]
  by_cases hnonab : ¬ ∀ a b : ↥((hyp.typeI.typeF.H).subgroupOf L), a * b = b * a
  · -- **Non-abelian branch:** the genuine (6.5.c) contradiction via the engine.
    rw [← hyp.SsubFiltration_bot]
    refine OddOrder.Peterfalvi.S08.nonempty_coherent_SOf_bot_of_index_dvd hKnorm hyp.tau hyp.A
      hyp.SsubFiltration
      hfrobK hnonab hodd hdvd hH'lt hcoh
      (fun A B _ _ hBA hAle _ hSAcoh hSBncoh =>
        Sset_six_two_index_bound hyp hodd hfrobK hAH (hyp.SsubFiltration_antitone hBA)
          ?_ hSAcoh hSBncoh)
    · -- `commutator (K / A) ≠ ⊤` from `A ≤ ⁅K,K⁆ < K` (nilpotent quotient not perfect).
      have hnle : ¬ ((hyp.typeI.typeF.H).subgroupOf L) ≤ A :=
        fun hle => lt_irrefl _ (lt_of_le_of_lt (le_trans hle hAle) hH'lt)
      have hAne : A.subgroupOf ((hyp.typeI.typeF.H).subgroupOf L) ≠ ⊤ := by
        rw [Ne, Subgroup.subgroupOf_eq_top]; exact hnle
      have : Nontrivial (↥((hyp.typeI.typeF.H).subgroupOf L) ⧸
          A.subgroupOf ((hyp.typeI.typeF.H).subgroupOf L)) :=
        Subgroup.nontrivial_quotient_of_ne_top hAne
      exact (Group.IsSolvable.commutator_lt_top_of_nontrivial _).ne
  · -- **Abelian branch:** `⁅K,K⁆ = ⊥`, so `S(⁅K,K⁆) = S(⊥) = Sset` is coherent by `hcoh`.
    push Not at hnonab
    have hcomm_bot : (⁅(hyp.typeI.typeF.H).subgroupOf L,
        (hyp.typeI.typeF.H).subgroupOf L⁆ : Subgroup ↥L) = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro p hp q hq
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_commute]
      have h := hnonab ⟨p, hp⟩ ⟨q, hq⟩
      have h3 := Subtype.ext_iff.mp h
      simpa [commute_iff_eq] using h3
    rw [← hyp.SsubFiltration_bot, ← hcomm_bot]
    exact hcoh

/-- **Frobenius realization bridge for type I** (the `kernel = M_F` form consumed by (12.10)).
A type-I maximal `M` whose complement `U = M/M_F` is a **Z-group** is a Frobenius group with kernel
`M_F = typeF.H`.  Wraps the §8 (8.2.b) `⟸` half `S10.typeF_frobenius_of_isZGroup` on
`data.typeF` (the former local duplicate of that lemma was removed in the issue-0172 §8 audit). -/
theorem typeI_frobenius_of_isZGroup_complement [Finite G] {M : Subgroup G}
    (data : TypeIData M) (hZ : _root_.IsZGroup ↥data.typeF.U) :
    OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥M (data.typeF.H.subgroupOf M)
      (data.typeF.U.subgroupOf M) :=
  OddOrder.Peterfalvi.S10.typeF_frobenius_of_isZGroup data.typeF hZ

end OddOrder.Peterfalvi.S14


