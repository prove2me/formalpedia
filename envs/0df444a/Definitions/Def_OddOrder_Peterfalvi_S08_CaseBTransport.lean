-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S08_CaseBTransport
-- name    : OddOrder_Peterfalvi_S08_CaseBTransport
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T07:02:22.076402+00:00
-- url     : https://prove2.me/theorems/68d4d165-6db7-4f99-b157-da8dbbae64fe
-- title:
--   Peterfalvi §8 case (B): transport lemmas
-- statement:
--   Part of the Peterfalvi §8 case-(B) coherence development, containing transport lemmas. The bundle consists of lemmas only.
--
--   The bundle also proves 2 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S08_CaseBTransport.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S08_CaseBTransport.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedTransport
import Definitions.Def_OddOrder_Peterfalvi_S08_CaseBCoherence
import Definitions.Def_OddOrder_Peterfalvi_S06_CertainTypeCoherence

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]

variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]

variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

/-- **(6.8.2.2) good-case `X`-structure, general `Y`-coherence witness.**  The `cY`-parametrized
version of `orthogonal_tau_indW2_add_extension_caseB`: for *any* `Y`-coherence witness `cY` (e.g.
the
swapped witness from `exists_Ycoherence_hgood_caseB` in the `|Y| = 2` edge), the good value
`⟨α^τ, cY.extension η₁⟩ = −|H:Z|` makes `X := α^τ + |H:Z|·cY.extension η₁` orthogonal to the whole
family `{cY.extension η}` and lie in `ℤ[Irr G]`, giving `α^τ = X − |H:Z|·cY.extension η₁`.

The agreement `cY.extension η − cY.extension η₁ = (η − η₁)^τ` is `cY.extends_on_supported` +
`map_sub`
(inlined, since `cY` need not be `coherentYset`). -/
theorem SibleyDadeHypothesis.orthogonal_tau_indW2_add_extension_general_caseB
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {W2 : Subgroup ↥L} (hW2H : W2 ≤ H) (hW2comm : W2 ≤ ⁅H, H⁆)
    [Invertible (Nat.card ↥W2 : ℂ)]
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    (φ : IrreducibleCharacter ↥W2) (_hφ1 : (φ : ClassFunction ↥W2 ℂ) 1 = 1)
    (h1 : ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ) 1
      = ((W2.subgroupOf H).index : ℂ) * η₁ 1)
    (hgood : ClassFunction.inner (hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
        - ((W2.subgroupOf H).index : ℂ) • η₁)) (cY.extension η₁)
      = -((W2.subgroupOf H).index : ℂ)) :
    (∀ η ∈ hyp.Yset,
        ClassFunction.inner (hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
            - ((W2.subgroupOf H).index : ℂ) • η₁)
          + ((W2.subgroupOf H).index : ℂ) • cY.extension η₁)
          (cY.extension η) = 0)
      ∧ hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
          - ((W2.subgroupOf H).index : ℂ) • η₁)
          + ((W2.subgroupOf H).index : ℂ) • cY.extension η₁ ∈ ZIrr G := by
  have : Fintype ↥W2 := Fintype.ofFinite _
  classical
  have hYon : ∀ η η', η ∈ hyp.Yset → η' ∈ hyp.Yset →
      ClassFunction.inner (cY.extension η) (cY.extension η')
        = if η = η' then (1 : ℂ) else 0 := by
    intro η η' hη hη'
    rw [cY.extension_inner_eq η η' (Submodule.subset_span hη) (Submodule.subset_span hη')]
    have h := irreducibleCharacter_inner_eq_ite
      (⟨η, hyp.isIrreducibleCharacter_of_mem_Yset hη⟩ : IrreducibleCharacter ↥L)
      (⟨η', hyp.isIrreducibleCharacter_of_mem_Yset hη'⟩ : IrreducibleCharacter ↥L)
    simpa using h
  have hcoeff0 : ∀ η ∈ hyp.Yset, η ≠ η₁ →
      ClassFunction.inner (hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
        - ((W2.subgroupOf H).index : ℂ) • η₁)) (cY.extension η) = 0 := by
    intro η hη hne
    have hconst := hyp.inner_tau_indW2_sub_smul_tau_Yset_diff hW2H hW2comm φ hη₁ hη hne
      ((W2.subgroupOf H).index : ℂ) h1
    have hsuppd : (η - η₁).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
      hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hη) (hyp.Yset_subset_S hη₁)
        ((hyp.Yset_apply_one hη).trans (hyp.Yset_apply_one hη₁).symm)
    have htaud : hyp.tau (η - η₁) = cY.extension η - cY.extension η₁ := by
      rw [← cY.extends_on_supported (η - η₁)
        ⟨Submodule.sub_mem _ (Submodule.subset_span hη) (Submodule.subset_span hη₁), hsuppd⟩,
        map_sub]
    rw [htaud, ClassFunction.inner_sub_right, hgood] at hconst
    linear_combination hconst
  have he₁e₁ : ClassFunction.inner (cY.extension η₁) (cY.extension η₁) = 1 := by
    rw [hYon η₁ η₁ hη₁ hη₁, if_pos rfl]
  refine ⟨?_, ?_⟩
  · intro η hη
    rw [ClassFunction.inner_add_left, ClassFunction.inner_smul_left]
    by_cases hee : η = η₁
    · subst hee; rw [hgood, he₁e₁]; ring
    · rw [hcoeff0 η hη hee, hYon η₁ η hη₁ hη, if_neg (Ne.symm hee)]; ring
  · have hsuppX : (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
        - ((W2.subgroupOf H).index : ℂ) • η₁).support
        ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
      hyp.support_indW2_sub_smul_subset_sharpImage hW2H φ hη₁ _ h1
    have hsrcZ : ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
        - ((W2.subgroupOf H).index : ℂ) • η₁ ∈ ZIrr (↥L) := by
      rw [Nat.cast_smul_eq_nsmul]
      exact sub_mem (ClassFunction.induce_mem_ZIrr W2 (IsIrreducibleCharacter.mem_ZIrr φ.2))
        (nsmul_mem (hyp.isIrreducibleCharacter_of_mem_Yset hη₁).mem_ZIrr (W2.subgroupOf H).index)
    have hvZ : hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
        - ((W2.subgroupOf H).index : ℂ) • η₁) ∈ ZIrr G :=
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
        hyp.dade hsuppX hsrcZ
    have he₁Z : ((W2.subgroupOf H).index : ℂ) • cY.extension η₁ ∈ ZIrr G := by
      rw [Nat.cast_smul_eq_nsmul]
      exact nsmul_mem (cY.extension_mem_ZIrr η₁ (Submodule.subset_span hη₁)) (W2.subgroupOf H).index
    exact add_mem hvZ he₁Z

/-- **Norm of a character induced from a central subgroup** (a (6.8.2.3) ingredient).  If `N` is a
central subgroup of a finite group `M` and `φ ∈ Irr N` (necessarily linear), then
`‖Ind^M_N φ‖² = |M : N|`.  Indeed `N ⊴ M` (central), conjugation acts trivially on `N`, so the
Mackey
restriction `|N|·Res_N(Ind^M_N φ) = ∑_{x∈M} φ^{x⁻¹} = |M|·φ` collapses; Frobenius reciprocity
`⟨Ind φ, Ind φ⟩ = ⟨φ, Res(Ind φ)⟩` then gives `|N|·‖Ind φ‖² = |M|`, i.e. `‖Ind φ‖² = |M:N|`.

This is the `∑ aᵢ² = |H : Z|` step of Peterfalvi (6.8.2.3) (`Z = W₂ ⊆ Z(H)`, applied with `M = ↥H`,
`N = W₂.subgroupOf H`): the squared multiplicities of `Ind^H_Z φ` sum to
`‖Ind^H_Z φ‖² = |H : Z|`. -/
theorem inner_induce_self_eq_index_of_le_center
    {M : Type*} [Group M] [Fintype M] [Invertible (Nat.card M : ℂ)]
    {N : Subgroup M} [Finite ↥N] [Invertible (Nat.card ↥N : ℂ)]
    (hN : N ≤ Subgroup.center M)
    {φ : ClassFunction ↥N ℂ} (hφ : IsIrreducibleCharacter φ) :
    ClassFunction.inner (ClassFunction.induce N φ) (ClassFunction.induce N φ)
      = (N.index : ℂ) := by
  classical
  have : Fintype ↥N := Fintype.ofFinite _
  have hNnorm : N.Normal := by
    constructor
    intro n hn g
    have hc : g * n = n * g := (Subgroup.mem_center_iff.mp (hN hn)) g
    have : g * n * g⁻¹ = n := by rw [hc, mul_assoc, mul_inv_cancel, mul_one]
    rw [this]; exact hn
  -- conjugation acts trivially on the central `N`.
  have hconjtriv : ∀ x : M, ClassFunction.conjBy x⁻¹ φ = φ := by
    intro x
    ext h
    rw [ClassFunction.conjBy_apply]
    have hheq : x⁻¹ * (h : M) * (x⁻¹)⁻¹ = (h : M) := by
      have hcomm : x⁻¹ * (h : M) = (h : M) * x⁻¹ :=
        Subgroup.mem_center_iff.mp (hN h.2) x⁻¹
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    exact congrArg (fun y : ↥N => φ y) (Subtype.ext hheq)
  -- Mackey: `|N|·Res(Ind φ) = ∑_x φ^{x⁻¹} = |M|·φ`.
  have hmackey : (Nat.card ↥N : ℂ) • ClassFunction.restrict N (ClassFunction.induce N φ)
      = (Nat.card M : ℂ) • φ := by
    rw [card_smul_restrict_induce]
    simp only [hconjtriv]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, Nat.card_eq_fintype_card]
  -- Frobenius reciprocity + the Mackey collapse give `|N|·‖Ind φ‖² = |M|`.
  have hfrob : ClassFunction.inner (ClassFunction.induce N φ) (ClassFunction.induce N φ)
      = ClassFunction.inner φ (ClassFunction.restrict N (ClassFunction.induce N φ)) :=
    ClassFunction.inner_induce_eq_inner_restrict N φ (ClassFunction.induce N φ)
  have hself : ClassFunction.inner φ φ = 1 := by
    have := irreducibleCharacter_inner_eq_ite (⟨φ, hφ⟩ : IrreducibleCharacter ↥N) ⟨φ, hφ⟩
    simpa using this
  have : Nonempty ↥N := ⟨1⟩
  have hstep : (Nat.card ↥N : ℂ) *
      ClassFunction.inner φ (ClassFunction.restrict N (ClassFunction.induce N φ))
      = (Nat.card M : ℂ) := by
    have h := congrArg (ClassFunction.inner φ) hmackey
    rw [OddOrder.RepresentationTheory.inner_smul_right,
      OddOrder.RepresentationTheory.inner_smul_right, star_natCast, star_natCast, hself,
      mul_one] at h
    exact h
  have hcardN : (Nat.card ↥N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hcardeq : (Nat.card ↥N : ℂ) * (N.index : ℂ) = (Nat.card M : ℂ) := by
    rw [← Nat.cast_mul, Subgroup.card_mul_index N]
  rw [← hfrob, ← hcardeq] at hstep
  exact mul_left_cancel₀ hcardN hstep

end OddOrder.Peterfalvi.S08


