-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S08_CaseBWeightedEndgame
-- name    : OddOrder_Peterfalvi_S08_CaseBWeightedEndgame
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T07:20:22.696774+00:00
-- url     : https://prove2.me/theorems/b70f502a-5a65-46c5-bdf5-dbd04a0797a5
-- title:
--   Peterfalvi (6.8.3): case-(B) norm-weighted endgame
-- statement:
--   Peterfalvi, *Character Theory for the Odd Order Theorem*, §6, (6.8.3). This file assembles the case-(B) (6.8.3) contradiction from the norm-weighted member-family bound and the fixed-point-free arithmetic spine of the case-(B) endgame.
--
--   Results: `sum_re_div_normSq_Xset_eq` (the (6.6) norm-weighted $X$ degree-square identity), `Xset_nonempty_of_subgroupOf_ne_bot_weighted` ($X$-set nonemptiness, norm-weighted) and `xSum_le_two_psi_caseB` and `xSum_le_two_psi_caseB_columnBreak` (the (6.2) norm-weighted $X$-sum bound).
--
--   The bundle also proves 3 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S08_CaseBWeightedEndgame.lean

/-
Copyright (c) 2026 The Odd Order Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S08_CaseBWeightedEndgame.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S08_CaseBEnumeration
import Definitions.Def_OddOrder_Peterfalvi_S08_CaseBEndgame

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]

variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]

variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

open scoped Classical in
/-- **(6.6) norm-weighted `X` degree-square identity** (case-(B) form).

The norm-weighted degree-square sum over `X = S − S(Z)` is `|L:H|·(|H| − |H:Z|)`.  Unlike the
Frobenius `sum_re_sq_Xset_eq` (which uses `χ(1)²/‖χ‖² = χ(1).re²` from irreducibility of every
member), this keeps the `/‖χ‖²` weights and so is valid even when `X` contains the **reducible**
certain-type columns of case (B): it routes through the complex orbit-count
`sum_div_normSq_induce_kernelFilter_eq` (in the `χ(1)²/⟨χ,χ⟩` form, valid for reducibles), taking
the difference of the `A = ⊥` and `A = Z` filter sums via `Finset.sum_sdiff`.  The per-summand real
conversion `χ(1)²/⟨χ,χ⟩ = (χ(1).re²/⟨χ,χ⟩.re : ℂ)` uses that `χ(1)` is a (real) degree
(`induce_apply_one`) and `⟨χ,χ⟩` is real (`inner_self_eq_realCast`). -/
theorem sum_re_div_normSq_Xset_eq (hyp : SibleyDadeHypothesis G L H) {Z : Subgroup ↥L} [Z.Normal] :
    ∑ χ ∈ ((Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧
              θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) \
        (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑(Z.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧
              θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction)),
        ((χ 1).re) ^ 2 / (ClassFunction.inner χ χ).re
      = (H.index : ℝ) * ((Nat.card ↥H : ℝ) - (Nat.card (↥H ⧸ Z.subgroupOf H) : ℝ)) := by
  let : H.Normal := hyp.H_normal
  have hbotker : ∀ θ : IrreducibleCharacter ↥H,
      (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥H ℂ) := by
    intro θ x hx
    rw [Subgroup.bot_subgroupOf, Subgroup.coe_bot, Set.mem_singleton_iff] at hx
    subst hx
    exact OddOrder.Peterfalvi.S03.one_mem_characterKernel _
  have hsub : (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
        (↑(Z.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
            (θ : ClassFunction ↥H ℂ) ∧
          θ ≠ trivialIrreducibleCharacter ↥H)).image
        (fun θ => ClassFunction.induce H θ.toClassFunction) ⊆
      (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
        (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
            (θ : ClassFunction ↥H ℂ) ∧
          θ ≠ trivialIrreducibleCharacter ↥H)).image
        (fun θ => ClassFunction.induce H θ.toClassFunction) := by
    apply Finset.image_subset_image
    intro θ hθ
    rw [Finset.mem_filter] at hθ ⊢
    exact ⟨hθ.1, hbotker θ, hθ.2.2⟩
  have hsd := Finset.sum_sdiff
    (f := fun χ : ClassFunction ↥L ℂ => χ 1 ^ 2 / ClassFunction.inner χ χ) hsub
  have hB2bot := @sum_div_normSq_induce_kernelFilter_eq ↥L _ _ _ H _ _ (⊥ : Subgroup ↥L) _
  have hB2Z := @sum_div_normSq_induce_kernelFilter_eq ↥L _ _ _ H _ _ Z _
  have hbotcard : Nat.card (↥H ⧸ (⊥ : Subgroup ↥L).subgroupOf H) = Nat.card ↥H := by
    rw [Subgroup.bot_subgroupOf]
    exact Nat.card_congr (QuotientGroup.quotientBot (G := ↥H)).toEquiv
  rw [hbotcard] at hB2bot
  -- the complex weighted `X`-set identity.
  have hcomplex : ∑ χ ∈ ((Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
              (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                  (θ : ClassFunction ↥H ℂ) ∧
                θ ≠ trivialIrreducibleCharacter ↥H)).image
            (fun θ => ClassFunction.induce H θ.toClassFunction) \
          (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
              (↑(Z.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                  (θ : ClassFunction ↥H ℂ) ∧
                θ ≠ trivialIrreducibleCharacter ↥H)).image
            (fun θ => ClassFunction.induce H θ.toClassFunction)),
          χ 1 ^ 2 / ClassFunction.inner χ χ
        = (H.index : ℂ) * ((Nat.card ↥H : ℂ) - (Nat.card (↥H ⧸ Z.subgroupOf H) : ℂ)) := by
    rw [eq_sub_of_add_eq hsd, hB2bot, hB2Z]; ring
  -- per-summand real conversion `χ(1)²/⟨χ,χ⟩ = (χ(1).re²/⟨χ,χ⟩.re : ℂ)`.
  have hconv : ∀ χ ∈ ((Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧
              θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) \
        (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑(Z.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧
              θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction)),
      χ 1 ^ 2 / ClassFunction.inner χ χ
        = (((χ 1).re ^ 2 / (ClassFunction.inner χ χ).re : ℝ) : ℂ) := by
    intro χ hχ
    rw [Finset.mem_sdiff] at hχ
    obtain ⟨θ, -, rfl⟩ := Finset.mem_image.mp hχ.1
    obtain ⟨d, -, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
    have hχ1 : ClassFunction.induce H (θ : ClassFunction ↥H ℂ) (1 : ↥L)
        = ((H.index * d : ℕ) : ℂ) := by
      rw [ClassFunction.induce_apply_one, hd]; push_cast; ring
    have hr : (ClassFunction.induce H (θ : ClassFunction ↥H ℂ) (1 : ↥L)).re
        = ((H.index * d : ℕ) : ℝ) := by
      rw [hχ1, Complex.natCast_re]
    rw [hr, hχ1, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast]
    congr 1
    rw [inner_self_eq_realCast (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)), Complex.ofReal_re]
  -- combine: cast the real sum to `ℂ`, rewrite each summand, identify with `hcomplex`.
  have key : (((∑ χ ∈ ((Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
              (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                  (θ : ClassFunction ↥H ℂ) ∧
                θ ≠ trivialIrreducibleCharacter ↥H)).image
            (fun θ => ClassFunction.induce H θ.toClassFunction) \
          (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
              (↑(Z.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                  (θ : ClassFunction ↥H ℂ) ∧
                θ ≠ trivialIrreducibleCharacter ↥H)).image
            (fun θ => ClassFunction.induce H θ.toClassFunction)),
          ((χ 1).re) ^ 2 / (ClassFunction.inner χ χ).re : ℝ)) : ℂ)
      = (((H.index : ℝ) * ((Nat.card ↥H : ℝ) - (Nat.card (↥H ⧸ Z.subgroupOf H) : ℝ))) : ℝ) := by
    rw [Complex.ofReal_sum, Finset.sum_congr rfl (fun χ hχ => (hconv χ hχ).symm), hcomplex]
    push_cast; ring
  exact Complex.ofReal_inj.mp key

open scoped Classical in
/-- **(6.6)/(6.8) X-set nonemptiness, norm-weighted (case-B, no Frobenius).**  As
`Xset_nonempty_of_subgroupOf_ne_bot`, but the strictly-positive degree sum is the **norm-weighted**
identity `sum_re_div_normSq_Xset_eq` (`∑_{X(Z)} χ(1).re²/‖χ‖² = |L:H|(|H|−|H:Z|)`, valid for
reducible `X`-members), so no Frobenius / `X`-irreducibility hypothesis is needed.  Since
`Z.subgroupOf H ≠ ⊥` gives `|H:Z| < |H|`, the weighted sum is `> 0`, hence `X(Z) ≠ ∅`.  This is the
case-(B) discharge of the `hXne` obligation of `nonempty_coherent_S_caseB_of_c2`. -/
theorem Xset_nonempty_of_subgroupOf_ne_bot_weighted (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} [Z.Normal] (hZbot : Z.subgroupOf H ≠ ⊥) :
    (hyp.Xset Z).Nonempty := by
  have : Fintype ↥H := Fintype.ofFinite _
  have hXsum := sum_re_div_normSq_Xset_eq hyp (Z := Z)
  set Xdiff := (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
          (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
              (θ : ClassFunction ↥H ℂ) ∧
            θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) \
        (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑(Z.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧
              θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) with hXdiffdef
  have hlt : Nat.card (↥H ⧸ Z.subgroupOf H) < Nat.card ↥H := by
    have h2 : 1 < Nat.card ↥(Z.subgroupOf H) := (Z.subgroupOf H).one_lt_card_iff_ne_bot.mpr hZbot
    have hcard : Nat.card ↥H
        = Nat.card (↥H ⧸ Z.subgroupOf H) * Nat.card ↥(Z.subgroupOf H) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf H)
    calc Nat.card (↥H ⧸ Z.subgroupOf H)
        < Nat.card (↥H ⧸ Z.subgroupOf H) * Nat.card ↥(Z.subgroupOf H) :=
          lt_mul_of_one_lt_right Nat.card_pos h2
      _ = Nat.card ↥H := hcard.symm
  have hidxpos : 0 < H.index := by rw [hyp.index_H_eq_card_W1]; exact Nat.card_pos
  have hpos : (0 : ℝ) < (H.index : ℝ) *
      ((Nat.card ↥H : ℝ) - (Nat.card (↥H ⧸ Z.subgroupOf H) : ℝ)) := by
    refine mul_pos (by exact_mod_cast hidxpos) ?_
    have : (Nat.card (↥H ⧸ Z.subgroupOf H) : ℝ) < (Nat.card ↥H : ℝ) := by exact_mod_cast hlt
    linarith
  rw [← hXsum] at hpos
  have hne : Xdiff.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hpos
    exact lt_irrefl 0 hpos
  obtain ⟨χ, hχ⟩ := hne
  refine ⟨χ, ?_⟩
  rw [hXdiffdef, Finset.mem_sdiff] at hχ
  obtain ⟨hχbot, hχnotZ⟩ := hχ
  obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hχbot
  obtain ⟨-, -, hθne⟩ := Finset.mem_filter.mp hθ
  have hχS : ClassFunction.induce H θ.toClassFunction ∈ hyp.S := by
    rw [hyp.S_eq]; exact ⟨θ, hθne, rfl⟩
  have hχnotSZ : ClassFunction.induce H θ.toClassFunction ∉ hyp.SsubFiltration Z := by
    intro hmem
    rw [hyp.mem_SsubFiltration] at hmem
    obtain ⟨θ', hne', hker', heq'⟩ := hmem
    exact hχnotZ (Finset.mem_image.mpr
      ⟨θ', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hker', hne'⟩, heq'.symm⟩)
  exact hyp.mem_Xset.mpr ⟨hχS, hχnotSZ⟩

open scoped Classical in
/-- **(6.2) norm-weighted `X`-sum bound** (case-(B) form).

The norm-weighted Peterfalvi (5.6) inequality for case (B): if `X(W₂) ∪ Y` is coherent but adding
the break pair `{ψ, ψ̄}` (`ψ ∈ S`, `{ψ, ψ̄}` disjoint from `X(W₂) ∪ Y`) is **not** coherent, then
the degree-square count over `X(W₂)` is bounded by `|L:H|·(|H| − |H:W₂|) ≤ 2·ψ(1).re·η(1).re`.

This is the weighted analogue of `xSum_le_two_psi` (`S08_CoherenceCorePart2`): the brick-3 family
bound `∑ⱼ χⱼ(1).re²/mcⱼ ≤ 2ψ(1).re·η(1).re` (`sMember_degreeSqNormReBound_of_not_coherent`) bounds
the sum over the enumerated `X(W₂) ∪ Y` family, into which the norm-weighted `X`-set identity
`sum_re_div_normSq_Xset_eq` injects `∑_{χ∈X(W₂)} χ(1).re²/‖χ‖²` (`X(W₂) ⊆ X(W₂) ∪ Y`, with
nonnegative weighted summands `inner_self_re_nonneg`). -/
theorem xSum_le_two_psi_caseB
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Finite ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Finite (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {W2 : Subgroup ↥L} [W2.Normal]
    {S₁ : Set (ClassFunction ↥L ℂ)} (hS₁sub : S₁ ⊆ hyp.S)
    (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁) (hS₁fin : S₁.Finite)
    (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (hXsub : hyp.Xset W2 ⊆ S₁)
    {η : ClassFunction ↥L ℂ} (hηY : η ∈ hyp.Yset) (hηS₁ : η ∈ S₁)
    {ψ : ClassFunction ↥L ℂ} (hψS : ψ ∈ hyp.S) (hψirr : IsIrreducibleCharacter ψ)
    (hψnotS1 : ψ ∉ S₁) (hψcnotS1 : ψ.conj ∉ S₁)
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (S₁ ∪ {ψ, ψ.conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    (H.index : ℝ) * ((Nat.card ↥H : ℝ) - (Nat.card (↥H ⧸ W2.subgroupOf H) : ℝ))
      ≤ 2 * (ψ 1).re * (η 1).re := by
  have : Fintype ↥(h46.W1 ⊔ h46.W2) := Fintype.ofFinite _
  have : Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W := Fintype.ofFinite _
  classical
  obtain ⟨k, χmem, mc, hinj, hrange, hmemS1, hmcpos, hmcnorm, hfambound⟩ :=
    sMember_degreeSqNormReBound_of_not_coherent hyp h46 hHK hW1 hS₁sub hS₁conj hS₁fin hS₁coh hηY
      hηS₁ hψS hψirr hψnotS1 hψcnotS1 hnc
  have hXsum := sum_re_div_normSq_Xset_eq hyp (Z := W2)
  set Xdiff := (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
          (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
              (θ : ClassFunction ↥H ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) \
        (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑(W2.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) with hXdiffdef
  have hsub : Xdiff ⊆ (Set.range χmem).toFinset := by
    intro χ hχ
    rw [Set.mem_toFinset, hrange]
    rw [hXdiffdef, Finset.mem_sdiff] at hχ
    obtain ⟨hχbot, hχnotZ⟩ := hχ
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hχbot
    obtain ⟨-, -, hne⟩ := Finset.mem_filter.mp hθ
    have hχS : ClassFunction.induce H θ.toClassFunction ∈ hyp.S := by
      rw [hyp.S_eq]; exact ⟨θ, hne, rfl⟩
    have hχnotSZ : ClassFunction.induce H θ.toClassFunction ∉ hyp.SsubFiltration W2 := by
      intro hmem
      rw [hyp.mem_SsubFiltration] at hmem
      obtain ⟨θ', hne', hker', heq'⟩ := hmem
      exact hχnotZ (Finset.mem_image.mpr
        ⟨θ', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hker', hne'⟩, heq'.symm⟩)
    exact hXsub (hyp.mem_Xset.mpr ⟨hχS, hχnotSZ⟩)
  rw [← hXsum]
  calc ∑ χ ∈ Xdiff, ((χ 1).re) ^ 2 / (ClassFunction.inner χ χ).re
      ≤ ∑ χ ∈ (Set.range χmem).toFinset, ((χ 1).re) ^ 2 / (ClassFunction.inner χ χ).re :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun χ _ _ => div_nonneg (sq_nonneg _) (inner_self_re_nonneg χ))
    _ = ∑ j : Fin k, ((χmem j 1).re) ^ 2 / (ClassFunction.inner (χmem j) (χmem j)).re :=
        sum_toFinset_range_eq hinj (fun χ => ((χ 1).re) ^ 2 / (ClassFunction.inner χ χ).re)
    _ = ∑ j : Fin k, ((χmem j 1).re) ^ 2 / mc j := by
        refine Finset.sum_congr rfl (fun j _ => ?_); rw [hmcnorm j, Complex.ofReal_re]
    _ ≤ 2 * (ψ 1).re * (η 1).re := hfambound

open scoped Classical in
/-- **Norm-weighted (5.6) `X`-sum bound, reducible-column break form.**  The column analogue of
`xSum_le_two_psi_caseB`: when the (6.8.3) break is a reducible certain-type column
`ψ = columnSum h46 χ₂b` (not excludable when `W₂ ⊄ Z`, e.g. case (A) at `Z = Z(H) ∩ H′`), the
norm-weighted member-family bound `sMember_degreeSqNormReBound_of_not_coherent_columnBreak` (brick
3,
column form) gives
`∑_{χ∈X(W₂)} χ(1).re²/‖χ‖² = |L:H|·(|H| − |H:W₂|) ≤ 2·(columnSum χ₂b)(1).re·η(1).re`.
The `X`-sum identity (`sum_re_div_normSq_Xset_eq`) and the weighted domination are identical to the
irreducible form. -/
theorem xSum_le_two_psi_caseB_columnBreak
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Finite (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {W2 : Subgroup ↥L} [W2.Normal]
    {S₁ : Set (ClassFunction ↥L ℂ)} (hS₁sub : S₁ ⊆ hyp.S)
    (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁) (hS₁fin : S₁.Finite)
    (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (hXsub : hyp.Xset W2 ⊆ S₁)
    {η : ClassFunction ↥L ℂ} (hηY : η ∈ hyp.Yset) (hηS₁ : η ∈ S₁)
    {χ₂b : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ} (hχ₂b : χ₂b ≠ 1)
    (hψnotS1 : OddOrder.Peterfalvi.S06.columnSum h46 χ₂b ∉ S₁)
    (hψcnotS1 : (OddOrder.Peterfalvi.S06.columnSum h46 χ₂b).conj ∉ S₁)
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (S₁ ∪ {OddOrder.Peterfalvi.S06.columnSum h46 χ₂b,
        (OddOrder.Peterfalvi.S06.columnSum h46 χ₂b).conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    (H.index : ℝ) * ((Nat.card ↥H : ℝ) - (Nat.card (↥H ⧸ W2.subgroupOf H) : ℝ))
      ≤ 2 * (OddOrder.Peterfalvi.S06.columnSum h46 χ₂b 1).re * (η 1).re := by
  have : Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W := Fintype.ofFinite _
  classical
  obtain ⟨k, χmem, mc, hinj, hrange, hmemS1, hmcpos, hmcnorm, hfambound⟩ :=
    sMember_degreeSqNormReBound_of_not_coherent_columnBreak hyp h46 hHK hW1 hS₁sub hS₁conj hS₁fin
      hS₁coh hηY hηS₁ hχ₂b hψnotS1 hψcnotS1 hnc
  have hXsum := sum_re_div_normSq_Xset_eq hyp (Z := W2)
  set Xdiff := (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
          (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
              (θ : ClassFunction ↥H ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) \
        (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑(W2.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) with hXdiffdef
  have hsub : Xdiff ⊆ (Set.range χmem).toFinset := by
    intro χ hχ
    rw [Set.mem_toFinset, hrange]
    rw [hXdiffdef, Finset.mem_sdiff] at hχ
    obtain ⟨hχbot, hχnotZ⟩ := hχ
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hχbot
    obtain ⟨-, -, hne⟩ := Finset.mem_filter.mp hθ
    have hχS : ClassFunction.induce H θ.toClassFunction ∈ hyp.S := by
      rw [hyp.S_eq]; exact ⟨θ, hne, rfl⟩
    have hχnotSZ : ClassFunction.induce H θ.toClassFunction ∉ hyp.SsubFiltration W2 := by
      intro hmem
      rw [hyp.mem_SsubFiltration] at hmem
      obtain ⟨θ', hne', hker', heq'⟩ := hmem
      exact hχnotZ (Finset.mem_image.mpr
        ⟨θ', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hker', hne'⟩, heq'.symm⟩)
    exact hXsub (hyp.mem_Xset.mpr ⟨hχS, hχnotSZ⟩)
  rw [← hXsum]
  calc ∑ χ ∈ Xdiff, ((χ 1).re) ^ 2 / (ClassFunction.inner χ χ).re
      ≤ ∑ χ ∈ (Set.range χmem).toFinset, ((χ 1).re) ^ 2 / (ClassFunction.inner χ χ).re :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun χ _ _ => div_nonneg (sq_nonneg _) (inner_self_re_nonneg χ))
    _ = ∑ j : Fin k, ((χmem j 1).re) ^ 2 / (ClassFunction.inner (χmem j) (χmem j)).re :=
        sum_toFinset_range_eq hinj (fun χ => ((χ 1).re) ^ 2 / (ClassFunction.inner χ χ).re)
    _ = ∑ j : Fin k, ((χmem j 1).re) ^ 2 / mc j := by
        refine Finset.sum_congr rfl (fun j _ => ?_); rw [hmcnorm j, Complex.ofReal_re]
    _ ≤ 2 * (OddOrder.Peterfalvi.S06.columnSum h46 χ₂b 1).re * (η 1).re := hfambound

/-- **Peterfalvi (6.8.2) case-(B): `S` has no real characters.**

Every `S`-member `Ind^L_H θ` (`θ ≠ 1`) is non-real: by `caseB_induce_column_or_irreducible` it is a
nontrivial certain-type column (non-real, since its conjugate is the *inverse* column
`columnSum χ₂⁻¹ ≠ columnSum χ₂` by the Gram matrix) or an irreducible (non-real by the odd order of
`L`, `caseB_irr_nonreal`).  This is the `S`-level form of `Xset_hasNoRealCharacters_caseB` — the
`HasNoRealCharacters Sb` hypothesis the break-pair extractor `exists_coherentBreakPair_general`
requires with `Sb = S`. -/
theorem S_hasNoRealCharacters_caseB
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Finite ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)] :
    OddOrder.Peterfalvi.S03.HasNoRealCharacters hyp.S := by
  have : Fintype ↥(h46.W1 ⊔ h46.W2) := Fintype.ofFinite _
  classical
  intro χ hχS
  rw [hyp.S_eq, Set.mem_ofPred_eq] at hχS
  obtain ⟨θ, hθne, rfl⟩ := hχS
  have hθne' : (θ : ClassFunction ↥H ℂ) ≠ trivialClassFunction ↥H := fun heq =>
    hθne (Subtype.ext (heq.trans (IrreducibleCharacter.coe_trivialIrreducibleCharacter).symm))
  rcases caseB_induce_column_or_irreducible h46 hHK hθne' with ⟨χ₂, hχ₂, hcol⟩ | hirr
  · -- column branch: distinct from its inverse column by the Gram matrix.
    intro hreal
    rw [ClassFunction.IsReal, ← hcol, OddOrder.Peterfalvi.S06.columnSum_conj_eq] at hreal
    have hgram_self := OddOrder.Peterfalvi.S06.columnFamily_mu_sum_inner h46 χ₂ χ₂
    have hgram_cross := OddOrder.Peterfalvi.S06.columnFamily_mu_sum_inner h46 χ₂ χ₂⁻¹
    rw [if_pos rfl] at hgram_self
    rw [if_neg (OddOrder.Peterfalvi.S06.column_inv_ne_self h46 hχ₂).symm] at hgram_cross
    simp only [← OddOrder.Peterfalvi.S06.columnSum_def] at hgram_self hgram_cross
    rw [hreal] at hgram_cross
    have hcontra : (Nat.card h46.W1 : ℂ) = 0 := hgram_self.symm.trans hgram_cross
    exact (NeZero.ne (Nat.card h46.W1)) (by exact_mod_cast hcontra)
  · -- irreducible branch: non-real by odd order.
    exact caseB_irr_nonreal hyp hirr

/-- **Peterfalvi (6.8.3) case-(B) extension: non-coherence of `S` is impossible.**

If `X(W₂) ∪ Y` (case (B), `W₂ ≤ Z(H) ∩ H′` central) is coherent but `S` is **not**, a contradiction
follows.  The break pair `{ψ, ψ̄}` (`exists_coherentBreakPair_general`, valid for the reducible
case-(B) `S` via `S_hasNoRealCharacters_caseB`) gives a coherent `S₁ ⊇ X(W₂) ∪ Y` whose extension by
`{ψ, ψ̄}` fails.  The break character `ψ` is **irreducible**: a reducible certain-type column would
lie in `X(W₂) ⊆ S₁` (`columnSum_mem_S` + `columnSum_notMem_SsubFiltration`), contradicting
`ψ ∉ S₁`.  The norm-weighted (5.6) bound `xSum_le_two_psi_caseB` then forces
`|W₁|·|H:W₂|·(|W₂|−1) = ∑_X χ(1)²/‖χ‖² ≤ 2ψ(1)·η(1) = 2|W₁|²·d` with `d = θ(1)`, `ψ = Ind θ`.
Combined with Cor 2.30 `d² ≤ |H:W₂|` (central `W₂`, `degree_sq_le_index_of_central_quotient`) and
the case-(B) fixed-point-free bound `(2|W₁|+1)² ≤ |H:W₂|` (`hfpf`, from `caseB_fpf_bound`), the
arithmetic core `false_of_w2_break_arith` yields a contradiction.  This is the case-(B) (6.8.3)
heart; the FPF bound and central-`W₂` data are supplied as hypotheses (from the `(6.4)`/`(6.5)`
case-(B) structure at the `S08_CoherenceTheorems` dispatch). -/
theorem false_of_coherentXunionYset_caseB_of_not_coherentS
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Finite ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Finite (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    [h46.W2.Normal]
    (hW2cen : h46.W2.subgroupOf H ≤ Subgroup.center ↥H)
    (hcZ : 2 ≤ Nat.card ↥(h46.W2.subgroupOf H))
    (hfpf : (2 * Nat.card hyp.W1 + 1) ^ 2 ≤ Nat.card (↥H ⧸ h46.W2.subgroupOf H))
    (hXYcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (hyp.Xset h46.W2 ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)))
    (hncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.S
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) : False := by
  have : Fintype ↥(h46.W1 ⊔ h46.W2) := Fintype.ofFinite _
  have : Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W := Fintype.ofFinite _
  classical
  -- break pair on `Sa = X(h46.W2) ∪ Y`, `Sb = S`.
  have hSaSb : hyp.Xset h46.W2 ∪ hyp.Yset ⊆ hyp.S := by
    rintro φ (hX | hY)
    · exact hyp.Xset_subset_S hX
    · exact hyp.Yset_subset_S hY
  have hSaconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.Xset h46.W2 ∪ hyp.Yset) := by
    intro φ hφ
    rcases hφ with hX | hY
    · exact Or.inl (hyp.Xset_closedUnderConjugate_unconditional h46.W2 hX)
    · exact Or.inr (hyp.Yset_closedUnderConjugate hY)
  obtain ⟨S₁, ψ, hS₁conj, hSaS₁, hS₁Sb, hψSb, hψnS₁, hψcnS₁, hS₁cohN, hncN⟩ :=
    exists_coherentBreakPair_general hyp.tau hSaSb hyp.S_finite hyp.S_closedUnderConjugate
      (S_hasNoRealCharacters_caseB hyp h46 hHK) hSaconj hXYcoh hncoh
  have hS₁fin : S₁.Finite := hyp.S_finite.subset hS₁Sb
  have hXsub : hyp.Xset h46.W2 ⊆ S₁ := fun φ hφ => hSaS₁ (Or.inl hφ)
  -- anchor `η ∈ Y` of degree `|W₁|`.
  obtain ⟨η, hηY⟩ := hyp.Yset_nonempty
  have hηS₁ : η ∈ S₁ := hSaS₁ (Or.inr hηY)
  have hηdeg : η 1 = (Nat.card hyp.W1 : ℂ) := hyp.Yset_apply_one hηY
  -- `ψ ∈ S` is irreducible: a reducible column would lie in `X(h46.W2) ⊆ S₁`, contra `ψ ∉ S₁`.
  have hψS : ψ ∈ hyp.S := hψSb
  have hψirr : IsIrreducibleCharacter ψ := by
    rcases caseB_S_member_column_or_irreducible hyp h46 hHK hψS with ⟨χ₂, hχ₂, hcol⟩ | hirr
    · exfalso
      apply hψnS₁
      rw [← hcol]
      exact hXsub (hyp.mem_Xset.mpr ⟨hyp.columnSum_mem_S h46 hHK hχ₂,
        hyp.columnSum_notMem_SsubFiltration h46 hHK hχ₂⟩)
    · exact hirr
  rw [hyp.S_eq, Set.mem_ofPred_eq] at hψS
  obtain ⟨θ, hθne, hψeq⟩ := hψS
  obtain ⟨d, hdpos, hθd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
  have hdsq : d ^ 2 ≤ Nat.card (↥H ⧸ h46.W2.subgroupOf H) := by
    obtain ⟨d', hθd', hd'sq⟩ := θ.isIrreducible.exists_degree_sq_le_index
      (h46.W2.subgroupOf H) hW2cen
    have hdd' : d = d' := by
      have hcast : (d : ℂ) = (d' : ℂ) := by rw [← hθd, hθd']
      exact_mod_cast hcast
    rw [hdd', ← Subgroup.index_eq_card]; exact hd'sq
  -- the norm-weighted (5.6) `X`-sum bound.
  have hxb := xSum_le_two_psi_caseB hyp h46 hHK hW1 (W2 := h46.W2) hS₁Sb hS₁conj hS₁fin
    hS₁cohN.some hXsub hηY hηS₁ hψSb hψirr hψnS₁ hψcnS₁ hncN
  have hψre : (ψ 1).re = (H.index : ℝ) * (d : ℝ) := by
    rw [hψeq, ClassFunction.induce_apply_one, hθd]
    simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im]; ring
  have hηre : (η 1).re = (Nat.card hyp.W1 : ℝ) := by rw [hηdeg, Complex.natCast_re]
  rw [hψre, hηre] at hxb
  -- cast the real inequality to ℕ.
  have hZle : Nat.card (↥H ⧸ h46.W2.subgroupOf H) ≤ Nat.card ↥H :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
  have hxbN : H.index * (Nat.card ↥H - Nat.card (↥H ⧸ h46.W2.subgroupOf H))
      ≤ 2 * (H.index * d) * Nat.card hyp.W1 := by
    rw [← Nat.cast_le (α := ℝ)]
    push_cast [Nat.cast_sub hZle]
    nlinarith [hxb]
  rw [hyp.index_mul_card_sub_factor (Z := h46.W2), hyp.index_H_eq_card_W1] at hxbN
  -- discharge the arithmetic core (`false_of_w2_break_arith`).
  refine false_of_w2_break_arith (w1 := Nat.card hyp.W1) (d := d)
    (hZ := Nat.card (↥H ⧸ h46.W2.subgroupOf H)) (cZ := Nat.card ↥(h46.W2.subgroupOf H))
    Nat.card_pos hdpos hdsq hcZ hfpf ?_
  calc Nat.card hyp.W1 * Nat.card (↥H ⧸ h46.W2.subgroupOf H)
          * (Nat.card ↥(h46.W2.subgroupOf H) - 1)
      = Nat.card (↥H ⧸ h46.W2.subgroupOf H)
          * (Nat.card hyp.W1 * (Nat.card ↥(h46.W2.subgroupOf H) - 1)) := by ring
    _ ≤ 2 * (Nat.card hyp.W1 * d) * Nat.card hyp.W1 := hxbN
    _ = 2 * Nat.card hyp.W1 ^ 2 * d := by ring

/-- **(6.8.3) case-(B) coherence producer** (gated-endpoint skeleton).

The producer (positive) form of the case-(B) (6.8.3) contradiction
`false_of_coherentXunionYset_caseB_of_not_coherentS`: given the `X(W₂) ∪ Y` coherence **seed**
`hXYcoh` together with the case-(B) structural data (`W₂` central in `H` (`hW2cen`), `|W₂| ≥ 2`
(`hcZ`), and the fixed-point-free bound `(2|W₁|+1)² ≤ |H:W₂|` (`hfpf`, from `caseB_fpf_bound`)), the
Sibley set `S` is coherent.  The proof is `by_contra` plus the (6.8.3) contradiction.

This is the case-(B) analogue of the case-(A) producer `nonempty_coherent_S_caseA_of_frobenius`,
with one essential difference: case (A) **constructs** its seed inline from the Frobenius data,
whereas the case-(B) seed `hXYcoh` is taken as a hypothesis.  Constructing it
(`coherentXunionYset_caseB_of_glued`) requires the §6 certain-type structure-theory anchoring
`hXanchored`, the residual gate of the `S08_CoherenceTheorems` c2-math-B dispatch — *not* discharged
here.  So this lemma is the sorry-free skeleton that reduces the case-(B) branch of
`sibleySetup_is_coherent` to exactly the seed construction. -/
theorem nonempty_coherent_S_caseB
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Finite ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Finite (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    [h46.W2.Normal]
    (hW2cen : h46.W2.subgroupOf H ≤ Subgroup.center ↥H)
    (hcZ : 2 ≤ Nat.card ↥(h46.W2.subgroupOf H))
    (hfpf : (2 * Nat.card hyp.W1 + 1) ^ 2 ≤ Nat.card (↥H ⧸ h46.W2.subgroupOf H))
    (hXYcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (hyp.Xset h46.W2 ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.S
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)) := by
  by_contra hncoh
  exact false_of_coherentXunionYset_caseB_of_not_coherentS hyp h46 hHK hW1
    hW2cen hcZ hfpf hXYcoh hncoh

end OddOrder.Peterfalvi.S08


