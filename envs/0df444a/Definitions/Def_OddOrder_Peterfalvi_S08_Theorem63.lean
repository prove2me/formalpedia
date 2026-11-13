-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S08_Theorem63
-- name    : OddOrder_Peterfalvi_S08_Theorem63
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T07:22:15.548045+00:00
-- url     : https://prove2.me/theorems/6cb7ced7-23b3-4230-82a6-c4c5b4dab44e
-- title:
--   Peterfalvi (6.2)/(6.3): coherence-break degree bound and the $\le 4|L:K|^2+1$ index bound
-- statement:
--   Peterfalvi, *Character Theory for the Odd Order Theorem*, §6, (6.2)/(6.3). These two theorems are the gate for the (6.5)(b) $p$-group reduction: the contrapositive of Theorem (6.3), where $\neg$coherent $S$, $H$ nilpotent and $S([H,H])=Y$ coherent give a bound on $|H:[H,H]|$.
--
--   Results: `sum_re_div_normSq_SsubFiltration_eq` (the (6.2) degree-square sum over a filtration set $S(A)$), `sSubFiltration_sum_le_two_psi_caseB` (the (6.2) $S(A)$-sum bound in case (c2)) and its reducible-column-break form.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S08_Theorem63.lean

/-
Copyright (c) 2026 The Odd Order Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S08_Theorem63.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S08_CaseBWeightedEndgame

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]

variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]

variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

open scoped Classical in
/-- **(6.2) degree-square sum over a filtration set `S(A)`.**

The norm-weighted degree-square sum over `S(A) = {Ind_H^L θ | A ⊆ Ker θ, θ ≠ 1}` is
`|L:H|·(|H : A| − 1)` (Peterfalvi (6.2) proof, mmd 04.8 L13-17: `∑_{χ∈S(A)} χ(1)²/‖χ‖² =
|L:K|(|K:A| − 1)`, with `K = H` the kernel).  Single-filter form of `sum_re_div_normSq_Xset_eq`:
the complex orbit-count identity `sum_div_normSq_induce_kernelFilter_eq` followed by the per-summand
real conversion `χ(1)²/⟨χ,χ⟩ = (χ(1).re²/⟨χ,χ⟩.re : ℂ)` (`χ(1)` a real degree, `⟨χ,χ⟩` real). -/
theorem sum_re_div_normSq_SsubFiltration_eq (hyp : SibleyDadeHypothesis G L H)
    {A : Subgroup ↥L} [A.Normal] :
    ∑ χ ∈ (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑(A.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧
              θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction),
        ((χ 1).re) ^ 2 / (ClassFunction.inner χ χ).re
      = (H.index : ℝ) * ((Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1) := by
  let : H.Normal := hyp.H_normal
  -- the complex weighted `S(A)` identity.
  have hcomplex := @sum_div_normSq_induce_kernelFilter_eq ↥L _ _ _ H _ _ A _
  -- per-summand real conversion `χ(1)²/⟨χ,χ⟩ = (χ(1).re²/⟨χ,χ⟩.re : ℂ)`.
  have hconv : ∀ χ ∈ (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
          (↑(A.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
              (θ : ClassFunction ↥H ℂ) ∧
            θ ≠ trivialIrreducibleCharacter ↥H)).image
        (fun θ => ClassFunction.induce H θ.toClassFunction),
      χ 1 ^ 2 / ClassFunction.inner χ χ
        = (((χ 1).re ^ 2 / (ClassFunction.inner χ χ).re : ℝ) : ℂ) := by
    intro χ hχ
    obtain ⟨θ, -, rfl⟩ := Finset.mem_image.mp hχ
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
  have key : (((∑ χ ∈ (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
              (↑(A.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                  (θ : ClassFunction ↥H ℂ) ∧
                θ ≠ trivialIrreducibleCharacter ↥H)).image
            (fun θ => ClassFunction.induce H θ.toClassFunction),
          ((χ 1).re) ^ 2 / (ClassFunction.inner χ χ).re : ℝ)) : ℂ)
      = (((H.index : ℝ) * ((Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1)) : ℝ) := by
    rw [Complex.ofReal_sum, Finset.sum_congr rfl (fun χ hχ => (hconv χ hχ).symm), hcomplex]
    push_cast; ring
  exact Complex.ofReal_inj.mp key

open scoped Classical in
/-- **(6.2) `S(A)`-sum bound, case (c2).**  The norm-weighted Peterfalvi (5.6) inequality for a
filtration set: if `S₁` (coherent, `S(A) ⊆ S₁ ⊆ S`) cannot be extended by the break pair
`{ψ, ψ̄}`, then the degree-square count over `S(A)` is bounded:
`|L:K|·(|K:A| − 1) ≤ 2·ψ(1).re·η(1).re` for the degree-`|L:K|` anchor `η ∈ Yset ∩ S₁`.

This is the filtration analogue of `xSum_le_two_psi_caseB`: the brick-3 family bound
`sMember_degreeSqNormReBound_of_not_coherent` (case (c2), `h46`-supplied) bounds the enumerated
`S₁`-family sum, into which the `S(A)` degree-square identity `sum_re_div_normSq_SsubFiltration_eq`
injects `∑_{χ∈S(A)} χ(1)²/‖χ‖²` (`S(A) ⊆ S₁`, nonnegative weighted summands). -/
theorem sSubFiltration_sum_le_two_psi_caseB
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Finite ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Finite (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {A : Subgroup ↥L} [A.Normal]
    {S₁ : Set (ClassFunction ↥L ℂ)} (hS₁sub : S₁ ⊆ hyp.S)
    (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁) (hS₁fin : S₁.Finite)
    (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (hSAsub : hyp.SsubFiltration A ⊆ S₁)
    {η : ClassFunction ↥L ℂ} (hηY : η ∈ hyp.Yset) (hηS₁ : η ∈ S₁)
    {ψ : ClassFunction ↥L ℂ} (hψS : ψ ∈ hyp.S) (hψirr : IsIrreducibleCharacter ψ)
    (hψnotS1 : ψ ∉ S₁) (hψcnotS1 : ψ.conj ∉ S₁)
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (S₁ ∪ {ψ, ψ.conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    (H.index : ℝ) * ((Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1)
      ≤ 2 * (ψ 1).re * (η 1).re := by
  classical
  have : Fintype ↥(h46.W1 ⊔ h46.W2) := Fintype.ofFinite _
  have : Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W := Fintype.ofFinite _
  obtain ⟨k, χmem, mc, hinj, hrange, hmemS1, hmcpos, hmcnorm, hfambound⟩ :=
    sMember_degreeSqNormReBound_of_not_coherent hyp h46 hHK hW1 hS₁sub hS₁conj hS₁fin hS₁coh hηY
      hηS₁ hψS hψirr hψnotS1 hψcnotS1 hnc
  have hSAsum := sum_re_div_normSq_SsubFiltration_eq hyp (A := A)
  set SAfilt := (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
          (↑(A.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
              (θ : ClassFunction ↥H ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) with hSAdef
  have hsub : SAfilt ⊆ (Set.range χmem).toFinset := by
    intro χ hχ
    rw [Set.mem_toFinset, hrange]
    rw [hSAdef] at hχ
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hχ
    obtain ⟨-, hker, hne⟩ := Finset.mem_filter.mp hθ
    exact hSAsub (hyp.mem_SsubFiltration.mpr ⟨θ, hne, hker, rfl⟩)
  rw [← hSAsum]
  calc ∑ χ ∈ SAfilt, ((χ 1).re) ^ 2 / (ClassFunction.inner χ χ).re
      ≤ ∑ χ ∈ (Set.range χmem).toFinset, ((χ 1).re) ^ 2 / (ClassFunction.inner χ χ).re :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun χ _ _ => div_nonneg (sq_nonneg _) (inner_self_re_nonneg χ))
    _ = ∑ j : Fin k, ((χmem j 1).re) ^ 2 / (ClassFunction.inner (χmem j) (χmem j)).re :=
        sum_toFinset_range_eq hinj (fun χ => ((χ 1).re) ^ 2 / (ClassFunction.inner χ χ).re)
    _ = ∑ j : Fin k, ((χmem j 1).re) ^ 2 / mc j := by
        refine Finset.sum_congr rfl (fun j _ => ?_); rw [hmcnorm j, Complex.ofReal_re]
    _ ≤ 2 * (ψ 1).re * (η 1).re := hfambound

open scoped Classical in
/-- **(6.2) `S(A)`-sum bound, case (c2), reducible COLUMN break.**  The column-break analogue of
`sSubFiltration_sum_le_two_psi_caseB`: the break `ψ` adjoined to discharge non-coherence is a
reducible certain-type column `μ_b = columnSum χ₂b`.  Same `(6.2)` conclusion
`|L:K|·(|H/A|−1) ≤ 2·μ_b(1)·η(1)`, via the column member-family bound
`sMember_degreeSqNormReBound_of_not_coherent_columnBreak` and the same `S(A)`-degree-sum
identity. -/
theorem sSubFiltration_sum_le_two_psi_caseB_columnBreak
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Finite (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {A : Subgroup ↥L} [A.Normal]
    {S₁ : Set (ClassFunction ↥L ℂ)} (hS₁sub : S₁ ⊆ hyp.S)
    (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁) (hS₁fin : S₁.Finite)
    (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (hSAsub : hyp.SsubFiltration A ⊆ S₁)
    {η : ClassFunction ↥L ℂ} (hηY : η ∈ hyp.Yset) (hηS₁ : η ∈ S₁)
    {χ₂b : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ} (hχ₂b : χ₂b ≠ 1)
    (hψnotS1 : OddOrder.Peterfalvi.S06.columnSum h46 χ₂b ∉ S₁)
    (hψcnotS1 : (OddOrder.Peterfalvi.S06.columnSum h46 χ₂b).conj ∉ S₁)
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (S₁ ∪ {OddOrder.Peterfalvi.S06.columnSum h46 χ₂b,
        (OddOrder.Peterfalvi.S06.columnSum h46 χ₂b).conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    (H.index : ℝ) * ((Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1)
      ≤ 2 * (OddOrder.Peterfalvi.S06.columnSum h46 χ₂b 1).re * (η 1).re := by
  classical
  have : Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W := Fintype.ofFinite _
  obtain ⟨k, χmem, mc, hinj, hrange, hmemS1, hmcpos, hmcnorm, hfambound⟩ :=
    sMember_degreeSqNormReBound_of_not_coherent_columnBreak hyp h46 hHK hW1 hS₁sub hS₁conj hS₁fin
      hS₁coh hηY hηS₁ hχ₂b hψnotS1 hψcnotS1 hnc
  have hSAsum := sum_re_div_normSq_SsubFiltration_eq hyp (A := A)
  set SAfilt := (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
          (↑(A.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
              (θ : ClassFunction ↥H ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) with hSAdef
  have hsub : SAfilt ⊆ (Set.range χmem).toFinset := by
    intro χ hχ
    rw [Set.mem_toFinset, hrange]
    rw [hSAdef] at hχ
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hχ
    obtain ⟨-, hker, hne⟩ := Finset.mem_filter.mp hθ
    exact hSAsub (hyp.mem_SsubFiltration.mpr ⟨θ, hne, hker, rfl⟩)
  rw [← hSAsum]
  calc ∑ χ ∈ SAfilt, ((χ 1).re) ^ 2 / (ClassFunction.inner χ χ).re
      ≤ ∑ χ ∈ (Set.range χmem).toFinset, ((χ 1).re) ^ 2 / (ClassFunction.inner χ χ).re :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun χ _ _ => div_nonneg (sq_nonneg _) (inner_self_re_nonneg χ))
    _ = ∑ j : Fin k, ((χmem j 1).re) ^ 2 / (ClassFunction.inner (χmem j) (χmem j)).re :=
        sum_toFinset_range_eq hinj (fun χ => ((χ 1).re) ^ 2 / (ClassFunction.inner χ χ).re)
    _ = ∑ j : Fin k, ((χmem j 1).re) ^ 2 / mc j := by
        refine Finset.sum_congr rfl (fun j _ => ?_); rw [hmcnorm j, Complex.ofReal_re]
    _ ≤ 2 * (OddOrder.Peterfalvi.S06.columnSum h46 χ₂b 1).re * (η 1).re := hfambound

end OddOrder.Peterfalvi.S08


