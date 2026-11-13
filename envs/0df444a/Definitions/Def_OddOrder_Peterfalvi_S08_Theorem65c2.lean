-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S08_Theorem65c2
-- name    : OddOrder_Peterfalvi_S08_Theorem65c2
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T07:23:52.147597+00:00
-- url     : https://prove2.me/theorems/93cad428-1c98-4dc3-beba-3dbf8f9aac54
-- title:
--   Peterfalvi (6.2)/(6.3)/(6.5) for case (c2): the certain-type $p$-group reduction chain
-- statement:
--   Peterfalvi, *Character Theory for the Odd Order Theorem*, §6, (6.2)/(6.3)/(6.5). This file assembles the case-(c2) (certain-type) analogue of the Frobenius (c1) chain from the (6.2) index bound to the conclusion that the group is a $p$-group.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 5 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S08_Theorem65c2.lean

/-
Copyright (c) 2026 The Odd Order Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S08_Theorem65c2.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S08_Theorem63
import Definitions.Def_OddOrder_Peterfalvi_S08_CaseBAssembly

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]

variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]

variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

/-- **Peterfalvi (6.2) per-step index bound, case (c2)** (`six_two_index_bound` analogue).

From `S(A)` coherent and `S(B)` not coherent (`S(A) ⊆ S(B)`), there is a break character
`ψ ∈ S(B)` with `|H : A| − 1 ≤ 2·ψ(1)`.  Mirror of the Frobenius `six_two_index_bound`
(`S08_CoherenceCorePart2:3576`) with the three-brick swap:
* break pair from `exists_coherentBreakPair_general` (no all-irreducible requirement);
* `S(B)` real-free from `S_hasNoRealCharacters_caseB`;
* the (6.2) bound from `sSubFiltration_sum_le_two_psi_caseB`, whose `hψirr` is discharged by
  `member_isIrreducible_of_W2_le` (using `W₂ ≤ B`), and whose `Y`-anchor `η ∈ Yset` lies in `S₁`
  because `Y = S(⁅H,H⁆) ⊆ S(A) ⊆ S₁` (using `A ≤ ⁅H,H⁆`).
The bound's `|L:H|·(|H:A|−1) ≤ 2ψ(1)·η(1)` is divided by `η(1) = |W₁| = |L:H|` to the stated
form. -/
theorem six_two_index_bound_c2 (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Finite ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Finite (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {A B : Subgroup ↥L} [A.Normal]
    (hAB : hyp.SsubFiltration A ⊆ hyp.SsubFiltration B)
    (hAcomm2 : A ≤ ⁅H, H⁆)
    (hSAcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration A)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)))
    (hSBncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration B)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    ∃ ψ, ψ ∈ hyp.SsubFiltration B ∧
      (Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1 ≤ 2 * (ψ 1).re := by
  have : Fintype ↥(h46.W1 ⊔ h46.W2) := Fintype.ofFinite _
  have : Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W := Fintype.ofFinite _
  obtain ⟨S₁, ψ, hS₁conj, hAS₁, hS₁B, hψB, hψnotS1, hψcnotS1, hS₁coh, hncoh⟩ :=
    exists_coherentBreakPair_general hyp.tau hAB (hyp.SsubFiltration_finite B)
      (hyp.SsubFiltration_closedUnderConjugate B)
      ((S_hasNoRealCharacters_caseB hyp h46 hHK).mono hyp.SsubFiltration_subset_S)
      (hyp.SsubFiltration_closedUnderConjugate A) hSAcoh hSBncoh
  obtain ⟨η, hηY⟩ := hyp.Yset_nonempty
  have hYsubA : hyp.Yset ⊆ hyp.SsubFiltration A := hyp.SsubFiltration_antitone hAcomm2
  have hηS₁ : η ∈ S₁ := hAS₁ (hYsubA hηY)
  have hψS : ψ ∈ hyp.S := hyp.SsubFiltration_subset_S hψB
  -- (6.2) bound, dispatching on whether the break `ψ` is a reducible column or irreducible.  This
  -- removes the `hW2B : W₂ ≤ B` hypothesis: the minimal-`A` induction (`six_three_c2`) cannot
  -- guarantee `W₂ ≤ B`, so a column-transition break `ψ = μ_b` must be admitted directly.
  have hbound : (H.index : ℝ) * ((Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1)
      ≤ 2 * (ψ 1).re * (η 1).re := by
    rcases caseB_S_member_column_or_irreducible hyp h46 hHK hψS with hcol | hirr
    · obtain ⟨χ₂b, hχ₂b, hcoleq⟩ := hcol
      have h := sSubFiltration_sum_le_two_psi_caseB_columnBreak hyp h46 hHK hW1
        (hS₁B.trans hyp.SsubFiltration_subset_S) hS₁conj
        ((hyp.SsubFiltration_finite B).subset hS₁B) hS₁coh.some hAS₁ hηY hηS₁ hχ₂b
        (by rw [hcoleq]; exact hψnotS1) (by rw [hcoleq]; exact hψcnotS1)
        (by rw [hcoleq]; exact hncoh)
      rwa [hcoleq] at h
    · exact sSubFiltration_sum_le_two_psi_caseB hyp h46 hHK hW1
        (hS₁B.trans hyp.SsubFiltration_subset_S) hS₁conj
        ((hyp.SsubFiltration_finite B).subset hS₁B) hS₁coh.some hAS₁ hηY hηS₁
        hψS hirr hψnotS1 hψcnotS1 hncoh
  have hηre : (η 1).re = (Nat.card hyp.W1 : ℝ) := by
    rw [hyp.Yset_apply_one hηY, Complex.natCast_re]
  have hidx : (H.index : ℝ) = (Nat.card hyp.W1 : ℝ) := by exact_mod_cast hyp.index_H_eq_card_W1
  have hHpos : (0 : ℝ) < (H.index : ℝ) := by rw [hidx]; exact_mod_cast Nat.card_pos
  refine ⟨ψ, hψB, ?_⟩
  rw [hηre, ← hidx] at hbound
  have hX : (H.index : ℝ) * ((Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1)
      ≤ (H.index : ℝ) * (2 * (ψ 1).re) := by
    calc (H.index : ℝ) * ((Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1)
        ≤ 2 * (ψ 1).re * (H.index : ℝ) := hbound
      _ = (H.index : ℝ) * (2 * (ψ 1).re) := by ring
  exact le_of_mul_le_mul_left hX hHpos

/-- **Peterfalvi (6.2), central case `C = H`, case (c2)** (`six_two_central` analogue).
With `B ⊆ D ≤ H` (`B` as `N = B.subgroupOf H`), `D/B` central in `H/B`, `S(A)` coherent, `S(B)` not:
`|H:A| − 1 ≤ 2|L:H|·√|H:D|`.  Mirror of `six_two_central` (`S08_CoherenceCorePart2:3669`), already
Frobenius-free apart from the (6.2) per-step call, which becomes `six_two_index_bound_c2`; the
θ-bound
`psi_degree_le_of_source_central` is unchanged (it consumes only `H_normal`). -/
theorem six_two_central_c2 (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Finite ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Finite (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {A B : Subgroup ↥L} [A.Normal] [B.Normal]
    (hAB : hyp.SsubFiltration A ⊆ hyp.SsubFiltration B)
    (hAcomm2 : A ≤ ⁅H, H⁆)
    (D : Subgroup ↥H) (hND : B.subgroupOf H ≤ D)
    (hcentral : D.map (QuotientGroup.mk' (B.subgroupOf H)) ≤
      Subgroup.center (↥H ⧸ B.subgroupOf H))
    (hSAcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration A)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)))
    (hSBncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration B)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    (Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1 ≤ 2 * (H.index : ℝ) * Real.sqrt (D.index : ℝ) := by
  have : Fintype ↥(h46.W1 ⊔ h46.W2) := Fintype.ofFinite _
  have : Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W := Fintype.ofFinite _
  obtain ⟨ψ, hψB, hψbound⟩ :=
    six_two_index_bound_c2 hyp h46 hHK hW1 hAB hAcomm2 hSAcoh hSBncoh
  rw [hyp.mem_SsubFiltration] at hψB
  obtain ⟨θ, _hθne, hθkerB, hψeq⟩ := hψB
  have hψdeg := hyp.psi_degree_le_of_source_central θ D hND hθkerB hcentral
  rw [hψeq] at hψbound
  calc (Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1
      ≤ 2 * (ClassFunction.induce H (θ : ClassFunction ↥H ℂ) 1).re := hψbound
    _ ≤ 2 * ((H.index : ℝ) * Real.sqrt (D.index : ℝ)) := by linarith [hψdeg]
    _ = 2 * (H.index : ℝ) * Real.sqrt (D.index : ℝ) := by ring

/-- **Peterfalvi (6.3) per-step index bound, case (c2)** (`six_three_index_bound` analogue).
For a section `B ⊆ A ⊆ H₁` with `A/B` central in `H/B`, `S(A)` coherent and `S(B)` not, the (6.2)
central bound combines with the arithmetic core `six_three_HH1_le` to give
`|H:H₁| ≤ 4|L:K|² + 1` (`K = H`).  Mirror of `six_three_index_bound`
(`S08_CoherenceCorePart2:3699`); only the (6.2) call becomes `six_two_central_c2`. -/
theorem six_three_index_bound_c2 (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Finite ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Finite (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {A B H₁ : Subgroup ↥L} [A.Normal] [B.Normal] (hBA : B ≤ A) (hAH₁ : A ≤ H₁)
    (hAcomm2 : A ≤ ⁅H, H⁆)
    (hcentral : (A.subgroupOf H).map (QuotientGroup.mk' (B.subgroupOf H)) ≤
      Subgroup.center (↥H ⧸ B.subgroupOf H))
    (hSAcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration A)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)))
    (hSBncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration B)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    Nat.card (↥H ⧸ H₁.subgroupOf H) ≤ 4 * H.index ^ 2 + 1 := by
  have : Fintype ↥(h46.W1 ⊔ h46.W2) := Fintype.ofFinite _
  have : Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W := Fintype.ofFinite _
  have hsixtwo := six_two_central_c2 hyp h46 hHK hW1 (hyp.SsubFiltration_antitone hBA)
    hAcomm2 (A.subgroupOf H) (Subgroup.subgroupOf_mono H hBA) hcentral hSAcoh hSBncoh
  have hHH1le : Nat.card (↥H ⧸ H₁.subgroupOf H) ≤ Nat.card (↥H ⧸ A.subgroupOf H) :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_of_le (Subgroup.subgroupOf_mono H hAH₁))
  refine six_three_HH1_le (LK := H.index) (KH := 1) (HA := Nat.card (↥H ⧸ A.subgroupOf H))
    (HH1 := Nat.card (↥H ⧸ H₁.subgroupOf H)) (by norm_num) hHH1le ?_
  simpa [Subgroup.index_eq_card] using hsixtwo

/-- **Peterfalvi (6.3), case (c2)** (`six_three` analogue, `hW2B`-free).  The minimal-`A` induction:
for `M ≤ H₁ ≤ ⁅H,H⁆` with `S(H₁)` coherent and `4|L:K|²+1 < |H:H₁|`, `S(M)` is coherent.  Mirror of
`six_three` (`S08_CoherenceCorePart2:3750`); `hF` becomes the certain-type `(h46, hHK, hW1)`, and
the
per-step `(6.3)` index bound is `six_three_index_bound_c2`.  The break admitted by that bound need
no
longer be irreducible — the `column/irreducible` dispatch in `six_two_index_bound_c2` removed the
`W₂ ≤ B` requirement, so the induction may descend below `W₂` (where column-transition breaks
occur).
The `A ≤ ⁅H,H⁆` input of `six_three_index_bound_c2` holds since `A ≤ H₁ ≤ ⁅H,H⁆`. -/
theorem six_three_c2 (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Finite ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Finite (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {M H₁ : Subgroup ↥L} [M.Normal] [H₁.Normal] (hMH₁ : M ≤ H₁) (hH₁comm : H₁ ≤ ⁅H, H⁆)
    (hcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration H₁)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)))
    (hbound : 4 * H.index ^ 2 + 1 < Nat.card (↥H ⧸ H₁.subgroupOf H)) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration M)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)) := by
  classical
  have : Fintype ↥(h46.W1 ⊔ h46.W2) := Fintype.ofFinite _
  have : Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W := Fintype.ofFinite _
  let : H.Normal := hyp.H_normal
  let : Group.IsNilpotent ↥H := hyp.H_nilpotent
  have : Finite (Subgroup ↥L) := Finite.of_injective (fun K : Subgroup ↥L => (K : Set ↥L))
    (fun _ _ h => SetLike.coe_injective h)
  set s : Set (Subgroup ↥L) := {A | A.Normal ∧ M ≤ A ∧ A ≤ H₁ ∧
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration A)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))} with hs_def
  have hH₁s : H₁ ∈ s := by
    simp only [hs_def, Set.mem_ofPred_eq]; exact ⟨‹H₁.Normal›, hMH₁, le_refl _, hcoh⟩
  obtain ⟨A, hAmem, hAmin⟩ :=
    Set.Finite.exists_minimalFor (id : Subgroup ↥L → Subgroup ↥L) s (Set.toFinite _) ⟨H₁, hH₁s⟩
  simp only [hs_def, Set.mem_ofPred_eq] at hAmem
  obtain ⟨hAnorm, hMA, hAH₁, hAcoh⟩ := hAmem
  have : A.Normal := hAnorm
  have hAeqM : A = M := by
    by_contra hne
    have hMltA : M < A := lt_of_le_of_ne hMA (Ne.symm hne)
    obtain ⟨B, hBnorm, hMB, hBltA, hBmaxl⟩ := exists_maximal_normal_between hMltA
    have : B.Normal := hBnorm
    have hAcomm2 : A ≤ ⁅H, H⁆ := hAH₁.trans hH₁comm
    have hAleH : A ≤ H := hAcomm2.trans (Subgroup.commutator_le_left H H)
    have hcentral := normal_central_of_maximal_normal_below (H := H) (A := A) (B := B)
      ‹H.Normal› hAleH hBltA hBmaxl
    have hSBncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration B)
        (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)) := by
      intro hBcoh
      have hBs : B ∈ s := by
        simp only [hs_def, Set.mem_ofPred_eq]
        exact ⟨hBnorm, hMB, hBltA.le.trans hAH₁, hBcoh⟩
      exact lt_irrefl _ (hBltA.trans_le (hAmin hBs hBltA.le))
    have hbnd := six_three_index_bound_c2 hyp h46 hHK hW1 hBltA.le hAH₁ hAcomm2 hcentral hAcoh
      hSBncoh
    omega
  rw [← hAeqM]
  exact hAcoh

/-- **Peterfalvi (6.3) consequence, case (c2): the abelianization bound from non-coherence.**  The
`hbound : |Abelianization H| ≤ 4|W₁|²+1` of the (6.5)/(6.8) reduction, certain-type case.  Mirror of
the index-bound part of `isPGroup_of_not_coherent` (`S08_CoherenceCorePart2:3818-3830`): apply
`six_three_c2` with `M = ⊥`, `H₁ = ⁅H,H⁆` (so `S(⊥) = S` would be coherent if
`|H:⁅H,H⁆| > 4|L:H|²+1`,
contradicting `hSncoh`); `S(⁅H,H⁆) = Y` is coherent (`coherentYset`).  Feeds the c2 `p`-group
reduction `exists_isPGroup_H_of_c2_of_card_le`. -/
theorem abelianization_card_le_of_not_coherent_c2 (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Finite ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Finite (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    (hSncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.S
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    Nat.card (Abelianization ↥H) ≤ 4 * Nat.card hyp.W1 ^ 2 + 1 := by
  have : Fintype ↥(h46.W1 ⊔ h46.W2) := Fintype.ofFinite _
  have : Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W := Fintype.ofFinite _
  let : H.Normal := hyp.H_normal
  let : Group.IsNilpotent ↥H := hyp.H_nilpotent
  have : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hyp.H_ne_bot
  have hcommlt : (⁅H, H⁆ : Subgroup ↥L) < H := by
    have h1 : _root_.commutator ↥H < ⊤ := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥H
    rw [← commutator_subgroupOf_self] at h1
    refine lt_of_le_of_ne (Subgroup.commutator_le_left H H) (fun heq => ?_)
    rw [heq, Subgroup.subgroupOf_self] at h1
    exact lt_irrefl _ h1
  have hidx : Nat.card (↥H ⧸ (⁅H, H⁆ : Subgroup ↥L).subgroupOf H) ≤ 4 * H.index ^ 2 + 1 := by
    by_contra hgt
    rw [not_le] at hgt
    have hYcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration ⁅H, H⁆)
        (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)) := ⟨hyp.coherentYset⟩
    have hMcoh := six_three_c2 hyp h46 hHK hW1 (M := ⊥) (H₁ := ⁅H, H⁆) bot_le le_rfl hYcoh hgt
    rw [hyp.SsubFiltration_bot] at hMcoh
    exact hSncoh hMcoh
  rw [commutator_subgroupOf_self, hyp.index_H_eq_card_W1] at hidx
  exact hidx

end OddOrder.Peterfalvi.S08


