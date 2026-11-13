-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S08_CoherenceCorePart2_SibleyBounds
-- name    : OddOrder_Peterfalvi_S08_CoherenceCorePart2_SibleyBounds
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:28:00.738419+00:00
-- url     : https://prove2.me/theorems/95a66136-f276-425e-a1a5-0a4066930bb3
-- title:
--   Peterfalvi §8: Sibley bounds and X-set coherence
-- statement:
--   Sibley arithmetic bounds and the $X$-set coherence construction in Peterfalvi, *Character Theory for the Odd Order Theorem*, §6 and §8, in the setting of the Sibley–Dade coherence argument.
--
--   Key results include `sMember_index_le_two_psi` (the (6.2) core inequality $|K:A|-1\le 2\psi(1)$, Frobenius case), `xSum_le_two_psi` (the (6.8.3) $X$-sum break bound), `Xset_nonempty_of_subgroupOf_ne_bot` (the (6.6) nonemptiness of the $X$-set from a nontrivial trace) and `six_two_index_bound` (the (6.2) first-obstruction and core wiring).
--
--   The bundle also proves 12 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S08_CoherenceCorePart2/SibleyBounds.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S08_CoherenceCorePart2/SibleyBounds.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S08_DegreeSums

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

open scoped commutatorElement

variable {L G : Type*} [Group L] [Group G]

namespace SibleyDadeHypothesis

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]

variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)]

variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

/-- **(6.6) `htotal` factorization.**  `|L:H|·(|H| − |H:Z|) = |H:Z| · (|L:H|·(|Z| − 1))` (Lagrange
`|H| = |H:Z|·|Z|`).  With the X degree-sum `total = |L:H|·(|H| − |H:Z|)` (`sum_re_sq_Xset_eq`), this
is the `total = qtot · c` of the X-chain step data with `qtot = |H:Z|`, `c = |L:H|·(|Z| − 1)`. -/
theorem index_mul_card_sub_factor (_hyp : SibleyDadeHypothesis G L H) {Z : Subgroup ↥L} [Z.Normal] :
    H.index * (Nat.card ↥H - Nat.card (↥H ⧸ Z.subgroupOf H))
      = Nat.card (↥H ⧸ Z.subgroupOf H) * (H.index * (Nat.card ↥(Z.subgroupOf H) - 1)) := by
  have hlag : Nat.card ↥H
      = Nat.card (↥H ⧸ Z.subgroupOf H) * Nat.card ↥(Z.subgroupOf H) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf H)
  have hz : 1 ≤ Nat.card ↥(Z.subgroupOf H) := Nat.card_pos
  obtain ⟨w, hw⟩ : ∃ w, Nat.card ↥(Z.subgroupOf H) = w + 1 := ⟨_, (Nat.sub_add_cancel hz).symm⟩
  rw [hlag, hw]
  simp only [Nat.mul_add, Nat.mul_one, Nat.add_sub_cancel]
  ring

/-- **(6.8.3) arithmetic core.**  The numeric contradiction closing the (6.8.3) extension in case
(A).  From the break-pair (5.6) bound `∑_{χ∈X} χ(1)² < 2ψ(1)η₁(1)` — i.e.
`|W₁|·|H:Z|·(|Z|−1) < 2·|W₁|²·d` with `ψ(1) = |W₁|d`, `η₁(1) = |W₁|` — together with [Is] Cor 2.30
`d² ≤ |H:Z|` (valid since `Z` is central) and the fixed-point-free bound `|Z|−1 ≥ 2|W₁|`
(`W₁` acts FPF on the odd-order `Z`), one derives `|H:Z| < d ≤ d² ≤ |H:Z|`, a contradiction.

Here `w1 = |W₁|`, `d = θ(1)` (the degree of the `H`-source of `ψ`), `hZ = |H:Z|`, `cZ = |Z|`.
The hypothesis `2 ≤ hZ` holds because `Z ⊆ H′ ⊊ H` (`H` non-abelian), so `|H:Z| ≥ |H:H′| ≥ 2`. -/
theorem false_of_centralCommutator_break_arith {w1 d hZ cZ : ℕ}
    (hw1 : 1 ≤ w1) (hd : 1 ≤ d) (hdsq : d ^ 2 ≤ hZ) (hZ2 : 2 ≤ hZ)
    (hfpf : 2 * w1 ≤ cZ - 1)
    (hbreak : w1 * hZ * (cZ - 1) ≤ 2 * w1 ^ 2 * d) : False := by
  set m := cZ - 1 with hm
  have hge : 2 * w1 ^ 2 * hZ ≤ w1 * hZ * m := by
    calc 2 * w1 ^ 2 * hZ = w1 * hZ * (2 * w1) := by ring
      _ ≤ w1 * hZ * m := mul_le_mul_right hfpf (w1 * hZ)
  have hle : 2 * w1 ^ 2 * hZ ≤ 2 * w1 ^ 2 * d := le_trans hge hbreak
  have hZd : hZ ≤ d := Nat.le_of_mul_le_mul_left hle (by positivity)
  have h2d : 2 ≤ d := le_trans hZ2 hZd
  have hdd : 2 * d ≤ d ^ 2 := by nlinarith [h2d]
  omega

open scoped Classical in
/-- **(6.2) core inequality** `|K:A| − 1 ≤ 2ψ(1)` (Frobenius case).

Combines the member-family degree-square bound `sMember_degreeSqReBound_of_not_coherent`
(`∑_{χ∈S₁} χ(1).re² ≤ 2ψ(1).re·χ₁(1).re`) with the real B2 identity
`sum_re_sq_induce_kernelFilter_eq`
(`∑_{χ∈S(A)} χ(1).re² = |L:H|·(|H:A| − 1)`).  Since `S(A) ⊆ S₁`, the `S(A)`-sum is bounded by the
`S₁`-sum, and with `χ₁(1) = |W₁| = |L:H|` (cancelling the positive index `|L:H|`) this gives
`|H:A| − 1 ≤ 2ψ(1)`.  This is the (6.2) bound `2ψ(1) ≥ |K:A| − 1` (with `K = H`); composing with the
θ-bound `ψ(1) ≤ |L:C|√|C:D|` yields the full (6.2) `2|L:C|√|C:D| ≥ |K:A| − 1`. -/
theorem sMember_index_le_two_psi (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1) {A : Subgroup ↥L} [A.Normal]
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁sub : S₁ ⊆ hyp.S) (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁)
    (hS₁fin : S₁.Finite) (hSA_S1 : hyp.SsubFiltration A ⊆ S₁)
    (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁S₁ : χ₁ ∈ S₁)
    (hχ₁deg : χ₁ 1 = (Nat.card hyp.W1 : ℂ))
    {ψ : ClassFunction ↥L ℂ} (hψS : ψ ∈ hyp.S) (hψirr : IsIrreducibleCharacter ψ)
    (hψnotS1 : ψ ∉ S₁) (hψcnotS1 : ψ.conj ∉ S₁)
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (S₁ ∪ {ψ, ψ.conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    (Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1 ≤ 2 * (ψ 1).re := by
  obtain ⟨k, χmem, hχinj, hrange, hmemS1, hfambound⟩ :=
    hyp.sMember_degreeSqReBound_of_not_coherent hF hS₁sub hS₁conj hS₁fin hS₁coh hχ₁S₁ hχ₁deg
      hψS hψirr hψnotS1 hψcnotS1 hnc
  have hcfinj : Function.Injective (fun j => (χmem j : ClassFunction ↥L ℂ)) :=
    fun a b h => hχinj (Subtype.ext h)
  have hB2 := hyp.sum_re_sq_induce_kernelFilter_eq hF (A := A)
  set SA := (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
        (↑(A.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
            (θ : ClassFunction ↥H ℂ) ∧
          θ ≠ trivialIrreducibleCharacter ↥H)).image
        (fun θ => ClassFunction.induce H θ.toClassFunction) with hSAdef
  -- the `S(A)` Finset is contained in the enumerated `S₁`-range Finset
  have hsub : SA ⊆ (Set.range (fun j => (χmem j : ClassFunction ↥L ℂ))).toFinset := by
    intro χ hχ
    rw [Set.mem_toFinset, hrange]
    rw [hSAdef] at hχ
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hχ
    obtain ⟨-, hker, hne⟩ := Finset.mem_filter.mp hθ
    exact hSA_S1 (by rw [hyp.mem_SsubFiltration]; exact ⟨θ, hne, hker, rfl⟩)
  have hchain : (H.index : ℝ) * ((Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1) ≤
      2 * (ψ 1).re * (χ₁ 1).re := by
    rw [← hB2]
    calc ∑ χ ∈ SA, ((χ 1).re) ^ 2
        ≤ ∑ χ ∈ (Set.range (fun j => (χmem j : ClassFunction ↥L ℂ))).toFinset, ((χ 1).re) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
      _ = ∑ j : Fin k, (((χmem j : ClassFunction ↥L ℂ) 1).re) ^ 2 :=
          sum_toFinset_range_eq hcfinj (fun χ => (χ 1).re ^ 2)
      _ ≤ 2 * (ψ 1).re * (χ₁ 1).re := hfambound
  have hχ₁re : (χ₁ 1).re = (H.index : ℝ) := by
    rw [hχ₁deg, Complex.natCast_re, hyp.index_H_eq_card_W1]
  rw [hχ₁re] at hchain
  have hidx_pos : (0 : ℝ) < (H.index : ℝ) := by
    rw [hyp.index_H_eq_card_W1]; exact_mod_cast Nat.card_pos
  have key : (H.index : ℝ) * ((Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1) ≤
      (H.index : ℝ) * (2 * (ψ 1).re) := by
    calc (H.index : ℝ) * ((Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1)
        ≤ 2 * (ψ 1).re * (H.index : ℝ) := hchain
      _ = (H.index : ℝ) * (2 * (ψ 1).re) := by ring
  exact le_of_mul_le_mul_left key hidx_pos

open scoped Classical in
/-- **(6.8.3) X-sum break bound.**  The (5.6)/B1 bound applied to the breaking coherent set
`S₁ ⊇ X`:
`∑_{χ∈X} χ(1)² ≤ 2ψ(1)·χ₁(1)`.  Since `X ⊆ S₁` and `S₁` enumerates as a member family bounded by
`sMember_degreeSqReBound_of_not_coherent`, the `X`-sum `(H.index)·(|H| − |H:Z|)`
(`sum_re_sq_Xset_eq`) is dominated by the full family sum, which the (5.6) break bounds by
`2ψ(1)χ₁(1)`.  This is the `(6.8.3)` inequality with `χ₁ = η₁ ∈ Y` of degree `|W₁|`. -/
theorem xSum_le_two_psi (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1) {Z : Subgroup ↥L} [Z.Normal]
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁sub : S₁ ⊆ hyp.S) (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁)
    (hS₁fin : S₁.Finite) (hXS1 : hyp.Xset Z ⊆ S₁)
    (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁S₁ : χ₁ ∈ S₁)
    (hχ₁deg : χ₁ 1 = (Nat.card hyp.W1 : ℂ))
    {ψ : ClassFunction ↥L ℂ} (hψS : ψ ∈ hyp.S) (hψirr : IsIrreducibleCharacter ψ)
    (hψnotS1 : ψ ∉ S₁) (hψcnotS1 : ψ.conj ∉ S₁)
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (S₁ ∪ {ψ, ψ.conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    (H.index : ℝ) * ((Nat.card ↥H : ℝ) - (Nat.card (↥H ⧸ Z.subgroupOf H) : ℝ))
      ≤ 2 * (ψ 1).re * (χ₁ 1).re := by
  obtain ⟨k, χmem, hχinj, hrange, hmemS1, hfambound⟩ :=
    hyp.sMember_degreeSqReBound_of_not_coherent hF hS₁sub hS₁conj hS₁fin hS₁coh hχ₁S₁ hχ₁deg
      hψS hψirr hψnotS1 hψcnotS1 hnc
  have hcfinj : Function.Injective (fun j => (χmem j : ClassFunction ↥L ℂ)) :=
    fun a b h => hχinj (Subtype.ext h)
  have hXsum := hyp.sum_re_sq_Xset_eq hF (Z := Z)
  set Xdiff := (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
          (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
              (θ : ClassFunction ↥H ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) \
        (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑(Z.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) with hXdiffdef
  have hsub : Xdiff ⊆ (Set.range (fun j => (χmem j : ClassFunction ↥L ℂ))).toFinset := by
    intro χ hχ
    rw [Set.mem_toFinset, hrange]
    rw [hXdiffdef, Finset.mem_sdiff] at hχ
    obtain ⟨hχbot, hχnotZ⟩ := hχ
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hχbot
    obtain ⟨-, -, hne⟩ := Finset.mem_filter.mp hθ
    have hχS : ClassFunction.induce H θ.toClassFunction ∈ hyp.S := by
      rw [hyp.S_eq]; exact ⟨θ, hne, rfl⟩
    have hχnotSZ : ClassFunction.induce H θ.toClassFunction ∉ hyp.SsubFiltration Z := by
      intro hmem
      rw [hyp.mem_SsubFiltration] at hmem
      obtain ⟨θ', hne', hker', heq'⟩ := hmem
      exact hχnotZ (Finset.mem_image.mpr
        ⟨θ', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hker', hne'⟩, heq'.symm⟩)
    exact hXS1 ⟨hχS, hχnotSZ⟩
  rw [← hXsum]
  calc ∑ χ ∈ Xdiff, ((χ 1).re) ^ 2
      ≤ ∑ χ ∈ (Set.range (fun j => (χmem j : ClassFunction ↥L ℂ))).toFinset, ((χ 1).re) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
    _ = ∑ j : Fin k, (((χmem j : ClassFunction ↥L ℂ) 1).re) ^ 2 :=
        sum_toFinset_range_eq hcfinj (fun χ => (χ 1).re ^ 2)
    _ ≤ 2 * (ψ 1).re * (χ₁ 1).re := hfambound

open scoped Classical in
/-- **(6.6) X-set nonemptiness from a nontrivial trace.**  If `Z ⊴ L` and `Z.subgroupOf H ≠ ⊥`,
then `X(Z) = S − S(Z)` is nonempty.  The (6.6) degree-square sum
`∑_{χ∈X(Z)} χ(1).re² = |L:H|·(|H| − |H:Z|)` (`sum_re_sq_Xset_eq`) is strictly positive because
`|H:Z| < |H|` whenever `Z.subgroupOf H` is nontrivial, and a positive sum of squares forces its
index Finset — hence `X(Z)` — to be nonempty.  (Note `Xset` is *antitone* in `Z` (`Xset_mono`), so
`X(Zc)` nonemptiness does **not** follow from `X(⁅H,H⁆)` nonemptiness; this degree-sum route is the
honest argument, and it avoids any Clifford-conjugacy reasoning about `Ind`.) -/
theorem Xset_nonempty_of_subgroupOf_ne_bot (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {Z : Subgroup ↥L} [Z.Normal] (hZbot : Z.subgroupOf H ≠ ⊥) :
    (hyp.Xset Z).Nonempty := by
  have : Fintype ↥H := Fintype.ofFinite _
  have hXsum := hyp.sum_re_sq_Xset_eq hF (Z := Z)
  set Xdiff := (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
          (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
              (θ : ClassFunction ↥H ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) \
        (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑(Z.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) with hXdiffdef
  -- `|H:Z| < |H|`, since `Z.subgroupOf H` is nontrivial
  have hlt : Nat.card (↥H ⧸ Z.subgroupOf H) < Nat.card ↥H := by
    have h2 : 1 < Nat.card ↥(Z.subgroupOf H) := (Z.subgroupOf H).one_lt_card_iff_ne_bot.mpr hZbot
    have hcard : Nat.card ↥H
        = Nat.card (↥H ⧸ Z.subgroupOf H) * Nat.card ↥(Z.subgroupOf H) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf H)
    calc Nat.card (↥H ⧸ Z.subgroupOf H)
        < Nat.card (↥H ⧸ Z.subgroupOf H) * Nat.card ↥(Z.subgroupOf H) :=
          lt_mul_of_one_lt_right Nat.card_pos h2
      _ = Nat.card ↥H := hcard.symm
  -- the degree-square sum is strictly positive
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
/-- **(6.6)/(6.8) X-set nonemptiness, CertainType (case B) form.**  As
`Xset_nonempty_of_subgroupOf_ne_bot` but the strictly-positive degree-square sum is supplied by the
case-B identity `sum_re_sq_Xset_eq_of_irreducible_X` (which needs only `X`-irreducibility, valid in
case B) instead of the Frobenius `sum_re_sq_Xset_eq`. The `hX` hypothesis is the
`X = S − S(Z) ⊆ Irr L`
fact (Peterfalvi (6.8.1) for (c2), discharged by `isIrreducibleCharacter_of_mem_Xset_c2_caseA`). -/
theorem Xset_nonempty_of_subgroupOf_ne_bot_of_irreducible_X (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} [Z.Normal] (hZbot : Z.subgroupOf H ≠ ⊥)
    (hX : ∀ χ ∈ ((Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧
              θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) \
        (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑(Z.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧
              θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction)),
        IsIrreducibleCharacter χ) :
    (hyp.Xset Z).Nonempty := by
  have : Fintype ↥H := Fintype.ofFinite _
  have hXsum := hyp.sum_re_sq_Xset_eq_of_irreducible_X (Z := Z) hX
  set Xdiff := (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
          (↑((⊥ : Subgroup ↥L).subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
              (θ : ClassFunction ↥H ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥H)).image
          (fun θ => ClassFunction.induce H θ.toClassFunction) \
        (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
            (↑(Z.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥H ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥H)).image
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

/-- **(6.6)/(6.8) X-set nonemptiness at the central commutator** (the redesign's `hXne`).
`X(Zc)` with `Zc = Z(H) ∩ H′` is nonempty whenever `H` is non-abelian (`commutator ↥H ≠ ⊥`),
since then `Zc ≠ ⊥` (`centralCommutator_ne_bot`), hence `Zc.subgroupOf H ≠ ⊥` (`Zc ≤ H`). -/
theorem Xset_centralCommutator_nonempty (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥) :
    (hyp.Xset hyp.centralCommutator).Nonempty := by
  have := hyp.centralCommutator_normal
  refine hyp.Xset_nonempty_of_subgroupOf_ne_bot hF ?_
  intro hbot
  apply hyp.centralCommutator_ne_bot hHnonab
  rw [eq_bot_iff]
  intro z hz
  have hzH : z ∈ H := hyp.centralCommutator_le hz
  have hmem : (⟨z, hzH⟩ : ↥H) ∈ hyp.centralCommutator.subgroupOf H :=
    (Subgroup.mem_subgroupOf).mpr hz
  rw [hbot, Subgroup.mem_bot] at hmem
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val hmem

/-- **(6.8.3) extension, case (A): non-coherence of `S` is impossible.**
If `X ∪ Y` (with `X = S − S(Z)`, `Z = Z(H)∩H′` central) is coherent but `S` is not, the
break-pair `{ψ, ψ̄}` (`exists_coherentBreakPair`) gives a coherent `S₁ ⊇ X∪Y` whose extension by
`{ψ,ψ̄}` fails; the (5.6)/B1 bound (`xSum_le_two_psi`) then forces
`|W₁|·|H:Z|·(|Z|−1) = ∑_X χ(1)² ≤ 2ψ(1)·η₁(1) = 2|W₁|²d` with `d = θ(1)`, `ψ = Ind θ`.  Combined
with Cor 2.30 `d² ≤ |H:Z|` (central `Z`) and the FPF bound `|Z|−1 ≥ 2|W₁|`
(`centralCommutator_card_subgroupOf_lower`), the arithmetic core
`false_of_centralCommutator_break_arith` yields a contradiction.  This is the heart of
Peterfalvi (6.8.3) — the step the old `Xset ⁅H,H⁆ ∪ Yset = S` shortcut elided. -/
theorem false_of_coherentXunionYset_of_not_coherentS (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    (hXYcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (hyp.Xset hyp.centralCommutator ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)))
    (hncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.S
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) : False := by
  classical
  have : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hyp.H_ne_bot
  let : Group.IsNilpotent ↥H := hyp.H_nilpotent
  have hcommlt : (⁅H, H⁆ : Subgroup ↥L) < H := by
    have h1 : _root_.commutator ↥H < ⊤ := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥H
    rw [← commutator_subgroupOf_self] at h1
    refine lt_of_le_of_ne (Subgroup.commutator_le_left H H) (fun heq => ?_)
    rw [heq, Subgroup.subgroupOf_self] at h1
    exact lt_irrefl _ h1
  -- break pair on `Sa = X ∪ Y`, `Sb = S`
  have hSaSb : hyp.Xset hyp.centralCommutator ∪ hyp.Yset ⊆ hyp.S := by
    rintro φ (hX | hY)
    · exact hyp.Xset_subset_S hX
    · exact hyp.Yset_subset_S hY
  have hSaconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate
      (hyp.Xset hyp.centralCommutator ∪ hyp.Yset) := by
    intro φ hφ
    rcases hφ with hX | hY
    · exact Or.inl (hyp.Xset_closedUnderConjugate_unconditional hyp.centralCommutator hX)
    · exact Or.inr (hyp.SsubFiltration_closedUnderConjugate ⁅H, H⁆ hY)
  obtain ⟨S₁, ψ, hS₁conj, hSaS₁, hS₁Sb, hψSb, hψnS₁, hψcnS₁, hS₁cohN, hncN⟩ :=
    exists_coherentBreakPair hyp.tau hSaSb hyp.S_finite hyp.S_closedUnderConjugate
      (hyp.S_hasNoRealCharacters hF)
      (fun χ hχ => hyp.isIrreducibleCharacter_of_mem_S_of_frobenius hF hχ)
      hSaconj hXYcoh hncoh
  -- anchor `η ∈ Y` of degree `|W₁|`
  obtain ⟨η, hηY⟩ := hyp.Yset_nonempty
  have hηS₁ : η ∈ S₁ := hSaS₁ (Or.inr hηY)
  have hηdeg : η 1 = (Nat.card hyp.W1 : ℂ) := by
    obtain ⟨χ, -, rfl⟩ := hyp.exists_linear_source_of_mem_Yset hηY
    exact hyp.induce_apply_one_eq_card_W1_of_degree_one _
      (OddOrder.RepresentationTheory.linearIrreducibleCharacter_apply_one χ)
  -- `ψ ∈ S` irreducible, `ψ = Ind θ`
  have hψS : ψ ∈ hyp.S := hψSb
  have hψirr : IsIrreducibleCharacter ψ := hyp.isIrreducibleCharacter_of_mem_S_of_frobenius hF hψS
  rw [hyp.S_eq, Set.mem_ofPred_eq] at hψS
  obtain ⟨θ, hθne, hψeq⟩ := hψS
  obtain ⟨d, hdpos, hθd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
  have hdsq : d ^ 2 ≤ Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H) := by
    obtain ⟨d', hθd', hd'sq⟩ := θ.isIrreducible.exists_degree_sq_le_index
      (hyp.centralCommutator.subgroupOf H) hyp.centralCommutator_subgroupOf_le_center
    have hdd' : d = d' := by
      have hcast : (d : ℂ) = (d' : ℂ) := by rw [← hθd, hθd']
      exact_mod_cast hcast
    rw [hdd', ← Subgroup.index_eq_card]; exact hd'sq
  -- the (5.6) X-sum bound
  have hxb := hyp.xSum_le_two_psi hF (Z := hyp.centralCommutator) hS₁Sb hS₁conj
    (hyp.S_finite.subset hS₁Sb) (fun φ hφ => hSaS₁ (Or.inl hφ)) hS₁cohN.some
    hηS₁ hηdeg hψSb hψirr hψnS₁ hψcnS₁ hncN
  have hψre : (ψ 1).re = (H.index : ℝ) * (d : ℝ) := by
    rw [hψeq, ClassFunction.induce_apply_one, hθd]
    simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im]; ring
  have hηre : (η 1).re = (Nat.card hyp.W1 : ℝ) := by rw [hηdeg, Complex.natCast_re]
  rw [hψre, hηre] at hxb
  -- cast the real inequality to ℕ
  have hZle : Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H) ≤ Nat.card ↥H :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
  have hxbN : H.index * (Nat.card ↥H - Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H))
      ≤ 2 * (H.index * d) * Nat.card hyp.W1 := by
    rw [← Nat.cast_le (α := ℝ)]
    push_cast [Nat.cast_sub hZle]
    nlinarith [hxb]
  rw [hyp.index_mul_card_sub_factor (Z := hyp.centralCommutator), hyp.index_H_eq_card_W1] at hxbN
  -- discharge the arithmetic core
  refine false_of_centralCommutator_break_arith (w1 := Nat.card hyp.W1) (d := d)
    (hZ := Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H))
    (cZ := Nat.card ↥(hyp.centralCommutator.subgroupOf H))
    Nat.card_pos hdpos hdsq ?_ ?_ ?_
  · -- `2 ≤ |H:Z|`
    have hZcnotle : ¬ H ≤ hyp.centralCommutator := by
      intro h
      exact (ne_of_lt hcommlt)
        (le_antisymm (Subgroup.commutator_le_left H H)
          (le_trans h hyp.centralCommutator_le_commutator))
    have hne : hyp.centralCommutator.subgroupOf H ≠ ⊤ := fun heq =>
      hZcnotle (Subgroup.subgroupOf_eq_top.mp heq)
    have hcard1 : Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H) ≠ 1 := by
      rw [← Subgroup.index_eq_card]; exact mt Subgroup.index_eq_one.mp hne
    have hcardpos : 0 < Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H) := Nat.card_pos
    omega
  · -- `2|W₁| ≤ |Z| − 1`
    have he := hyp.centralCommutator_card_subgroupOf_lower hF hHnonab
    omega
  · -- the break inequality, reassociated
    calc Nat.card hyp.W1 * Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H)
            * (Nat.card ↥(hyp.centralCommutator.subgroupOf H) - 1)
        = Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H)
            * (Nat.card hyp.W1 * (Nat.card ↥(hyp.centralCommutator.subgroupOf H) - 1)) := by ring
      _ ≤ 2 * (Nat.card hyp.W1 * d) * Nat.card hyp.W1 := hxbN
      _ = 2 * Nat.card hyp.W1 ^ 2 * d := by ring

open scoped Classical in
/-- **(6.2) first-obstruction + core wiring** `|K:A| − 1 ≤ 2ψ(1)`.

From `S(A)` coherent and `S(B)` not coherent (with `S(A) ⊆ S(B)`), the first-obstruction
`exists_coherentBreakPair` produces a breaking pair `{ψ, ψ̄}` with `ψ ∈ S(B)` (`ψ, ψ̄ ∉ S₁`), and
the
(6.2) core `sMember_index_le_two_psi` — with the degree-`|W₁|` anchor `χ₁ ∈ S(A) ⊆ S₁`
(`exists_mem_SsubFiltration_degree_W1`, valid since `H/(A.subgroupOf H)` has a proper commutator
subgroup) — gives `|H:A| − 1 ≤ 2ψ(1)`.  The structural inputs (`S(B)` finite / conjugation-closed /
real-free / irreducible, `S(A)` conjugation-closed) come from the landed `SsubFiltration_*`
helpers. -/
theorem six_two_index_bound (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {A B : Subgroup ↥L} [A.Normal]
    (hAB : hyp.SsubFiltration A ⊆ hyp.SsubFiltration B)
    (hAcomm : _root_.commutator (↥H ⧸ A.subgroupOf H) ≠ ⊤)
    (hSAcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration A)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)))
    (hSBncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration B)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    ∃ ψ, ψ ∈ hyp.SsubFiltration B ∧
      (Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1 ≤ 2 * (ψ 1).re := by
  let : H.Normal := hyp.H_normal
  obtain ⟨S₁, ψ, hS₁conj, hAS₁, hS₁B, hψB, hψnotS1, hψcnotS1, hS₁coh, hncoh⟩ :=
    exists_coherentBreakPair hyp.tau hAB (hyp.SsubFiltration_finite B)
      (hyp.SsubFiltration_closedUnderConjugate B) (hyp.SsubFiltration_hasNoRealCharacters hF B)
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_S_of_frobenius hF
        (hyp.SsubFiltration_subset_S hφ))
      (hyp.SsubFiltration_closedUnderConjugate A) hSAcoh hSBncoh
  obtain ⟨χ₁, hχ₁SA, hχ₁deg⟩ := hyp.exists_mem_SsubFiltration_degree_W1 hAcomm
  have hψS : ψ ∈ hyp.S := hyp.SsubFiltration_subset_S hψB
  exact ⟨ψ, hψB, hyp.sMember_index_le_two_psi hF
    (hS₁B.trans hyp.SsubFiltration_subset_S) hS₁conj
    ((hyp.SsubFiltration_finite B).subset hS₁B) hAS₁ hS₁coh.some
    (hAS₁ hχ₁SA) hχ₁deg hψS (hyp.isIrreducibleCharacter_of_mem_S_of_frobenius hF hψS)
    hψnotS1 hψcnotS1 hncoh⟩

/-- **(6.2) θ-bound for an induced member, central (`C = H`) case.**

When the section is `N ◁ D ≤ H` with `θ` trivial on `N` and `D ⧸ N` central in `H ⧸ N`, the b-half
`degree_sq_le_index_of_central_quotient` gives `θ(1)² ≤ |H:D|` directly (no Clifford restriction),
so `ψ = Ind_H^L θ` has `ψ(1) = |L:H|·θ(1) ≤ |L:H|·√|H:D|`.  This is the form (6.3) consumes (it
applies (6.2) with `C = H`). -/
theorem psi_degree_le_of_source_central (_hyp : SibleyDadeHypothesis G L H)
    (θ : IrreducibleCharacter ↥H) {N : Subgroup ↥H} [N.Normal] (D : Subgroup ↥H) (hND : N ≤ D)
    (hθN : (↑N : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥H ℂ))
    (hcentral : D.map (QuotientGroup.mk' N) ≤ Subgroup.center (↥H ⧸ N)) :
    (ClassFunction.induce H (θ : ClassFunction ↥H ℂ) 1).re ≤
      (H.index : ℝ) * Real.sqrt (D.index : ℝ) := by
  let : H.Normal := _hyp.H_normal
  have : Fintype ↥H := Fintype.ofFinite _
  obtain ⟨d, hd1, hd2⟩ :=
    degree_sq_le_index_of_central_quotient N θ D hND hθN hcentral
  have hind : (ClassFunction.induce H (θ : ClassFunction ↥H ℂ) 1).re
      = (H.index : ℝ) * ((θ : ClassFunction ↥H ℂ) 1).re := by
    rw [ClassFunction.induce_apply_one, Complex.mul_re, Complex.natCast_re, Complex.natCast_im]
    ring
  rw [hind, hd1, Complex.natCast_re]
  exact mul_le_mul_of_nonneg_left (Real.le_sqrt_of_sq_le (by exact_mod_cast hd2))
    (Nat.cast_nonneg _)

/-- **Peterfalvi (6.2), central case `C = H`** (the form consumed by (6.3)).

With the section `B ⊆ D ≤ H` (`B` as `N = B.subgroupOf H`), `D/B` central in `H/B`, `S(A)`
coherent, `S(B)` not: `|K:A| − 1 ≤ 2|L:H|·√|H:D|`.  Specializes `six_two` to `C = H`, where the
θ-bound is the direct b-half (`psi_degree_le_of_source_central`), so the source `θ` of the breaking
pair `ψ ∈ S(B)` is trivial on `N = B.subgroupOf H` (no restriction step needed). -/
theorem six_two_central (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {A B : Subgroup ↥L} [A.Normal] [B.Normal]
    (hAB : hyp.SsubFiltration A ⊆ hyp.SsubFiltration B)
    (hAcomm : _root_.commutator (↥H ⧸ A.subgroupOf H) ≠ ⊤)
    (D : Subgroup ↥H) (hND : B.subgroupOf H ≤ D)
    (hcentral : D.map (QuotientGroup.mk' (B.subgroupOf H)) ≤
      Subgroup.center (↥H ⧸ B.subgroupOf H))
    (hSAcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration A)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)))
    (hSBncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration B)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    (Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1 ≤ 2 * (H.index : ℝ) * Real.sqrt (D.index : ℝ) := by
  let : H.Normal := hyp.H_normal
  obtain ⟨ψ, hψB, hψbound⟩ := hyp.six_two_index_bound hF hAB hAcomm hSAcoh hSBncoh
  rw [hyp.mem_SsubFiltration] at hψB
  obtain ⟨θ, _hθne, hθkerB, hψeq⟩ := hψB
  have hψdeg := hyp.psi_degree_le_of_source_central θ D hND hθkerB hcentral
  rw [hψeq] at hψbound
  calc (Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1
      ≤ 2 * (ClassFunction.induce H (θ : ClassFunction ↥H ℂ) 1).re := hψbound
    _ ≤ 2 * ((H.index : ℝ) * Real.sqrt (D.index : ℝ)) := by linarith [hψdeg]
    _ = 2 * (H.index : ℝ) * Real.sqrt (D.index : ℝ) := by ring

/-- **(6.3) per-step index bound.**

The per-step of Peterfalvi (6.3): for a section `B ⊆ A ⊆ H₁` with `A/B` central in `H/B`, `S(A)`
coherent and `S(B)` not, the (6.2) central bound `six_two_central` (`|H:A| − 1 ≤ 2|L:H|√|H:A|`)
combines with the arithmetic core `six_three_HH1_le` to give `|H:H₁| ≤ 4|L:K|² + 1` (`K = H`).
The minimal-`A` / maximal-`B` induction of (6.3) repeatedly applies this step. -/
theorem six_three_index_bound (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {A B H₁ : Subgroup ↥L} [A.Normal] [B.Normal] (hBA : B ≤ A) (hAH₁ : A ≤ H₁)
    (hAcomm : _root_.commutator (↥H ⧸ A.subgroupOf H) ≠ ⊤)
    (hcentral : (A.subgroupOf H).map (QuotientGroup.mk' (B.subgroupOf H)) ≤
      Subgroup.center (↥H ⧸ B.subgroupOf H))
    (hSAcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration A)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)))
    (hSBncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration B)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    Nat.card (↥H ⧸ H₁.subgroupOf H) ≤ 4 * H.index ^ 2 + 1 := by
  let : H.Normal := hyp.H_normal
  have hsixtwo := hyp.six_two_central hF (hyp.SsubFiltration_antitone hBA) hAcomm
    (A.subgroupOf H) (Subgroup.subgroupOf_mono H hBA) hcentral hSAcoh hSBncoh
  have hHH1le : Nat.card (↥H ⧸ H₁.subgroupOf H) ≤ Nat.card (↥H ⧸ A.subgroupOf H) :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_of_le (Subgroup.subgroupOf_mono H hAH₁))
  refine six_three_HH1_le (LK := H.index) (KH := 1) (HA := Nat.card (↥H ⧸ A.subgroupOf H))
    (HH1 := Nat.card (↥H ⧸ H₁.subgroupOf H)) (by norm_num) hHH1le ?_
  simpa [Subgroup.index_eq_card] using hsixtwo

/-- **`hAcomm` from nilpotency of `H`.**

In the Sibley setup `H` is nilpotent, so for a normal `A ⊊ H` the quotient `H/A` is a nontrivial
nilpotent (hence solvable) group, whence its commutator subgroup is proper: `[H/A, H/A] ≠ ⊤`.  This
supplies the `hAcomm` hypothesis of `six_two_index_bound` / `six_three_index_bound` (which need a
degree-`|W₁|` anchor in `S(A)`). -/
theorem commutator_subgroupOf_quotient_ne_top (hyp : SibleyDadeHypothesis G L H)
    {A : Subgroup ↥L} [A.Normal] (hAH : A < H) :
    _root_.commutator (↥H ⧸ A.subgroupOf H) ≠ ⊤ := by
  let : H.Normal := hyp.H_normal
  let : Group.IsNilpotent ↥H := hyp.H_nilpotent
  have : (A.subgroupOf H).Normal := (‹A.Normal›).subgroupOf H
  have : Nontrivial (↥H ⧸ A.subgroupOf H) := by
    rw [QuotientGroup.nontrivial_iff]
    intro htop
    rw [Subgroup.subgroupOf_eq_top] at htop
    exact hAH.ne (le_antisymm hAH.le htop)
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (G := ↥H ⧸ A.subgroupOf H)).ne

/-- **Peterfalvi (6.3)** (Frobenius case `K = H`).

With `M ≤ H₁ ⊊ H` normal subgroups of `L`, `S(H₁)` coherent and `|H:H₁| > 4|L:H|² + 1`, the set
`S(M)` is coherent.

Minimal-`A` induction (Peterfalvi's argument): pick a normal `A ∈ [M, H₁]` with `S(A)` coherent that
is minimal for `⊆` (exists since `H₁` qualifies).  If `A ≠ M` then `M < A`; take a maximal normal
`B` with `M ≤ B ⊊ A` (`exists_maximal_normal_between`).  Then `A/B ⊆ Z(H/B)`
(`normal_central_of_maximal_normal_below`, using `H` nilpotent), and `S(B)` is *not* coherent (else
`B ∈ [M, H₁]` would beat the minimality of `A`).  So `six_three_index_bound` gives
`|H:H₁| ≤ 4|L:H|² + 1`, contradicting the hypothesis.  Hence `A = M` and `S(M) = S(A)` is
coherent. -/
theorem six_three (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {M H₁ : Subgroup ↥L} [M.Normal] [H₁.Normal] (hMH₁ : M ≤ H₁) (hH₁H : H₁ < H)
    (hcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration H₁)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)))
    (hbound : 4 * H.index ^ 2 + 1 < Nat.card (↥H ⧸ H₁.subgroupOf H)) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration M)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)) := by
  classical
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
    have hAltH : A < H := lt_of_le_of_lt hAH₁ hH₁H
    have hAcomm := hyp.commutator_subgroupOf_quotient_ne_top hAltH
    have hcentral := normal_central_of_maximal_normal_below (H := H) (A := A) (B := B)
      ‹H.Normal› hAltH.le hBltA hBmaxl
    have hSBncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration B)
        (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)) := by
      intro hBcoh
      have hBs : B ∈ s := by
        simp only [hs_def, Set.mem_ofPred_eq]
        exact ⟨hBnorm, hMB, hBltA.le.trans hAH₁, hBcoh⟩
      exact lt_irrefl _ (hBltA.trans_le (hAmin hBs hBltA.le))
    have hbnd := hyp.six_three_index_bound hF hBltA.le hAH₁ hAcomm hcentral hAcoh hSBncoh
    omega
  rw [← hAeqM]
  exact hAcoh

/-- **Peterfalvi (6.5) consequence (Frobenius case): `H` is a `p`-group.**

If the full set `S` is *not* coherent, then `H` is a `p`-group for some prime `p`.  Apply
`six_three`
with `M = ⊥`, `H₁ = ⁅H,H⁆`: `S(⁅H,H⁆) = Y` is coherent (`coherentYset`), `⊥ ≤ ⁅H,H⁆` and `⁅H,H⁆ ⊊ H`
(`H` nilpotent nontrivial ⟹ not perfect), so if `|H:⁅H,H⁆| > 4|L:H|²+1` then `S(⊥) = S` would be
coherent — contradiction.  Hence `|Abelianization H| = |H:⁅H,H⁆| ≤ 4|W₁|²+1`
(`commutator_subgroupOf_self`, `index_H_eq_card_W1`), and as everything has odd order
`isPGroup_of_isFrobeniusGroup_of_card_le` produces the prime.  This is the (6.5)/(6.6) reduction
"`H` is a `p`-group" that feeds the (6.8) capstone. -/
theorem isPGroup_of_not_coherent (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hSncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.S
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    ∃ p : ℕ, p.Prime ∧ IsPGroup p ↥H := by
  let : H.Normal := hyp.H_normal
  let : Group.IsNilpotent ↥H := hyp.H_nilpotent
  have : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hyp.H_ne_bot
  -- `⁅H,H⁆ ⊊ H` from nilpotency (nontrivial nilpotent is not perfect)
  have hcommlt : (⁅H, H⁆ : Subgroup ↥L) < H := by
    have h1 : _root_.commutator ↥H < ⊤ := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥H
    rw [← commutator_subgroupOf_self] at h1
    refine lt_of_le_of_ne (Subgroup.commutator_le_left H H) (fun heq => ?_)
    rw [heq, Subgroup.subgroupOf_self] at h1
    exact lt_irrefl _ h1
  -- the index bound, by the contrapositive of `six_three`
  have hidx : Nat.card (↥H ⧸ (⁅H, H⁆ : Subgroup ↥L).subgroupOf H) ≤ 4 * H.index ^ 2 + 1 := by
    by_contra hgt
    rw [not_le] at hgt
    have hYcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.SsubFiltration ⁅H, H⁆)
        (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)) := ⟨hyp.coherentYset⟩
    have hMcoh := hyp.six_three hF (M := ⊥) (H₁ := ⁅H, H⁆) bot_le hcommlt hYcoh hgt
    rw [hyp.SsubFiltration_bot] at hMcoh
    exact hSncoh hMcoh
  -- convert the index bound to the abelianization-card bound
  have hbound : Nat.card (Abelianization ↥H) ≤ 4 * Nat.card hyp.W1 ^ 2 + 1 := by
    rw [commutator_subgroupOf_self, hyp.index_H_eq_card_W1] at hidx
    exact hidx
  -- odd orders
  have hLodd : Odd (Nat.card ↥L) := hyp.card_L_odd
  have hHodd : Odd (Nat.card (Abelianization ↥H)) :=
    Odd.of_dvd_nat (Odd.of_dvd_nat hLodd H.card_subgroup_dvd_card)
      (Subgroup.card_quotient_dvd_card (_root_.commutator ↥H))
  have hW1odd : Odd (Nat.card hyp.W1) := Odd.of_dvd_nat hLodd hyp.W1.card_subgroup_dvd_card
  exact isPGroup_of_isFrobeniusGroup_of_card_le hF hHodd hW1odd hbound

/-- **(T8 leaf 8) `2 ≤ |S₀|`**, from the abstract input `X ⊆ Irr L`.

If `X` is nonempty, its base block `S₀` (minimal-degree members) contains a minimal-degree `χ`
together with its conjugate `χ̄ ≠ χ` (`Xset_hasNoRealCharacters_of_irreducible_X`,
`xBaseBlock_closedUnderConjugate_of_irreducible_X`), so `2 ≤ |S₀|`. -/
theorem two_le_xBaseBlock_ncard_of_irreducible_X (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ) (hXne : (hyp.Xset Z).Nonempty) :
    2 ≤ (hyp.xBaseBlock Z).ncard := by
  have hXfin := hyp.xSet_finite_of_irreducible_X hX
  obtain ⟨χ, hχX, hχmin⟩ := Set.exists_min_image (hyp.Xset Z)
    (fun ψ => (OddOrder.Peterfalvi.S03.characterDegree ψ).re) hXfin hXne
  have hχS₀ : χ ∈ hyp.xBaseBlock Z := ⟨hχX, hχmin⟩
  have hconjS₀ : χ.conj ∈ hyp.xBaseBlock Z :=
    hyp.xBaseBlock_closedUnderConjugate_of_irreducible_X hZH hX hχS₀
  have hne : χ.conj ≠ χ := hyp.Xset_hasNoRealCharacters_of_irreducible_X hZH hX hχX
  have hS₀fin : (hyp.xBaseBlock Z).Finite := hXfin.subset (hyp.xBaseBlock_subset Z)
  have h1 : 1 < (hyp.xBaseBlock Z).ncard :=
    (Set.one_lt_ncard hS₀fin).mpr ⟨χ.conj, hconjS₀, χ, hχS₀, hne⟩
  omega

/-- **(T8 leaf 8) `2 ≤ |S₀|`** (Frobenius case). -/
theorem two_le_xBaseBlock_ncard (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal] (hXne : (hyp.Xset Z).Nonempty) :
    2 ≤ (hyp.xBaseBlock Z).ncard :=
  hyp.two_le_xBaseBlock_ncard_of_irreducible_X hZH
    (fun _ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h) hXne

end SibleyDadeHypothesis

end OddOrder.Peterfalvi.S08


