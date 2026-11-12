-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S05_SignedTripleGrid
-- name    : OddOrder_Peterfalvi_S05_SignedTripleGrid
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:48:53.572493+00:00
-- url     : https://prove2.me/theorems/8da947e7-7806-43a6-9707-6a849c758f44
-- title:
--   Peterfalvi (3.5.4): the signed-triple grid (tail)
-- statement:
--   The final part of the Peterfalvi §3 signed-triple-grid development, containing the case analysis of (3.5.4) on the grid of signed triples.
--
--   Main results: `exists_namedTriangle` (the (3.5.4) named triangle), `caseII_false` (Case II is impossible), `lStep` (the $L$-step) and the $O$-step variants `oStep`, `oStep_out`, `oStep_force` and `oStep_both_out`.
--
--   The bundle also proves 12 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S05_SignedTripleGrid.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S05_SignedTripleGrid.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S05_NormThree
import Definitions.Def_OddOrder_Peterfalvi_S05_NormThreeCharacters

namespace OddOrder.Peterfalvi.S05

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G]

namespace IsSignedTripleGrid

variable [Invertible (Nat.card G : ℂ)] {ι κ : Type*} {A : ι → κ → Finset (ClassFunction G ℂ)}

/-- In a single cell `A i j`, the negative of a member is not a member (it is a signed triple). -/
theorem neg_not_mem_self (hG : IsSignedTripleGrid A) {i : ι} {j : κ} {x : ClassFunction G ℂ}
    (hx : x ∈ A i j) : -x ∉ A i j := by
  intro hnx
  have hxsig := hG.signed i j x hx
  have h0 := hG.orthogonal i j x hx (-x) hnx (fun h => hxsig.ne_neg_self h)
  rw [ClassFunction.inner_neg_right, hxsig.inner_self] at h0
  exact one_ne_zero (neg_eq_zero.mp h0)

/-- **Uniqueness half of (3.5.4)**: for a fixed column `j₀`, at most one element lies in every
`A i j₀` (two such would both lie in `A i₁ j₀ ∩ A i₂ j₀`, a singleton by `L`). -/
theorem common_unique [Fintype ι] (hG : IsSignedTripleGrid A) (hι : 2 ≤ Fintype.card ι) {j₀ : κ}
    {z z' : ClassFunction G ℂ} (hz : ∀ i, z ∈ A i j₀) (hz' : ∀ i, z' ∈ A i j₀) : z = z' := by
  classical
  have : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨i₁, i₂, h12⟩ := exists_pair_ne ι
  have hcard : (A i₁ j₀ ∩ A i₂ j₀).card = 1 := hG.inter_L i₁ i₂ j₀ j₀ (Or.inr ⟨h12, rfl⟩)
  have hle := Finset.card_le_one.mp (le_of_eq hcard)
  exact hle z (Finset.mem_inter.mpr ⟨hz i₁, hz i₂⟩) z' (Finset.mem_inter.mpr ⟨hz' i₁, hz' i₂⟩)

/-- **(3.5.4) reduction**: if no element is common to every `A i j₀` (the negation of (3.5.4)),
then three rows `i₁, i₂, i₃` have *no* common element — a "triangle" (their three pairwise
intersection elements are then forced distinct).  Pick distinct `i₁, i₂` with common element `z`
(unique by `L`); since `z` is not common to all rows there is `i₃` with `z ∉ A i₃ j₀`; the triple
`{i₁, i₂, i₃}` then shares no element (a common `w` would equal `z ∉ A i₃ j₀`). -/
theorem exists_triangle_of_not_exists_common [Fintype ι] (hG : IsSignedTripleGrid A)
    (hι : 2 ≤ Fintype.card ι) (j₀ : κ) (hno : ¬ ∃ z, ∀ i, z ∈ A i j₀) :
    ∃ i₁ i₂ i₃ : ι, i₁ ≠ i₂ ∧ i₁ ≠ i₃ ∧ i₂ ≠ i₃ ∧
      ¬ ∃ w, w ∈ A i₁ j₀ ∧ w ∈ A i₂ j₀ ∧ w ∈ A i₃ j₀ := by
  classical
  have : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨i₁, i₂, h12⟩ := exists_pair_ne ι
  have hcard : (A i₁ j₀ ∩ A i₂ j₀).card = 1 := hG.inter_L i₁ i₂ j₀ j₀ (Or.inr ⟨h12, rfl⟩)
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcard
  have hzmem : z ∈ A i₁ j₀ ∩ A i₂ j₀ := hz ▸ Finset.mem_singleton_self z
  obtain ⟨hz1, hz2⟩ := Finset.mem_inter.mp hzmem
  -- some row misses `z`, else `z` is common.
  obtain ⟨i₃, hz3⟩ : ∃ i₃, z ∉ A i₃ j₀ := by
    by_contra hcon
    exact hno ⟨z, fun i => not_not.mp (fun h => hcon ⟨i, h⟩)⟩
  refine ⟨i₁, i₂, i₃, h12, ?_, ?_, ?_⟩
  · rintro rfl; exact hz3 hz1
  · rintro rfl; exact hz3 hz2
  · rintro ⟨w, hw1, hw2, hw3⟩
    have hle := Finset.card_le_one.mp (le_of_eq hcard)
    exact hz3 ((hle w (Finset.mem_inter.mpr ⟨hw1, hw2⟩) z hzmem) ▸ hw3)

open scoped Classical in
/-- **(3.5.4) named triangle**: from three rows `i₁, i₂, i₃` with no common element, name their
three pairwise-intersection elements `e₁₂, e₁₃, e₂₃` (the "vertices", forced distinct) and the
three remaining "third" elements `t₁, t₂, t₃`, giving the explicit decompositions
`A i₁ j₀ = {e₁₂, e₁₃, t₁}`, `A i₂ j₀ = {e₁₂, e₂₃, t₂}`, `A i₃ j₀ = {e₁₃, e₂₃, t₃}`
(Peterfalvi's `β₁₁ = χ₁+χ₂+χ₃`, `β₂₁ = χ₁+χ₄+χ₅`, `β₃₁ = χ₂+χ₄+χ₆`).  Input to the Cases-I/II
argument that adds a fourth row. -/
theorem exists_namedTriangle (hG : IsSignedTripleGrid A) {i₁ i₂ i₃ : ι} {j₀ : κ}
    (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃) (h23 : i₂ ≠ i₃)
    (hnoc : ¬ ∃ w, w ∈ A i₁ j₀ ∧ w ∈ A i₂ j₀ ∧ w ∈ A i₃ j₀) :
    ∃ e₁₂ e₁₃ e₂₃ t₁ t₂ t₃ : ClassFunction G ℂ,
      A i₁ j₀ = {e₁₂, e₁₃, t₁} ∧ A i₂ j₀ = {e₁₂, e₂₃, t₂} ∧ A i₃ j₀ = {e₁₃, e₂₃, t₃} ∧
      e₁₂ ≠ e₁₃ ∧ e₁₂ ≠ e₂₃ ∧ e₁₃ ≠ e₂₃ := by
  classical
  obtain ⟨e₁₂, he12⟩ := Finset.card_eq_one.mp (hG.inter_L i₁ i₂ j₀ j₀ (Or.inr ⟨h12, rfl⟩))
  obtain ⟨e₁₃, he13⟩ := Finset.card_eq_one.mp (hG.inter_L i₁ i₃ j₀ j₀ (Or.inr ⟨h13, rfl⟩))
  obtain ⟨e₂₃, he23⟩ := Finset.card_eq_one.mp (hG.inter_L i₂ i₃ j₀ j₀ (Or.inr ⟨h23, rfl⟩))
  obtain ⟨m12a, m12b⟩ := Finset.mem_inter.mp (he12 ▸ Finset.mem_singleton_self e₁₂)
  obtain ⟨m13a, m13b⟩ := Finset.mem_inter.mp (he13 ▸ Finset.mem_singleton_self e₁₃)
  obtain ⟨m23a, m23b⟩ := Finset.mem_inter.mp (he23 ▸ Finset.mem_singleton_self e₂₃)
  have d1213 : e₁₂ ≠ e₁₃ := by rintro rfl; exact hnoc ⟨e₁₂, m12a, m12b, m13b⟩
  have d1223 : e₁₂ ≠ e₂₃ := by rintro rfl; exact hnoc ⟨e₁₂, m12a, m12b, m23b⟩
  have d1323 : e₁₃ ≠ e₂₃ := by rintro rfl; exact hnoc ⟨e₁₃, m13a, m23a, m13b⟩
  obtain ⟨t₁, _, _, _, hset1⟩ :=
    exists_third_of_card_three (hG.card_eq_three i₁ j₀) m12a m13a d1213
  obtain ⟨t₂, _, _, _, hset2⟩ :=
    exists_third_of_card_three (hG.card_eq_three i₂ j₀) m12b m23a d1223
  obtain ⟨t₃, _, _, _, hset3⟩ :=
    exists_third_of_card_three (hG.card_eq_three i₃ j₀) m13b m23b d1323
  exact ⟨e₁₂, e₁₃, e₂₃, t₁, t₂, t₃, hset1, hset2, hset3, d1213, d1223, d1323⟩

open scoped Classical in
/-- **(3.5.4) Case II is impossible**: a fourth row `i₄` whose `j₀`-cell is exactly the three
"third" elements `{χ₃, χ₅, χ₆}` (the K₄ configuration, Peterfalvi's `β₄₁ = χ₃+χ₅+χ₆`) yields a
contradiction.  Look at the second-column cell `B = A i₁ j₁`: writing `n_k = [χ_k ∈ B]`,
`p_k = [-χ_k ∈ B]`, the relations `L(i₁j₁, i₁j₀)` (gives `n₁+n₂+n₃ = 1`, `p₁=p₂=p₃=0`) and
`O(i₁j₁, i_pj₀)` for `p = 2,3,4` (give `n₁+n₄+n₅ = p₁+p₄+p₅` etc.) sum to `1 + 2(n₄+n₅+n₆) =
2(p₄+p₅+p₆)` — an odd number equal to an even one.  (This single parity argument replaces
Peterfalvi's case-by-case (3.5.4.6).) -/
theorem caseII_false (hG : IsSignedTripleGrid A) {i₁ i₂ i₃ i₄ : ι} {j₀ j₁ : κ}
    {χ1 χ2 χ3 χ4 χ5 χ6 : ClassFunction G ℂ} (hj : j₁ ≠ j₀)
    (hi12 : i₁ ≠ i₂) (hi13 : i₁ ≠ i₃) (hi14 : i₁ ≠ i₄)
    (hset1 : A i₁ j₀ = {χ1, χ2, χ3}) (hset2 : A i₂ j₀ = {χ1, χ4, χ5})
    (hset3 : A i₃ j₀ = {χ2, χ4, χ6}) (hset4 : A i₄ j₀ = {χ3, χ5, χ6}) : False := by
  classical
  obtain ⟨d12, d13, d23⟩ := triple_distinct (hset1 ▸ hG.card_eq_three i₁ j₀)
  obtain ⟨d14, d15, d45⟩ := triple_distinct (hset2 ▸ hG.card_eq_three i₂ j₀)
  obtain ⟨d24, d26, d46⟩ := triple_distinct (hset3 ▸ hG.card_eq_three i₃ j₀)
  obtain ⟨d35, d36, d56⟩ := triple_distinct (hset4 ▸ hG.card_eq_three i₄ j₀)
  have hnoNeg : ∀ x ∈ A i₁ j₁, -x ∉ A i₁ j₀ := hG.noNeg_L i₁ i₁ j₁ j₀ (Or.inl ⟨rfl, hj⟩)
  have hL : (A i₁ j₁ ∩ ({χ1, χ2, χ3} : Finset _)).card = 1 := by
    have h := hG.inter_L i₁ i₁ j₁ j₀ (Or.inl ⟨rfl, hj⟩); rwa [hset1] at h
  have hO2 : (A i₁ j₁ ∩ ({χ1, χ4, χ5} : Finset _)).card =
      (A i₁ j₁ |>.filter (fun x => -x ∈ ({χ1, χ4, χ5} : Finset _))).card := by
    have h := hG.inter_O i₁ i₂ j₁ j₀ hi12 hj; rwa [hset2] at h
  have hO3 : (A i₁ j₁ ∩ ({χ2, χ4, χ6} : Finset _)).card =
      (A i₁ j₁ |>.filter (fun x => -x ∈ ({χ2, χ4, χ6} : Finset _))).card := by
    have h := hG.inter_O i₁ i₃ j₁ j₀ hi13 hj; rwa [hset3] at h
  have hO4 : (A i₁ j₁ ∩ ({χ3, χ5, χ6} : Finset _)).card =
      (A i₁ j₁ |>.filter (fun x => -x ∈ ({χ3, χ5, χ6} : Finset _))).card := by
    have h := hG.inter_O i₁ i₄ j₁ j₀ hi14 hj; rwa [hset4] at h
  rw [card_inter_triple _ d12 d13 d23] at hL
  rw [card_inter_triple _ d14 d15 d45, card_filter_neg_triple _ d14 d15 d45] at hO2
  rw [card_inter_triple _ d24 d26 d46, card_filter_neg_triple _ d24 d26 d46] at hO3
  rw [card_inter_triple _ d35 d36 d56, card_filter_neg_triple _ d35 d36 d56] at hO4
  -- `-χ₁, -χ₂, -χ₃ ∉ B` (the `noNeg` half of `L(i₁j₁, i₁j₀)`).
  have hp1 : -χ1 ∉ A i₁ j₁ := fun hm =>
    hnoNeg _ hm (by rw [neg_neg, hset1]; exact Finset.mem_insert_self _ _)
  have hp2 : -χ2 ∉ A i₁ j₁ := fun hm =>
    hnoNeg _ hm (by rw [neg_neg, hset1]
                    exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hp3 : -χ3 ∉ A i₁ j₁ := fun hm =>
    hnoNeg _ hm (by rw [neg_neg, hset1]
                    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
                      (Finset.mem_singleton_self _)))
  rw [if_neg hp1] at hO2
  rw [if_neg hp2] at hO3
  rw [if_neg hp3] at hO4
  -- Atomise the indicators and finish by parity (sum of the three `O`s is `odd = even`).
  set n1 := (if χ1 ∈ A i₁ j₁ then 1 else 0 : ℕ)
  set n2 := (if χ2 ∈ A i₁ j₁ then 1 else 0 : ℕ)
  set n3 := (if χ3 ∈ A i₁ j₁ then 1 else 0 : ℕ)
  set n4 := (if χ4 ∈ A i₁ j₁ then 1 else 0 : ℕ)
  set n5 := (if χ5 ∈ A i₁ j₁ then 1 else 0 : ℕ)
  set n6 := (if χ6 ∈ A i₁ j₁ then 1 else 0 : ℕ)
  set p4 := (if -χ4 ∈ A i₁ j₁ then 1 else 0 : ℕ)
  set p5 := (if -χ5 ∈ A i₁ j₁ then 1 else 0 : ℕ)
  set p6 := (if -χ6 ∈ A i₁ j₁ then 1 else 0 : ℕ)
  omega

/-- For two `L`-linked cells, no member of one is the negative of a member of the other (the
`noNeg_L` field, read symmetrically). -/
theorem ne_neg_of_Llinked (hG : IsSignedTripleGrid A) {i i' : ι} {j j' : κ}
    (h : (i = i' ∧ j ≠ j') ∨ (i ≠ i' ∧ j = j')) {x y : ClassFunction G ℂ}
    (hx : x ∈ A i j) (hy : y ∈ A i' j') : x ≠ -y := by
  have hsymm : (i' = i ∧ j' ≠ j) ∨ (i' ≠ i ∧ j' = j) := by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1.symm, h2.symm⟩
    · exact Or.inr ⟨h1.symm, h2.symm⟩
  intro hxy
  exact hG.noNeg_L i' i j' j hsymm y hy (hxy ▸ hx)

/-- For two `L`-linked cells sharing the element `z`, any common element equals `z`
(`|A ∩ A'| = 1`). -/
theorem eq_of_mem_Llinked (hG : IsSignedTripleGrid A) {i i' : ι} {j j' : κ}
    (h : (i = i' ∧ j ≠ j') ∨ (i ≠ i' ∧ j = j')) {z w : ClassFunction G ℂ}
    (hz : z ∈ A i j) (hz' : z ∈ A i' j') (hw : w ∈ A i j) (hw' : w ∈ A i' j') : w = z := by
  classical
  have hcard := hG.inter_L i i' j j' h
  exact Finset.card_le_one.mp (le_of_eq hcard) w (Finset.mem_inter.mpr ⟨hw, hw'⟩) z
    (Finset.mem_inter.mpr ⟨hz, hz'⟩)

open scoped Classical in
/-- **(3.5.4) `L`-step**: if `B = A i j` and `A i' j' = {χ, u, v}` are `L`-linked cells with
`χ ∈ B` (so `χ` is *the* shared element), then `u, v ∉ B`, and none of `χ, u, v` has its negative
in `B`. -/
theorem lStep (hG : IsSignedTripleGrid A) {i i' : ι} {j j' : κ}
    (h : (i = i' ∧ j ≠ j') ∨ (i ≠ i' ∧ j = j')) {χ u v : ClassFunction G ℂ}
    (hC : A i' j' = {χ, u, v}) (hχu : χ ≠ u) (hχv : χ ≠ v) (_huv : u ≠ v)
    (hχB : χ ∈ A i j) :
    u ∉ A i j ∧ v ∉ A i j ∧ -χ ∉ A i j ∧ -u ∉ A i j ∧ -v ∉ A i j := by
  have hsymm : (i' = i ∧ j' ≠ j) ∨ (i' ≠ i ∧ j' = j) := by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1.symm, h2.symm⟩
    · exact Or.inr ⟨h1.symm, h2.symm⟩
  have hχC : χ ∈ A i' j' := by rw [hC]; exact Finset.mem_insert_self _ _
  have huC : u ∈ A i' j' := by
    rw [hC]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hvC : v ∈ A i' j' := by
    rw [hC]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact fun h' => hχu (eq_of_mem_Llinked hG h hχB hχC h' huC).symm
  · exact fun h' => hχv (eq_of_mem_Llinked hG h hχB hχC h' hvC).symm
  · exact hG.noNeg_L i' i j' j hsymm χ hχC
  · exact hG.noNeg_L i' i j' j hsymm u huC
  · exact hG.noNeg_L i' i j' j hsymm v hvC

open scoped Classical in
/-- **(3.5.4) O-step**: if `B = A i j` and `A i' j' = {χ, u, v}` are `O`-related cells (`i ≠ i'`,
`j ≠ j'`) with `χ ∈ B` and `-χ ∉ B`, then `u, v ∉ B` and *exactly one* of `-u, -v` lies in `B`
(stated as `-u ∈ B ↔ -v ∉ B`).  This is the engine of (3.5.4.1). -/
theorem oStep (hG : IsSignedTripleGrid A) {i i' : ι} {j j' : κ} (hii : i ≠ i') (hjj : j ≠ j')
    {χ u v : ClassFunction G ℂ} (hC : A i' j' = {χ, u, v})
    (hχu : χ ≠ u) (hχv : χ ≠ v) (huv : u ≠ v)
    (hχB : χ ∈ A i j) (hnegχ : -χ ∉ A i j) :
    u ∉ A i j ∧ v ∉ A i j ∧ (-u ∈ A i j ↔ -v ∉ A i j) := by
  classical
  have hO := hG.inter_O i i' j j' hii hjj
  rw [hC, card_inter_triple _ hχu hχv huv, card_filter_neg_triple _ hχu hχv huv,
    if_pos hχB, if_neg hnegχ] at hO
  set au := (if u ∈ A i j then (1 : ℕ) else 0) with hau
  set av := (if v ∈ A i j then (1 : ℕ) else 0) with hav
  set bu := (if -u ∈ A i j then (1 : ℕ) else 0) with hbu
  set bv := (if -v ∈ A i j then (1 : ℕ) else 0) with hbv
  have hau1 : au ≤ 1 := by rw [hau]; split <;> omega
  have hav1 : av ≤ 1 := by rw [hav]; split <;> omega
  have hbu1 : bu ≤ 1 := by rw [hbu]; split <;> omega
  have hbv1 : bv ≤ 1 := by rw [hbv]; split <;> omega
  have cu : au + bu ≤ 1 := by
    rw [hau, hbu]; by_cases h : u ∈ A i j
    · rw [if_pos h, if_neg (hG.neg_not_mem_self h)]
    · rw [if_neg h]; split <;> omega
  have cv : av + bv ≤ 1 := by
    rw [hav, hbv]; by_cases h : v ∈ A i j
    · rw [if_pos h, if_neg (hG.neg_not_mem_self h)]
    · rw [if_neg h]; split <;> omega
  obtain ⟨hau0, hav0, hsum⟩ : au = 0 ∧ av = 0 ∧ bu + bv = 1 := by omega
  refine ⟨?_, ?_, ?_⟩
  · intro h; rw [hau, if_pos h] at hau0; exact one_ne_zero hau0
  · intro h; rw [hav, if_pos h] at hav0; exact one_ne_zero hav0
  · constructor
    · intro h hnv'; rw [hbu, if_pos h, hbv, if_pos hnv'] at hsum; omega
    · intro h; by_contra h'; rw [hbu, if_neg h', hbv, if_neg h] at hsum; omega

open scoped Classical in
/-- **(3.5.4) O-step (all-out)**: if `B = A i j` and `A i' j' = {x, y, z}` are `O`-related and
none of `x, y, z` lies in `B`, then none of `-x, -y, -z` lies in `B`.  Used with the transversal
cell to kill the negated meet-points at once. -/
theorem oStep_out (hG : IsSignedTripleGrid A) {i i' : ι} {j j' : κ} (hii : i ≠ i') (hjj : j ≠ j')
    {x y z : ClassFunction G ℂ} (hC : A i' j' = {x, y, z})
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : x ∉ A i j) (hy : y ∉ A i j) (hz : z ∉ A i j) :
    -x ∉ A i j ∧ -y ∉ A i j ∧ -z ∉ A i j := by
  classical
  have hO := hG.inter_O i i' j j' hii hjj
  rw [hC, card_inter_triple _ hxy hxz hyz, card_filter_neg_triple _ hxy hxz hyz,
    if_neg hx, if_neg hy, if_neg hz] at hO
  refine ⟨?_, ?_, ?_⟩ <;> intro h
  · rw [if_pos h] at hO; omega
  · rw [if_pos h] at hO; omega
  · rw [if_pos h] at hO; omega

/-- Two members of the *same* cell are never negatives of each other. -/
theorem ne_neg_of_mem_same (hG : IsSignedTripleGrid A) {i : ι} {j : κ}
    {x y : ClassFunction G ℂ} (hx : x ∈ A i j) (hy : y ∈ A i j) : x ≠ -y :=
  fun h => hG.neg_not_mem_self hy (h ▸ hx)

open scoped Classical in
/-- **(3.5.4) O-step (force)**: if `B = A i j` and `A i' j' = {x, y, z}` are `O`-related with
`x, y ∉ B` but `-x ∈ B`, then `z ∈ B` (the lone negated member forces the third one in). -/
theorem oStep_force (hG : IsSignedTripleGrid A) {i i' : ι} {j j' : κ} (hii : i ≠ i') (hjj : j ≠ j')
    {x y z : ClassFunction G ℂ} (hC : A i' j' = {x, y, z})
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : x ∉ A i j) (hy : y ∉ A i j) (hnx : -x ∈ A i j) : z ∈ A i j := by
  classical
  have hO := hG.inter_O i i' j j' hii hjj
  rw [hC, card_inter_triple _ hxy hxz hyz, card_filter_neg_triple _ hxy hxz hyz,
    if_neg hx, if_neg hy, if_pos hnx] at hO
  by_contra hz
  rw [if_neg hz] at hO; omega

open scoped Classical in
/-- **(3.5.4) O-step (both-out)**: if `B = A i j` and `A i' j' = {x, y, z}` are `O`-related with
`x, y ∉ B` and `-x, -y ∉ B`, then neither `z` nor `-z` lies in `B`.  (The O-relation reduces to
`[z ∈ B] = [-z ∈ B]`, impossible for a `1` and forced `0` for a `0`.)  Yields newness of the
"third element" against a whole cell at once. -/
theorem oStep_both_out (hG : IsSignedTripleGrid A) {i i' : ι} {j j' : κ}
    (hii : i ≠ i') (hjj : j ≠ j') {x y z : ClassFunction G ℂ} (hC : A i' j' = {x, y, z})
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : x ∉ A i j) (hy : y ∉ A i j) (hnx : -x ∉ A i j) (hny : -y ∉ A i j) :
    z ∉ A i j ∧ -z ∉ A i j := by
  classical
  have hO := hG.inter_O i i' j j' hii hjj
  rw [hC, card_inter_triple _ hxy hxz hyz, card_filter_neg_triple _ hxy hxz hyz,
    if_neg hx, if_neg hy, if_neg hnx, if_neg hny] at hO
  refine ⟨?_, ?_⟩
  · intro hz; rw [if_pos hz, if_neg (hG.neg_not_mem_self hz)] at hO; omega
  · intro hnz
    rw [if_neg (fun hz => hG.neg_not_mem_self hz hnz), if_pos hnz] at hO; omega

open scoped Classical in
/-- **(3.5.4) L-step (third)**: in an `L`-linked cell `{x, y, z}` with `x, y ∉ B`, the unique
shared element is `z`, so `z ∈ B`. -/
theorem lStep_third (hG : IsSignedTripleGrid A) {i i' : ι} {j j' : κ}
    (h : (i = i' ∧ j ≠ j') ∨ (i ≠ i' ∧ j = j')) {x y z : ClassFunction G ℂ}
    (hC : A i' j' = {x, y, z}) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : x ∉ A i j) (hy : y ∉ A i j) : z ∈ A i j := by
  classical
  have hcard := hG.inter_L i i' j j' h
  rw [hC, card_inter_triple _ hxy hxz hyz, if_neg hx, if_neg hy] at hcard
  by_contra hz; rw [if_neg hz] at hcard; omega

/-- Two distinct elements cannot both be shared by an `L`-linked pair of cells (`|A ∩ A'| = 1`). -/
theorem not_two_shared (hG : IsSignedTripleGrid A) {i i' : ι} {j j' : κ}
    (h : (i = i' ∧ j ≠ j') ∨ (i ≠ i' ∧ j = j')) {u v : ClassFunction G ℂ}
    (hu : u ∈ A i j) (hu' : u ∈ A i' j') (hv : v ∈ A i j) (hv' : v ∈ A i' j')
    (huv : u ≠ v) : False := by
  classical
  have hcard := hG.inter_L i i' j j' h
  have h2 : 1 < (A i j ∩ A i' j').card := Finset.one_lt_card.mpr
    ⟨u, Finset.mem_inter.mpr ⟨hu, hu'⟩, v, Finset.mem_inter.mpr ⟨hv, hv'⟩, huv⟩
  omega

open scoped Classical in
/-- An `L`-linked pair of cells given by *disjoint* explicit triples is impossible (`|A ∩ A'| = 1`
forces a shared element).  Engine of the "`χ ∉ A_{i2}`" steps: a cell forced by `pencilCell` to be
`{χ, -f, -f'}` is disjoint from another determined cell, contradicting `L`. -/
theorem not_disjoint_Llinked (hG : IsSignedTripleGrid A) {i i' : ι} {j j' : κ}
    (h : (i = i' ∧ j ≠ j') ∨ (i ≠ i' ∧ j = j')) {a1 a2 a3 b1 b2 b3 : ClassFunction G ℂ}
    (hX : A i j = {a1, a2, a3}) (hY : A i' j' = {b1, b2, b3})
    (ha1 : a1 ∉ ({b1, b2, b3} : Finset (ClassFunction G ℂ)))
    (ha2 : a2 ∉ ({b1, b2, b3} : Finset (ClassFunction G ℂ)))
    (ha3 : a3 ∉ ({b1, b2, b3} : Finset (ClassFunction G ℂ))) : False := by
  classical
  have hcard := hG.inter_L i i' j j' h
  have hdisj : Disjoint ({a1, a2, a3} : Finset (ClassFunction G ℂ)) {b1, b2, b3} := by
    rw [Finset.disjoint_left]
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ha1
    · exact ha2
    · exact ha3
  have hz : (A i j ∩ A i' j').card = 0 := by
    rw [hX, hY]; exact Finset.card_eq_zero.mpr (Finset.disjoint_iff_inter_eq_empty.mp hdisj)
  omega

open scoped Classical in
/-- **(3.5.4.1) pencil cell**: in the Case-I configuration, three pencil rows `ra, rb, rc` share
the apex `χ` (so `A ra j₀ = {χ, ma, fa}`, etc.) and a transversal row `rt` meets them at the
"meet-points" (`A rt j₀ = {ma, mb, mc}`).  If `χ ∈ A ra j₁` for a second column `j₁`, then the
whole cell is `A ra j₁ = {χ, -fb, -fc}` — the apex together with the *negated free-points* of the
other two pencil rows.  (Peterfalvi: `χ₁ ∈ A₁₂ ⟹ β₁₂ = χ₁ - χ₅ - χ₇`.)  The proof: `L(ra j₁, ra j₀)`
removes `ma, fa`; `O` against `Lb`, `Lc` forces "exactly one of the two negated others"; and the
`O` against the transversal `T` kills both negated meet-points at once, leaving the free ones. -/
theorem pencilCell (hG : IsSignedTripleGrid A) {ra rb rc rt : ι} {j₀ j₁ : κ}
    (hab : ra ≠ rb) (hac : ra ≠ rc) (hat : ra ≠ rt) (hbc : rb ≠ rc) (hj : j₀ ≠ j₁)
    {χ ma mb mc fa fb fc : ClassFunction G ℂ}
    (hLa : A ra j₀ = {χ, ma, fa}) (hLb : A rb j₀ = {χ, mb, fb})
    (hLc : A rc j₀ = {χ, mc, fc}) (hT : A rt j₀ = {ma, mb, mc})
    (hχB : χ ∈ A ra j₁) :
    A ra j₁ = {χ, -fb, -fc} := by
  classical
  obtain ⟨dχma, dχfa, dmafa⟩ := triple_distinct (hLa ▸ hG.card_eq_three ra j₀)
  obtain ⟨dχmb, dχfb, dmbfb⟩ := triple_distinct (hLb ▸ hG.card_eq_three rb j₀)
  obtain ⟨dχmc, dχfc, dmcfc⟩ := triple_distinct (hLc ▸ hG.card_eq_three rc j₀)
  obtain ⟨dmamb, dmamc, dmbmc⟩ := triple_distinct (hT ▸ hG.card_eq_three rt j₀)
  -- Step 1: `L(ra j₁, ra j₀)` — `χ` is the unique shared element; `ma, fa ∉ B`, `-χ ∉ B`.
  obtain ⟨hmaB, hfaB, hnegχB, _, _⟩ :=
    lStep hG (Or.inl ⟨rfl, hj.symm⟩) hLa dχma dχfa dmafa hχB
  -- Step 2/3: `O` against the other two pencil rows.
  obtain ⟨hmbB, _, hxorb⟩ := oStep hG hab hj.symm hLb dχmb dχfb dmbfb hχB hnegχB
  obtain ⟨hmcB, _, hxorc⟩ := oStep hG hac hj.symm hLc dχmc dχfc dmcfc hχB hnegχB
  -- Step 4: `O` against the transversal — `ma, mb, mc ∉ B`, so `-mb, -mc ∉ B`.
  obtain ⟨_, hnegmbB, hnegmcB⟩ :=
    oStep_out hG hat hj.symm hT dmamb dmamc dmbmc hmaB hmbB hmcB
  -- Step 5: hence `-fb, -fc ∈ B`.
  have hnegfbB : -fb ∈ A ra j₁ := not_not.mp (fun h => hnegmbB (hxorb.mpr h))
  have hnegfcB : -fc ∈ A ra j₁ := not_not.mp (fun h => hnegmcB (hxorc.mpr h))
  -- Distinctness for the final triple.
  have hχLa : χ ∈ A ra j₀ := by rw [hLa]; exact Finset.mem_insert_self _ _
  have hχLb : χ ∈ A rb j₀ := by rw [hLb]; exact Finset.mem_insert_self _ _
  have hχLc : χ ∈ A rc j₀ := by rw [hLc]; exact Finset.mem_insert_self _ _
  have hfbLb : fb ∈ A rb j₀ := by
    rw [hLb]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_singleton_self _))
  have hfcLc : fc ∈ A rc j₀ := by
    rw [hLc]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_singleton_self _))
  have dχnfb : χ ≠ -fb := ne_neg_of_Llinked hG (Or.inr ⟨hab, rfl⟩) hχLa hfbLb
  have dχnfc : χ ≠ -fc := ne_neg_of_Llinked hG (Or.inr ⟨hac, rfl⟩) hχLa hfcLc
  have dnfbnfc : (-fb) ≠ -fc := by
    intro h
    exact dχfb (eq_of_mem_Llinked hG (Or.inr ⟨hbc, rfl⟩) hχLb hχLc hfbLb
      (neg_injective h ▸ hfcLc)).symm
  -- Conclude `B = {χ, -fb, -fc}` by cardinality.
  have hsub : ({χ, -fb, -fc} : Finset (ClassFunction G ℂ)) ⊆ A ra j₁ := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact hχB
    · exact hnegfbB
    · exact hnegfcB
  have hcard3 : ({χ, -fb, -fc} : Finset (ClassFunction G ℂ)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [dχnfb, dχnfc]),
      Finset.card_insert_of_notMem (by simp [dnfbnfc]), Finset.card_singleton]
  exact (Finset.eq_of_subset_of_card_le hsub
    (le_of_eq (by rw [hG.card_eq_three ra j₁, hcard3]))).symm

open scoped Classical in
/-- **(3.5.4.2) transversal cell**: if the transversal row `rt`'s second-column cell shares the
meet-point `ma` (`= χ₂`) with its first-column cell `{ma, mb, mc}`, then `A rt j₁ = {ma, -fa, χ8}`
for a *new* element `χ8` (Peterfalvi `β₃₂ = χ₂ - χ₃ + χ₈`), distinct from the apex `χ` and from the
meets/frees `±mb, ±mc, fb, fc` of the other two pencil rows.  The shared half is an `L`-step; that
`-fa ∈ B` (rather than `-χ`) comes from excluding `-χ ∈ B`, which would force both free-points
`fb, fc ∈ B` (one O-step each), but `B` has room for only one element besides `ma, -χ`.  Newness of
`χ8` falls out of `oStep_both_out` against the two pencil cells. -/
theorem transversalCell (hG : IsSignedTripleGrid A) {ra rb rc rt : ι} {j₀ j₁ : κ}
    (_hab : ra ≠ rb) (_hac : ra ≠ rc) (hbc : rb ≠ rc)
    (hat : ra ≠ rt) (hbt : rb ≠ rt) (hct : rc ≠ rt) (hj : j₀ ≠ j₁)
    {χ ma mb mc fa fb fc : ClassFunction G ℂ}
    (hLa : A ra j₀ = {χ, ma, fa}) (hLb : A rb j₀ = {χ, mb, fb})
    (hLc : A rc j₀ = {χ, mc, fc}) (hT : A rt j₀ = {ma, mb, mc})
    (hmaB : ma ∈ A rt j₁) :
    ∃ χ8, A rt j₁ = {ma, -fa, χ8} ∧
      χ8 ≠ χ ∧ χ8 ≠ fb ∧ χ8 ≠ fc ∧ χ8 ≠ -fb ∧ χ8 ≠ -fc ∧ χ8 ≠ -mb ∧ χ8 ≠ -mc := by
  classical
  obtain ⟨_, _, dmafa⟩ := triple_distinct (hLa ▸ hG.card_eq_three ra j₀)
  obtain ⟨dχma, dχfa, _⟩ := triple_distinct (hLa ▸ hG.card_eq_three ra j₀)
  obtain ⟨dχmb, dχfb, dmbfb⟩ := triple_distinct (hLb ▸ hG.card_eq_three rb j₀)
  obtain ⟨dχmc, dχfc, dmcfc⟩ := triple_distinct (hLc ▸ hG.card_eq_three rc j₀)
  obtain ⟨dmamb, dmamc, dmbmc⟩ := triple_distinct (hT ▸ hG.card_eq_three rt j₀)
  -- column-`j₀` memberships
  have hχLa : χ ∈ A ra j₀ := by rw [hLa]; exact Finset.mem_insert_self _ _
  have hmaLa : ma ∈ A ra j₀ := by
    rw [hLa]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hfaLa : fa ∈ A ra j₀ := by
    rw [hLa]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_singleton_self _))
  have hχLb : χ ∈ A rb j₀ := by rw [hLb]; exact Finset.mem_insert_self _ _
  have hmbLb : mb ∈ A rb j₀ := by
    rw [hLb]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hfbLb : fb ∈ A rb j₀ := by
    rw [hLb]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_singleton_self _))
  have hχLc : χ ∈ A rc j₀ := by rw [hLc]; exact Finset.mem_insert_self _ _
  have hmcLc : mc ∈ A rc j₀ := by
    rw [hLc]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hfcLc : fc ∈ A rc j₀ := by
    rw [hLc]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_singleton_self _))
  have hmaT : ma ∈ A rt j₀ := by rw [hT]; exact Finset.mem_insert_self _ _
  have hmbT : mb ∈ A rt j₀ := by
    rw [hT]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hmcT : mc ∈ A rt j₀ := by
    rw [hT]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  -- Step 1: `L(rt j₁, rt j₀)`, shared element `ma`.
  obtain ⟨hmb_nB, hmc_nB, hnegma_nB, hnegmb_nB, hnegmc_nB⟩ :=
    lStep hG (Or.inl ⟨rfl, hj.symm⟩) hT dmamb dmamc dmbmc hmaB
  -- Step 2: `O(rt j₁, ra j₀)`, reorder to `{ma, χ, fa}`.
  have hLa' : A ra j₀ = {ma, χ, fa} := by rw [hLa, Finset.insert_comm]
  obtain ⟨hχ_nB, _hfa_nB, hxor⟩ :=
    oStep hG hat.symm hj.symm hLa' dχma.symm dmafa dχfa hmaB hnegma_nB
  -- Step 3: exclude `-χ ∈ B`, hence `-fa ∈ B`.
  have hnegχ_nB : -χ ∉ A rt j₁ := by
    intro hnegχ
    have hfbB : fb ∈ A rt j₁ :=
      oStep_force hG hbt.symm hj.symm hLb dχmb dχfb dmbfb hχ_nB hmb_nB hnegχ
    have hfcB : fc ∈ A rt j₁ :=
      oStep_force hG hct.symm hj.symm hLc dχmc dχfc dmcfc hχ_nB hmc_nB hnegχ
    have hmanegχ : ma ≠ -χ := ne_neg_of_mem_same hG hmaLa hχLa
    obtain ⟨t, _, _, _, hBset⟩ :=
      exists_third_of_card_three (hG.card_eq_three rt j₁) hmaB hnegχ hmanegχ
    have hfbma : fb ≠ ma := fun h => dmbfb
      (eq_of_mem_Llinked hG (Or.inr ⟨hbt, rfl⟩) hmbLb hmbT hfbLb (by rw [h]; exact hmaT)).symm
    have hfcma : fc ≠ ma := fun h => dmcfc
      (eq_of_mem_Llinked hG (Or.inr ⟨hct, rfl⟩) hmcLc hmcT hfcLc (by rw [h]; exact hmaT)).symm
    have hfbnegχ : fb ≠ -χ := ne_neg_of_mem_same hG hfbLb hχLb
    have hfcnegχ : fc ≠ -χ := ne_neg_of_mem_same hG hfcLc hχLc
    have hfbfc : fb ≠ fc := fun h => dχfb
      (eq_of_mem_Llinked hG (Or.inr ⟨hbc, rfl⟩) hχLb hχLc hfbLb (by rw [h]; exact hfcLc)).symm
    have hfbt : fb = t := by
      have := hBset ▸ hfbB
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h | h | h
      · exact absurd h hfbma
      · exact absurd h hfbnegχ
      · exact h
    have hfct : fc = t := by
      have := hBset ▸ hfcB
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h | h | h
      · exact absurd h hfcma
      · exact absurd h hfcnegχ
      · exact h
    exact hfbfc (hfbt.trans hfct.symm)
  have hnegfaB : -fa ∈ A rt j₁ := not_not.mp (fun h => hnegχ_nB (hxor.mpr h))
  -- Step 4: name the third element `χ8`.
  have hmanegfa : ma ≠ -fa := ne_neg_of_mem_same hG hmaLa hfaLa
  obtain ⟨χ8, hχ8B, _, _, hBset⟩ :=
    exists_third_of_card_three (hG.card_eq_three rt j₁) hmaB hnegfaB hmanegfa
  -- Newness of `χ8`.
  obtain ⟨hfb_nB, hnegfb_nB⟩ :=
    oStep_both_out hG hbt.symm hj.symm hLb dχmb dχfb dmbfb hχ_nB hmb_nB hnegχ_nB hnegmb_nB
  obtain ⟨hfc_nB, hnegfc_nB⟩ :=
    oStep_both_out hG hct.symm hj.symm hLc dχmc dχfc dmcfc hχ_nB hmc_nB hnegχ_nB hnegmc_nB
  exact ⟨χ8, hBset, fun h => hχ_nB (h ▸ hχ8B), fun h => hfb_nB (h ▸ hχ8B),
    fun h => hfc_nB (h ▸ hχ8B), fun h => hnegfb_nB (h ▸ hχ8B), fun h => hnegfc_nB (h ▸ hχ8B),
    fun h => hnegmb_nB (h ▸ hχ8B), fun h => hnegmc_nB (h ▸ hχ8B)⟩

open scoped Classical in
/-- **(3.5.4.4)-(3.5.4.5) Case-I endgame**: with the roles fixed as `ra` = special row (whose
`j₁`-cell `B₁ = {ma, -mb, fb}` is determined in (3.5.4.3)), `rb` = active row, `rc` = passive row,
and `B₃ = A rt j₁ = {ma, -fa, χ8}` the transversal cell, the configuration is impossible.

(3.5.4.4): the active cell `B₂ = A rb j₁` has `fb, χ8 ∈ B₂` (`χ ∉ B₂` by `pencilCell` ⊥ `B₁`;
`mb ∉ B₂` by `noNeg(B₁,B₂)`; then `fb ∈ B₂`; `ma ∉ B₂` as the `B₁∩B₂`-share is `fb`; `-fa ∉ B₂`
by an O-step; finally `χ8 ∈ B₂`).  (3.5.4.5): in the passive cell `B₄ = A rc j₁`, `χ ∉ B₄`
(`pencilCell` ⊥ `B₁`); `ma, -fa ∉ B₄` (each forces the other in, contradicting `L(B₄,B₃)`, using
`-χ ∉ B₄` from the *same-row* `noNeg`); so `χ8 ∈ B₄`; then `fb ∉ B₄` (share with `B₂` is `χ8`),
forcing `-mb ∈ B₄` (share with `B₁`); but then `O(B₄, A rb j₀)` forces `mb ∈ B₄` too —
impossible. -/
theorem caseI_tail (hG : IsSignedTripleGrid A) {ra rb rc rt : ι} {j₀ j₁ : κ}
    (hab : ra ≠ rb) (hac : ra ≠ rc) (hbc : rb ≠ rc)
    (_hat : ra ≠ rt) (hbt : rb ≠ rt) (hct : rc ≠ rt) (hj : j₀ ≠ j₁)
    {χ ma mb mc fa fb fc χ8 : ClassFunction G ℂ}
    (hLa : A ra j₀ = {χ, ma, fa}) (hLb : A rb j₀ = {χ, mb, fb})
    (hLc : A rc j₀ = {χ, mc, fc}) (hT : A rt j₀ = {ma, mb, mc})
    (hB3 : A rt j₁ = {ma, -fa, χ8}) (hB1 : A ra j₁ = {ma, -mb, fb})
    (hχ8fb : χ8 ≠ fb) (_hχ8negmb : χ8 ≠ -mb) : False := by
  classical
  obtain ⟨dχma, dχfa, dmafa⟩ := triple_distinct (hLa ▸ hG.card_eq_three ra j₀)
  obtain ⟨dχmb, dχfb, dmbfb⟩ := triple_distinct (hLb ▸ hG.card_eq_three rb j₀)
  obtain ⟨dχmc, dχfc, dmcfc⟩ := triple_distinct (hLc ▸ hG.card_eq_three rc j₀)
  obtain ⟨dma_negfa, dma_χ8, dnegfa_χ8⟩ := triple_distinct (hB3 ▸ hG.card_eq_three rt j₁)
  obtain ⟨dma_negmb, dma_fb, dnegmb_fb⟩ := triple_distinct (hB1 ▸ hG.card_eq_three ra j₁)
  -- column-`j₀` memberships
  have hχLa : χ ∈ A ra j₀ := by rw [hLa]; exact Finset.mem_insert_self _ _
  have hmaLa : ma ∈ A ra j₀ := by
    rw [hLa]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hfaLa : fa ∈ A ra j₀ := by
    rw [hLa]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_singleton_self _))
  have hχLb : χ ∈ A rb j₀ := by rw [hLb]; exact Finset.mem_insert_self _ _
  have hmbLb : mb ∈ A rb j₀ := by
    rw [hLb]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hfbLb : fb ∈ A rb j₀ := by
    rw [hLb]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_singleton_self _))
  have hχLc : χ ∈ A rc j₀ := by rw [hLc]; exact Finset.mem_insert_self _ _
  have hfcLc : fc ∈ A rc j₀ := by
    rw [hLc]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_singleton_self _))
  -- `B₁`, `B₃` memberships
  have hmaB1 : ma ∈ A ra j₁ := by rw [hB1]; exact Finset.mem_insert_self _ _
  have hfbB1 : fb ∈ A ra j₁ := by
    rw [hB1]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_singleton_self _))
  have hnegmbB1 : -mb ∈ A ra j₁ := by
    rw [hB1]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hmaB3 : ma ∈ A rt j₁ := by rw [hB3]; exact Finset.mem_insert_self _ _
  have hnegfaB3 : -fa ∈ A rt j₁ := by
    rw [hB3]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  -- uniform non-negation among named column-`j₀` elements
  have hnn : ∀ {r s : ι} {x y : ClassFunction G ℂ}, x ∈ A r j₀ → y ∈ A s j₀ → x ≠ -y := by
    intro r s x y hx hy
    by_cases hrs : r = s
    · subst hrs; exact ne_neg_of_mem_same hG hx hy
    · exact ne_neg_of_Llinked hG (Or.inr ⟨hrs, rfl⟩) hx hy
  -- distinctness of non-apex elements from different pencil rows
  have hcross : ∀ {r s : ι} {x y : ClassFunction G ℂ}, r ≠ s → χ ∈ A r j₀ → χ ∈ A s j₀ →
      x ∈ A r j₀ → y ∈ A s j₀ → x ≠ χ → x ≠ y := by
    intro r s x y hrs hχr hχs hx hy hxχ hxy
    exact hxχ (eq_of_mem_Llinked hG (Or.inr ⟨hrs, rfl⟩) hχr hχs hx (by rw [hxy]; exact hy))
  have hfa_mb : fa ≠ mb := hcross hab hχLa hχLb hfaLa hmbLb dχfa.symm
  -- ===== (3.5.4.4): the active cell `B₂ = A rb j₁` =====
  have hχ_nB2 : χ ∉ A rb j₁ := by
    intro hχB2
    have hpc : A rb j₁ = {χ, -fa, -fc} := pencilCell hG hab.symm hbc hbt hac hj hLb hLa hLc
      (by rw [hT]; ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto) hχB2
    refine not_disjoint_Llinked hG (Or.inr ⟨hab.symm, rfl⟩) hpc hB1 ?_ ?_ ?_
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨dχma, hnn hχLb hmbLb, dχfb⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨(hnn hmaLa hfaLa).symm, neg_injective.ne hfa_mb, (hnn hfbLb hfaLa).symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨(hnn hmaLa hfcLc).symm,
        neg_injective.ne (hcross hbc.symm hχLc hχLb hfcLc hmbLb dχfc.symm),
        (hnn hfbLb hfcLc).symm⟩
  have hmb_nB2 : mb ∉ A rb j₁ := by
    have h := hG.noNeg_L ra rb j₁ j₁ (Or.inr ⟨hab, rfl⟩) (-mb) hnegmbB1
    rwa [neg_neg] at h
  have hfbB2 : fb ∈ A rb j₁ :=
    lStep_third hG (Or.inl ⟨rfl, hj.symm⟩) hLb dχmb dχfb dmbfb hχ_nB2 hmb_nB2
  have hma_nB2 : ma ∉ A rb j₁ := fun hmaB2 =>
    not_two_shared hG (Or.inr ⟨hab.symm, rfl⟩) hfbB2 hfbB1 hmaB2 hmaB1
      (hcross hab.symm hχLb hχLa hfbLb hmaLa dχfb.symm)
  have hnegfa_nB2 : -fa ∉ A rb j₁ := by
    intro hnfa
    have hfaB2 : fa ∈ A rb j₁ := by
      have hO := hG.inter_O rb ra j₁ j₀ hab.symm hj.symm
      rw [hLa, card_inter_triple _ dχma dχfa dmafa, card_filter_neg_triple _ dχma dχfa dmafa,
        if_neg hχ_nB2, if_neg hma_nB2, if_pos hnfa] at hO
      by_contra h; rw [if_neg h] at hO; omega
    exact hG.neg_not_mem_self hfaB2 hnfa
  have hχ8B2 : χ8 ∈ A rb j₁ :=
    lStep_third hG (Or.inr ⟨hbt, rfl⟩) hB3 dma_negfa dma_χ8 dnegfa_χ8 hma_nB2 hnegfa_nB2
  -- ===== (3.5.4.5): the passive cell `B₄ = A rc j₁` =====
  have hχ_nB4 : χ ∉ A rc j₁ := by
    intro hχB4
    have hpc : A rc j₁ = {χ, -fa, -fb} := pencilCell hG hac.symm hbc.symm hct hab hj hLc hLa hLb
      (by rw [hT]; ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto) hχB4
    refine not_disjoint_Llinked hG (Or.inr ⟨hac.symm, rfl⟩) hpc hB1 ?_ ?_ ?_
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨dχma, hnn hχLb hmbLb, dχfb⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨(hnn hmaLa hfaLa).symm, neg_injective.ne hfa_mb, (hnn hfbLb hfaLa).symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨(hnn hmaLa hfbLb).symm, neg_injective.ne dmbfb.symm, (hnn hfbLb hfbLb).symm⟩
  have hnegχ_nB4 : -χ ∉ A rc j₁ := hG.noNeg_L rc rc j₀ j₁ (Or.inl ⟨rfl, hj⟩) χ hχLc
  have hma_nB4 : ma ∉ A rc j₁ := by
    intro hma
    have hnegfaB4 : -fa ∈ A rc j₁ := by
      have hO := hG.inter_O rc ra j₁ j₀ hac.symm hj.symm
      rw [hLa, card_inter_triple _ dχma dχfa dmafa, card_filter_neg_triple _ dχma dχfa dmafa,
        if_neg hχ_nB4, if_pos hma, if_neg hnegχ_nB4, if_neg (hG.neg_not_mem_self hma)] at hO
      by_contra h; rw [if_neg h] at hO; omega
    exact not_two_shared hG (Or.inr ⟨hct, rfl⟩) hma hmaB3 hnegfaB4 hnegfaB3 dma_negfa
  have hnegfa_nB4 : -fa ∉ A rc j₁ := by
    intro hnfa
    have hmaB4 : ma ∈ A rc j₁ := by
      have hO := hG.inter_O rc ra j₁ j₀ hac.symm hj.symm
      rw [hLa, card_inter_triple _ dχma dχfa dmafa, card_filter_neg_triple _ dχma dχfa dmafa,
        if_neg hχ_nB4, if_neg (fun hfa => hG.neg_not_mem_self hfa hnfa), if_neg hnegχ_nB4,
        if_pos hnfa] at hO
      by_contra h; rw [if_neg h] at hO; omega
    exact hma_nB4 hmaB4
  have hχ8B4 : χ8 ∈ A rc j₁ :=
    lStep_third hG (Or.inr ⟨hct, rfl⟩) hB3 dma_negfa dma_χ8 dnegfa_χ8 hma_nB4 hnegfa_nB4
  have hfb_nB4 : fb ∉ A rc j₁ := fun hfbB4 =>
    not_two_shared hG (Or.inr ⟨hbc.symm, rfl⟩) hχ8B4 hχ8B2 hfbB4 hfbB2 hχ8fb
  have hnegmbB4 : -mb ∈ A rc j₁ := by
    have hB1' : A ra j₁ = {ma, fb, -mb} := by
      rw [hB1]; ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    exact lStep_third hG (Or.inr ⟨hac.symm, rfl⟩) hB1' dma_fb dma_negmb dnegmb_fb.symm
      hma_nB4 hfb_nB4
  have hO := hG.inter_O rc rb j₁ j₀ hbc.symm hj.symm
  rw [hLb, card_inter_triple _ dχmb dχfb dmbfb, card_filter_neg_triple _ dχmb dχfb dmbfb,
    if_neg hχ_nB4, if_neg hfb_nB4, if_pos hnegmbB4] at hO
  have hmbB4 : mb ∈ A rc j₁ := by by_contra h; rw [if_neg h] at hO; omega
  exact hG.neg_not_mem_self hmbB4 hnegmbB4

open scoped Classical in
/-- A 3-element cell containing three pairwise-distinct elements is exactly that triple. -/
theorem cell_eq_triple (hG : IsSignedTripleGrid A) {i : ι} {j : κ} {x y z : ClassFunction G ℂ}
    (hx : x ∈ A i j) (hy : y ∈ A i j) (hz : z ∈ A i j) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    A i j = {x, y, z} := by
  classical
  have hsub : ({x, y, z} : Finset (ClassFunction G ℂ)) ⊆ A i j := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact hx
    · exact hy
    · exact hz
  have hc3 : ({x, y, z} : Finset (ClassFunction G ℂ)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hxy, hxz]),
      Finset.card_insert_of_notMem (by simp [hyz]), Finset.card_singleton]
  exact (Finset.eq_of_subset_of_card_le hsub (le_of_eq (by rw [hG.card_eq_three i j, hc3]))).symm

open scoped Classical in
/-- **(3.5.4.3) + glue**: if the transversal `j₁`-cell shares the meet `ma` of the special pencil
row `ra`, Case I is impossible.  After `transversalCell`, the special cell is pinned to
`B₁ = A ra j₁`: `χ ∉ B₁` (`pencilCell` ⊥ `B₃`), `fa ∉ B₁` (`noNeg(B₃,B₁)`), so `ma ∈ B₁`; then `O`
against the transversal gives exactly one of `-mb, -mc ∈ B₁`, naming the *active* row.  Each branch
fills `B₁ = {ma, -m_act, f_act}` (`oStep_force`) and dispatches to `caseI_tail` with the active and
passive rows assigned.  (The whole argument is symmetric in the two non-special rows.) -/
theorem caseI_special (hG : IsSignedTripleGrid A) {ra rb rc rt : ι} {j₀ j₁ : κ}
    (hab : ra ≠ rb) (hac : ra ≠ rc) (hbc : rb ≠ rc)
    (hat : ra ≠ rt) (hbt : rb ≠ rt) (hct : rc ≠ rt) (hj : j₀ ≠ j₁)
    {χ ma mb mc fa fb fc : ClassFunction G ℂ}
    (hLa : A ra j₀ = {χ, ma, fa}) (hLb : A rb j₀ = {χ, mb, fb})
    (hLc : A rc j₀ = {χ, mc, fc}) (hT : A rt j₀ = {ma, mb, mc})
    (hmaB : ma ∈ A rt j₁) : False := by
  classical
  obtain ⟨χ8, hB3, hχ8χ, hχ8fb, hχ8fc, hχ8nfb, hχ8nfc, hχ8nmb, hχ8nmc⟩ :=
    transversalCell hG hab hac hbc hat hbt hct hj hLa hLb hLc hT hmaB
  obtain ⟨dχma, dχfa, dmafa⟩ := triple_distinct (hLa ▸ hG.card_eq_three ra j₀)
  obtain ⟨dχmb, dχfb, dmbfb⟩ := triple_distinct (hLb ▸ hG.card_eq_three rb j₀)
  obtain ⟨dχmc, dχfc, dmcfc⟩ := triple_distinct (hLc ▸ hG.card_eq_three rc j₀)
  obtain ⟨dmamb, dmamc, dmbmc⟩ := triple_distinct (hT ▸ hG.card_eq_three rt j₀)
  have hχLa : χ ∈ A ra j₀ := by rw [hLa]; exact Finset.mem_insert_self _ _
  have hmaLa : ma ∈ A ra j₀ := by
    rw [hLa]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hfaLa : fa ∈ A ra j₀ := by
    rw [hLa]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_singleton_self _))
  have hχLb : χ ∈ A rb j₀ := by rw [hLb]; exact Finset.mem_insert_self _ _
  have hmbLb : mb ∈ A rb j₀ := by
    rw [hLb]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hfbLb : fb ∈ A rb j₀ := by
    rw [hLb]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_singleton_self _))
  have hχLc : χ ∈ A rc j₀ := by rw [hLc]; exact Finset.mem_insert_self _ _
  have hmcLc : mc ∈ A rc j₀ := by
    rw [hLc]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hfcLc : fc ∈ A rc j₀ := by
    rw [hLc]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_singleton_self _))
  have hnn : ∀ {r s : ι} {x y : ClassFunction G ℂ}, x ∈ A r j₀ → y ∈ A s j₀ → x ≠ -y := by
    intro r s x y hx hy
    by_cases hrs : r = s
    · subst hrs; exact ne_neg_of_mem_same hG hx hy
    · exact ne_neg_of_Llinked hG (Or.inr ⟨hrs, rfl⟩) hx hy
  have hcross : ∀ {r s : ι} {x y : ClassFunction G ℂ}, r ≠ s → χ ∈ A r j₀ → χ ∈ A s j₀ →
      x ∈ A r j₀ → y ∈ A s j₀ → x ≠ χ → x ≠ y := by
    intro r s x y hrs hχr hχs hx hy hxχ hxy
    exact hxχ (eq_of_mem_Llinked hG (Or.inr ⟨hrs, rfl⟩) hχr hχs hx (by rw [hxy]; exact hy))
  have hnegfaB3 : -fa ∈ A rt j₁ := by
    rw [hB3]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  -- `χ ∉ B₁`
  have hχ_nB1 : χ ∉ A ra j₁ := by
    intro hχB1
    have hpc : A ra j₁ = {χ, -fb, -fc} := pencilCell hG hab hac hat hbc hj hLa hLb hLc hT hχB1
    refine not_disjoint_Llinked hG (Or.inr ⟨hat, rfl⟩) hpc hB3 ?_ ?_ ?_
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨dχma, hnn hχLa hfaLa, hχ8χ.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨(hnn hmaLa hfbLb).symm,
        neg_injective.ne (hcross hab.symm hχLb hχLa hfbLb hfaLa dχfb.symm), hχ8nfb.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨(hnn hmaLa hfcLc).symm,
        neg_injective.ne (hcross hac.symm hχLc hχLa hfcLc hfaLa dχfc.symm), hχ8nfc.symm⟩
  -- `fa ∉ B₁`, hence `ma ∈ B₁`
  have hfa_nB1 : fa ∉ A ra j₁ := by
    have h := hG.noNeg_L rt ra j₁ j₁ (Or.inr ⟨hat.symm, rfl⟩) (-fa) hnegfaB3
    rwa [neg_neg] at h
  have hLa' : A ra j₀ = {χ, fa, ma} := by rw [hLa, Finset.pair_comm]
  have hmaB1 : ma ∈ A ra j₁ :=
    lStep_third hG (Or.inl ⟨rfl, hj.symm⟩) hLa' dχfa dχma dmafa.symm hχ_nB1 hfa_nB1
  have hnegma_nB1 : -ma ∉ A ra j₁ := hG.noNeg_L ra ra j₀ j₁ (Or.inl ⟨rfl, hj⟩) ma hmaLa
  obtain ⟨hmb_nB1, hmc_nB1, hxor⟩ := oStep hG hat hj.symm hT dmamb dmamc dmbmc hmaB1 hnegma_nB1
  by_cases hmbB1 : -mb ∈ A ra j₁
  · have hLb' : A rb j₀ = {mb, χ, fb} := by rw [hLb, Finset.insert_comm]
    have hfbB1 : fb ∈ A ra j₁ :=
      oStep_force hG hab hj.symm hLb' dχmb.symm dmbfb dχfb hmb_nB1 hχ_nB1 hmbB1
    have hB1 : A ra j₁ = {ma, -mb, fb} := cell_eq_triple hG hmaB1 hmbB1 hfbB1
      (hnn hmaLa hmbLb) (hcross hab hχLa hχLb hmaLa hfbLb dχma.symm) (hnn hfbLb hmbLb).symm
    exact caseI_tail hG hab hac hbc hat hbt hct hj hLa hLb hLc hT hB3 hB1 hχ8fb hχ8nmb
  · have hmcB1 : -mc ∈ A ra j₁ := by by_contra h; exact hmbB1 (hxor.mpr h)
    have hLc' : A rc j₀ = {mc, χ, fc} := by rw [hLc, Finset.insert_comm]
    have hfcB1 : fc ∈ A ra j₁ :=
      oStep_force hG hac hj.symm hLc' dχmc.symm dmcfc dχfc hmc_nB1 hχ_nB1 hmcB1
    have hB1 : A ra j₁ = {ma, -mc, fc} := cell_eq_triple hG hmaB1 hmcB1 hfcB1
      (hnn hmaLa hmcLc) (hcross hac hχLa hχLc hmaLa hfcLc dχma.symm) (hnn hfcLc hmcLc).symm
    have hT' : A rt j₀ = {ma, mc, mb} := by rw [hT, Finset.pair_comm]
    exact caseI_tail hG hac hab hbc.symm hat hct hbt hj hLa hLc hLb hT' hB3 hB1 hχ8fc hχ8nmc

open scoped Classical in
/-- **(3.5.4) Case I is impossible**: the full pencil configuration (apex `χ` shared by rows
`ra, rb, rc`, transversal `rt` with `A rt j₀ = {ma, mb, mc}`).  The transversal's `j₁`-cell shares
exactly one of `ma, mb, mc` (an `L`-relation), naming the special row; dispatch to `caseI_special`
with that row in the lead (the configuration is symmetric in the three pencil rows). -/
theorem caseI_false (hG : IsSignedTripleGrid A) {ra rb rc rt : ι} {j₀ j₁ : κ}
    (hab : ra ≠ rb) (hac : ra ≠ rc) (hbc : rb ≠ rc)
    (hat : ra ≠ rt) (hbt : rb ≠ rt) (hct : rc ≠ rt) (hj : j₀ ≠ j₁)
    {χ ma mb mc fa fb fc : ClassFunction G ℂ}
    (hLa : A ra j₀ = {χ, ma, fa}) (hLb : A rb j₀ = {χ, mb, fb})
    (hLc : A rc j₀ = {χ, mc, fc}) (hT : A rt j₀ = {ma, mb, mc}) : False := by
  classical
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp (hG.inter_L rt rt j₁ j₀ (Or.inl ⟨rfl, hj.symm⟩))
  obtain ⟨hwB, hwT⟩ := Finset.mem_inter.mp (hw ▸ Finset.mem_singleton_self w)
  rw [hT] at hwT
  simp only [Finset.mem_insert, Finset.mem_singleton] at hwT
  rcases hwT with rfl | rfl | rfl
  · exact caseI_special hG hab hac hbc hat hbt hct hj hLa hLb hLc hT hwB
  · exact caseI_special hG hab.symm hbc hac hbt hat hct hj hLb hLa hLc
      (by rw [hT, Finset.insert_comm]) hwB
  · refine caseI_special hG hac.symm hbc.symm hab hct hat hbt hj hLc hLa hLb ?_ hwB
    rw [hT]; ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto

open scoped Classical in
/-- **(3.5.4)**, existence half: with at least four rows and a second column `j₁ ≠ j₀`, some element
is common to every `A i j₀`.  If not, three rows form a triangle (`exists_namedTriangle`); a fourth
row's `j₀`-cell either hits a vertex of the triangle (Case I — `caseI_false`, three sub-cases by
which vertex) or hits none, so equals the three "third" elements (Case II — `caseII_false`).  With
`common_unique`, this gives `|⋂ᵢ A i j₀| = 1`. -/
theorem exists_common [Fintype ι] (hG : IsSignedTripleGrid A) (hι : 4 ≤ Fintype.card ι)
    {j₀ j₁ : κ} (hjne : j₀ ≠ j₁) : ∃ z, ∀ i, z ∈ A i j₀ := by
  classical
  by_contra hno
  obtain ⟨i₁, i₂, i₃, h12, h13, h23, hnoc⟩ :=
    exists_triangle_of_not_exists_common hG (by omega) j₀ hno
  obtain ⟨e12, e13, e23, t1, t2, t3, hS1, hS2, hS3, d1213, d1223, d1323⟩ :=
    exists_namedTriangle hG h12 h13 h23 hnoc
  obtain ⟨i₄, hi4⟩ : ∃ i₄, i₄ ∉ ({i₁, i₂, i₃} : Finset ι) := by
    have hb : ({i₁, i₂, i₃} : Finset ι).card ≤ 3 := by
      have hb1 := Finset.card_insert_le i₁ ({i₂, i₃} : Finset ι)
      have hb2 := Finset.card_insert_le i₂ ({i₃} : Finset ι)
      simp only [Finset.card_singleton] at hb1 hb2; omega
    by_contra hcon; push Not at hcon
    have hle : (Finset.univ : Finset ι).card ≤ ({i₁, i₂, i₃} : Finset ι).card :=
      Finset.card_le_card (fun x _ => hcon x)
    rw [Finset.card_univ] at hle; omega
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi4
  obtain ⟨h41, h42, h43⟩ := hi4
  obtain ⟨_, de12t1, de13t1⟩ := triple_distinct (hS1 ▸ hG.card_eq_three i₁ j₀)
  obtain ⟨_, de12t2, de23t2⟩ := triple_distinct (hS2 ▸ hG.card_eq_three i₂ j₀)
  obtain ⟨_, de13t3, de23t3⟩ := triple_distinct (hS3 ▸ hG.card_eq_three i₃ j₀)
  have he12_1 : e12 ∈ A i₁ j₀ := by rw [hS1]; exact Finset.mem_insert_self _ _
  have he12_2 : e12 ∈ A i₂ j₀ := by rw [hS2]; exact Finset.mem_insert_self _ _
  have he13_1 : e13 ∈ A i₁ j₀ := by
    rw [hS1]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have he13_3 : e13 ∈ A i₃ j₀ := by rw [hS3]; exact Finset.mem_insert_self _ _
  have he23_2 : e23 ∈ A i₂ j₀ := by
    rw [hS2]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have he23_3 : e23 ∈ A i₃ j₀ := by
    rw [hS3]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have ht1_1 : t1 ∈ A i₁ j₀ := by
    rw [hS1]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_singleton_self _))
  have ht2_2 : t2 ∈ A i₂ j₀ := by
    rw [hS2]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_singleton_self _))
  have ht3_3 : t3 ∈ A i₃ j₀ := by
    rw [hS3]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_singleton_self _))
  by_cases he12 : e12 ∈ A i₄ j₀
  · -- Case I, apex `e12`, pencil `i₁, i₂, i₄`, transversal `i₃`
    obtain ⟨hne13_4, _, _, _, _⟩ := lStep hG (Or.inr ⟨h41, rfl⟩) hS1 d1213 de12t1 de13t1 he12
    obtain ⟨hne23_4, _, _, _, _⟩ := lStep hG (Or.inr ⟨h42, rfl⟩) hS2 d1223 de12t2 de23t2 he12
    have ht3_4 : t3 ∈ A i₄ j₀ :=
      lStep_third hG (Or.inr ⟨h43, rfl⟩) hS3 d1323 de13t3 de23t3 hne13_4 hne23_4
    have he12t3 : e12 ≠ t3 := fun h =>
      d1213 (eq_of_mem_Llinked hG (Or.inr ⟨h13, rfl⟩) he13_1 he13_3 he12_1 (by rw [h]; exact ht3_3))
    obtain ⟨fc, _, _, _, hA4⟩ :=
      exists_third_of_card_three (hG.card_eq_three i₄ j₀) he12 ht3_4 he12t3
    exact caseI_false hG h12 (Ne.symm h41) (Ne.symm h42) h13 h23 h43 hjne hS1 hS2 hA4 hS3
  · by_cases he13 : e13 ∈ A i₄ j₀
    · -- Case I, apex `e13`, pencil `i₁, i₃, i₄`, transversal `i₂`
      have hS1' : A i₁ j₀ = {e13, e12, t1} := by rw [hS1, Finset.insert_comm]
      obtain ⟨hne12_4, _, _, _, _⟩ :=
        lStep hG (Or.inr ⟨h41, rfl⟩) hS1' d1213.symm de13t1 de12t1 he13
      obtain ⟨hne23_4, _, _, _, _⟩ := lStep hG (Or.inr ⟨h43, rfl⟩) hS3 d1323 de13t3 de23t3 he13
      have ht2_4 : t2 ∈ A i₄ j₀ :=
        lStep_third hG (Or.inr ⟨h42, rfl⟩) hS2 d1223 de12t2 de23t2 hne12_4 hne23_4
      have he13t2 : e13 ≠ t2 := fun h =>
        (d1213 (eq_of_mem_Llinked hG (Or.inr ⟨h12, rfl⟩) he12_1 he12_2 he13_1
          (by rw [h]; exact ht2_2)).symm)
      obtain ⟨fc, _, _, _, hA4⟩ :=
        exists_third_of_card_three (hG.card_eq_three i₄ j₀) he13 ht2_4 he13t2
      exact caseI_false hG h13 (Ne.symm h41) (Ne.symm h43) h12 h23.symm h42 hjne hS1' hS3 hA4 hS2
    · by_cases he23 : e23 ∈ A i₄ j₀
      · -- Case I, apex `e23`, pencil `i₂, i₃, i₄`, transversal `i₁`
        have hS2' : A i₂ j₀ = {e23, e12, t2} := by rw [hS2, Finset.insert_comm]
        have hS3' : A i₃ j₀ = {e23, e13, t3} := by rw [hS3, Finset.insert_comm]
        obtain ⟨hne12_4, _, _, _, _⟩ :=
          lStep hG (Or.inr ⟨h42, rfl⟩) hS2' d1223.symm de23t2 de12t2 he23
        obtain ⟨hne13_4, _, _, _, _⟩ :=
          lStep hG (Or.inr ⟨h43, rfl⟩) hS3' d1323.symm de23t3 de13t3 he23
        have ht1_4 : t1 ∈ A i₄ j₀ :=
          lStep_third hG (Or.inr ⟨h41, rfl⟩) hS1 d1213 de12t1 de13t1 hne12_4 hne13_4
        have he23t1 : e23 ≠ t1 := fun h =>
          d1223 (eq_of_mem_Llinked hG (Or.inr ⟨h12, rfl⟩) he12_1 he12_2
            (by rw [h]; exact ht1_1) he23_2).symm
        obtain ⟨fc, _, _, _, hA4⟩ :=
          exists_third_of_card_three (hG.card_eq_three i₄ j₀) he23 ht1_4 he23t1
        exact caseI_false hG h23 (Ne.symm h42) (Ne.symm h43) h12.symm h13.symm h41 hjne hS2' hS3'
          hA4 hS1
      · -- Case II: the fourth cell is the three "third" elements
        have ht1_4 : t1 ∈ A i₄ j₀ :=
          lStep_third hG (Or.inr ⟨h41, rfl⟩) hS1 d1213 de12t1 de13t1 he12 he13
        have ht2_4 : t2 ∈ A i₄ j₀ :=
          lStep_third hG (Or.inr ⟨h42, rfl⟩) hS2 d1223 de12t2 de23t2 he12 he23
        have ht3_4 : t3 ∈ A i₄ j₀ :=
          lStep_third hG (Or.inr ⟨h43, rfl⟩) hS3 d1323 de13t3 de23t3 he13 he23
        have ht1t2 : t1 ≠ t2 := fun h =>
          de12t1 (eq_of_mem_Llinked hG (Or.inr ⟨h12, rfl⟩) he12_1 he12_2 ht1_1
            (by rw [h]; exact ht2_2)).symm
        have ht1t3 : t1 ≠ t3 := fun h =>
          de13t1 (eq_of_mem_Llinked hG (Or.inr ⟨h13, rfl⟩) he13_1 he13_3 ht1_1
            (by rw [h]; exact ht3_3)).symm
        have ht2t3 : t2 ≠ t3 := fun h =>
          de23t2 (eq_of_mem_Llinked hG (Or.inr ⟨h23, rfl⟩) he23_2 he23_3 ht2_2
            (by rw [h]; exact ht3_3)).symm
        have hA4 : A i₄ j₀ = {t1, t2, t3} := cell_eq_triple hG ht1_4 ht2_4 ht3_4 ht1t2 ht1t3 ht2t3
        exact caseII_false hG hjne.symm h12 h13 (Ne.symm h41) hS1 hS2 hS3 hA4

/-- **Peterfalvi (3.5.4)**: `|⋂_{1 ≤ i < w₁} A_{i1}| = 1` (abstract form).  With at least four rows
and a second column, exactly one element lies in every `A i j₀`.  Combines the existence half
`exists_common` (the sunflower argument: triangle + Cases I/II) with the uniqueness half
`common_unique` (two such share `A i₁ j₀ ∩ A i₂ j₀`, a singleton). -/
theorem existsUnique_common [Fintype ι] (hG : IsSignedTripleGrid A) (hι : 4 ≤ Fintype.card ι)
    {j₀ j₁ : κ} (hjne : j₀ ≠ j₁) : ∃! z, ∀ i, z ∈ A i j₀ := by
  obtain ⟨z, hz⟩ := exists_common hG hι hjne
  exact ⟨z, hz, fun z' hz' => common_unique hG (by omega) hz' hz⟩

open scoped Classical in
/-- **(3.5.5) core**: the element `z` common to every `A i j₀` is orthogonal to every other column
— neither `z` nor `-z` lies in any `A r j₁` (`j₁ ≠ j₀`).  Peterfalvi: "`χ₀₁` is orthogonal to
`A_{i2}`".  If `±z ∈ A r j₁`, then for each of the `≥ 3` other rows `i ≠ r` the `O`-relation
`O(r j₁, i j₀)` forces a member of `A r j₁` tied to `A i j₀` and distinct from `±z`; these are
pairwise distinct (a shared one would be the common `z`), giving an injection of the `≥ 4` rows
into the 3-element `A r j₁` — impossible. -/
theorem common_not_mem_other_column [Fintype ι] (hG : IsSignedTripleGrid A)
    (hι : 4 ≤ Fintype.card ι) {j₀ j₁ : κ} (hjne : j₀ ≠ j₁) {z : ClassFunction G ℂ}
    (hz : ∀ i, z ∈ A i j₀) (r : ι) : z ∉ A r j₁ ∧ -z ∉ A r j₁ := by
  classical
  -- injection engine: a `w ∈ A r j₁` plus an injective `Y : (· ≠ r) → A r j₁ ∖ {w}` is impossible
  have engine : ∀ (w : ClassFunction G ℂ) (Y : ι → ClassFunction G ℂ), w ∈ A r j₁ →
      (∀ i, i ≠ r → Y i ∈ A r j₁) → (∀ i, i ≠ r → Y i ≠ w) →
      (∀ i, i ≠ r → ∀ i', i' ≠ r → Y i = Y i' → i = i') → False := by
    intro w Y hwB hYmem hYne hYinj
    have hsub : insert w (Finset.image Y (Finset.univ.erase r)) ⊆ A r j₁ := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_image] at hx
      rcases hx with rfl | ⟨i, hi, rfl⟩
      · exact hwB
      · exact hYmem i (Finset.mem_erase.mp hi).1
    have hwnot : w ∉ Finset.image Y (Finset.univ.erase r) := by
      rw [Finset.mem_image]; rintro ⟨i, hi, hYi⟩
      exact hYne i (Finset.mem_erase.mp hi).1 hYi
    have hinj : Set.InjOn Y (Finset.univ.erase r : Finset ι) := by
      intro i hi i' hi' h
      exact hYinj i (Finset.mem_erase.mp hi).1 i' (Finset.mem_erase.mp hi').1 h
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hwnot, Finset.card_image_of_injOn hinj,
      Finset.card_erase_of_mem (Finset.mem_univ r), Finset.card_univ,
      Nat.sub_add_cancel (by omega), hG.card_eq_three r j₁] at hcard
    omega
  refine ⟨fun hzB => ?_, fun hzB => ?_⟩
  · -- `z ∈ A r j₁`: each `i ≠ r` gives `y` with `-y ∈ A i j₀`, `y ≠ z`
    have hex : ∀ i, i ≠ r → ∃ y, y ∈ A r j₁ ∧ -y ∈ A i j₀ ∧ y ≠ z := by
      intro i hir
      have hpos : 0 < (A r j₁ ∩ A i j₀).card :=
        Finset.card_pos.mpr ⟨z, Finset.mem_inter.mpr ⟨hzB, hz i⟩⟩
      rw [hG.inter_O r i j₁ j₀ hir.symm hjne.symm] at hpos
      obtain ⟨y, hyf⟩ := Finset.card_pos.mp hpos
      rw [Finset.mem_filter] at hyf
      exact ⟨y, hyf.1, hyf.2, fun hyz => hG.neg_not_mem_self (hz i) (hyz ▸ hyf.2)⟩
    choose! Y hYmem hYneg hYne using hex
    refine engine z Y hzB hYmem hYne (fun i hir i' hir' hYY => ?_)
    by_contra hne
    have heq : -Y i = z := eq_of_mem_Llinked hG (Or.inr ⟨hne, rfl⟩) (hz i) (hz i')
      (hYneg i hir) (hYY.symm ▸ hYneg i' hir')
    exact hG.neg_not_mem_self hzB (by rw [← heq, neg_neg]; exact hYmem i hir)
  · -- `-z ∈ A r j₁`: each `i ≠ r` gives `y` with `y ∈ A i j₀`, `y ≠ -z`
    have hex : ∀ i, i ≠ r → ∃ y, y ∈ A r j₁ ∧ y ∈ A i j₀ ∧ y ≠ -z := by
      intro i hir
      have hpos : 0 < (A r j₁ |>.filter (fun x => -x ∈ A i j₀)).card :=
        Finset.card_pos.mpr ⟨-z, Finset.mem_filter.mpr ⟨hzB, by rw [neg_neg]; exact hz i⟩⟩
      rw [← hG.inter_O r i j₁ j₀ hir.symm hjne.symm] at hpos
      obtain ⟨y, hyf⟩ := Finset.card_pos.mp hpos
      rw [Finset.mem_inter] at hyf
      exact ⟨y, hyf.1, hyf.2, fun hyz => hG.neg_not_mem_self (hz i) (hyz ▸ hyf.2)⟩
    choose! Y hYmem hYpos hYne using hex
    refine engine (-z) Y hzB hYmem hYne (fun i hir i' hir' hYY => ?_)
    by_contra hne
    have heq : Y i = z := eq_of_mem_Llinked hG (Or.inr ⟨hne, rfl⟩) (hz i) (hz i')
      (hYpos i hir) (hYY.symm ▸ hYpos i' hir')
    exact hG.neg_not_mem_self hzB (by rw [neg_neg]; exact heq ▸ hYmem i hir)

open scoped Classical in
/-- **(3.5.5) cell decomposition**: with `≥ 4` rows and two distinct columns `j₀ ≠ j₁`, let `z₀` be
the element common to every `A i j₀` (`existsUnique_common`).  Then each cell `A i j₀` splits as
`{z₀, m, φ}` where `m` is the (unique) element of the same-row meet `A i j₀ ∩ A i j₁` and `φ` is the
remaining "third" element; the three are pairwise distinct and `φ ∉ A i j₁`.  This is Peterfalvi's
`β_{i1} = -χ_{i0} - χ_{01} + χ_{i1}` read off the set `A_{i1} = {-χ_{01}, -χ_{i0}, χ_{i1}}`
(`z₀ = -χ₀₁`, `m = -χ_{i0}`, `φ = χ_{i1}`).  `z₀ ≠ m` because `z₀ ∉ A i j₁` (`common_not_mem_other
_column`) while `m ∈ A i j₁`. -/
theorem cell_decomposition [Fintype ι] (hG : IsSignedTripleGrid A) (hι : 4 ≤ Fintype.card ι)
    {j₀ j₁ : κ} (hjne : j₀ ≠ j₁) {z₀ : ClassFunction G ℂ} (hz₀ : ∀ i, z₀ ∈ A i j₀) (i : ι) :
    ∃ m φ : ClassFunction G ℂ, A i j₀ = {z₀, m, φ} ∧ m ∈ A i j₁ ∧ φ ∉ A i j₁ ∧
      z₀ ≠ m ∧ z₀ ≠ φ ∧ m ≠ φ := by
  classical
  -- the same-row meet `A i j₀ ∩ A i j₁` is a singleton `{m}` (`L(i j₀, i j₁)`)
  obtain ⟨m, hm⟩ := Finset.card_eq_one.mp (hG.inter_L i i j₀ j₁ (Or.inl ⟨rfl, hjne⟩))
  obtain ⟨hmj₀, hmj₁⟩ := Finset.mem_inter.mp (hm ▸ Finset.mem_singleton_self m)
  -- `z₀ ≠ m`: `z₀` is orthogonal to the other column, but `m` lies in it
  have hz₀notj₁ := (hG.common_not_mem_other_column hι hjne hz₀ i).1
  have hzm : z₀ ≠ m := fun h => hz₀notj₁ (h ▸ hmj₁)
  -- the third element `φ`
  obtain ⟨φ, hφmem, hφz, hφm, hset⟩ :=
    exists_third_of_card_three (hG.card_eq_three i j₀) (hz₀ i) hmj₀ hzm
  -- `φ ∉ A i j₁`: else `φ ∈ A i j₀ ∩ A i j₁ = {m}`, so `φ = m`
  have hφnotj₁ : φ ∉ A i j₁ := fun h =>
    hφm (eq_of_mem_Llinked hG (Or.inl ⟨rfl, hjne⟩) hmj₀ hmj₁ hφmem h)
  exact ⟨m, φ, hset, hmj₁, hφnotj₁, hzm, Ne.symm hφz, Ne.symm hφm⟩

/-- **(3.5.5) orthogonality core**: the element `z` common to every `A · j` is orthogonal to every
member `y` of any *other* column `A i l` (`l ≠ j`): `z ≠ y` and `z ≠ -y`.  Both `z ∉ A i l` and
`-z ∉ A i l` hold (`common_not_mem_other_column`), so neither `y` nor `-y` can equal `z`.  This is
the workhorse for the orthogonality of the column characters `χ_{0j}` to the row characters
`χ_{i0}` and the interior characters `χ_{ij}` (`j ≠ l`). -/
theorem common_ne_other_column_mem [Fintype ι] (hG : IsSignedTripleGrid A)
    (hι : 4 ≤ Fintype.card ι) {i : ι} {j l : κ} (hjl : j ≠ l) {z y : ClassFunction G ℂ}
    (hz : ∀ i', z ∈ A i' j) (hy : y ∈ A i l) : z ≠ y ∧ z ≠ -y := by
  obtain ⟨h1, h2⟩ := hG.common_not_mem_other_column hι hjl hz i
  exact ⟨fun h => h1 (h ▸ hy), fun h => h2 (by rw [h, neg_neg]; exact hy)⟩

open scoped Classical in
/-- **(3.5.5) symmetric cell decomposition**: with `≥ 4` rows and `≥ 2` columns, a cell `A i j`
containing both its column-common element `zc` (in every `A · j`) and its row-common element `wr`
(in every `A i ·`) splits as `{zc, wr, φ}` with the three pairwise distinct.  `zc ≠ wr` because
`zc` lies outside every other column (`common_not_mem_other_column`) while `wr`, being row-common,
lies in some other column.  This is the `w₂ ≥ 5` form, where `zc = -χ_{0j}`, `wr = -χ_{i0}`,
`φ = χ_{ij}`. -/
theorem symm_cell_decomposition [Fintype ι] [Fintype κ] (hG : IsSignedTripleGrid A)
    (hι : 4 ≤ Fintype.card ι) (hκ : 2 ≤ Fintype.card κ) {i : ι} {j : κ}
    {zc wr : ClassFunction G ℂ} (hzc : ∀ i', zc ∈ A i' j) (hwr : ∀ j', wr ∈ A i j') :
    ∃ φ : ClassFunction G ℂ, A i j = {zc, wr, φ} ∧ zc ≠ wr ∧ zc ≠ φ ∧ wr ≠ φ := by
  classical
  obtain ⟨j', hj'⟩ : ∃ j' : κ, j ≠ j' := by
    have : Nontrivial κ := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨a, b, hab⟩ := exists_pair_ne κ
    rcases eq_or_ne j a with rfl | ha
    · exact ⟨b, hab⟩
    · exact ⟨a, ha⟩
  have hzw : zc ≠ wr := (hG.common_ne_other_column_mem hι hj' hzc (hwr j')).1
  obtain ⟨φ, _, hφz, hφw, hset⟩ :=
    exists_third_of_card_three (hG.card_eq_three i j) (hzc i) (hwr j) hzw
  exact ⟨φ, hset, hzw, Ne.symm hφz, Ne.symm hφw⟩

/-- The **transpose** of a signed-triple grid (swap rows and columns) is again a signed-triple grid.
Used for the `W₁ ↔ W₂` interchange in the (3.5.4)/(3.5.5) WLOG `w₁ ≥ 5`: when only `w₂ ≥ 5`, apply
the row-indexed results to the transposed grid. -/
theorem transpose (hG : IsSignedTripleGrid A) :
    IsSignedTripleGrid (fun (j : κ) (i : ι) => A i j) where
  card_eq_three j i := hG.card_eq_three i j
  signed j i := hG.signed i j
  orthogonal j i := hG.orthogonal i j
  inter_L j j' i i' h := hG.inter_L i i' j j' (by tauto)
  noNeg_L j j' i i' h := hG.noNeg_L i i' j j' (by tauto)
  inter_O j j' i i' hjj hii := hG.inter_O i i' j j' hii hjj

open scoped Classical in
/-- **(3.5.5) cross-cell orthogonality of the interior characters** (the `O(ij, kl)` step): in the
symmetric regime (`≥ 4` rows and columns), if `A i j = {zj, wi, φ}` with `zj` column-`j`-common and
`wi` row-`i`-common, then for any *far* cell `A k l` (`i ≠ k`, `j ≠ l`) the third element `φ` and
its negative both lie outside `A k l`.  Indeed `zj, wi ∉ A k l` and `-zj, -wi ∉ A k l`
(`common_not_mem_other_column` for the column `j`, and via `transpose` for the row `i`), so the
`O`-relation `O(ij, kl)` forces `[φ ∈ A k l] = [-φ ∈ A k l]`, hence both `0` (`oStep_both_out`).
This makes the interior characters `χ_{ij}` pairwise orthogonal when both indices differ. -/
theorem third_not_mem_far_cell [Fintype ι] [Fintype κ] (hG : IsSignedTripleGrid A)
    (hι : 4 ≤ Fintype.card ι) (hκ : 4 ≤ Fintype.card κ) {i k : ι} {j l : κ}
    (hik : i ≠ k) (hjl : j ≠ l) {zj wi φ : ClassFunction G ℂ}
    (hzj : ∀ i', zj ∈ A i' j) (hwi : ∀ j', wi ∈ A i j')
    (hcell : A i j = {zj, wi, φ}) (hd1 : zj ≠ wi) (hd2 : zj ≠ φ) (hd3 : wi ≠ φ) :
    φ ∉ A k l ∧ -φ ∉ A k l := by
  obtain ⟨hzj1, hzj2⟩ := hG.common_not_mem_other_column hι hjl hzj k
  obtain ⟨hwi1, hwi2⟩ := hG.transpose.common_not_mem_other_column hκ hik hwi l
  exact hG.oStep_both_out (Ne.symm hik) (Ne.symm hjl) hcell hd1 hd2 hd3 hzj1 hwi1 hzj2 hwi2

/-- The row-analogue of `common_ne_other_column_mem` (via `transpose`): an element `wr` common to
every cell of row `i` is orthogonal to every member `y` of any *other* row `A k j` (`k ≠ i`). -/
theorem common_ne_other_row_mem [Fintype κ] (hG : IsSignedTripleGrid A)
    (hκ : 4 ≤ Fintype.card κ) {i k : ι} {j : κ} (hik : i ≠ k) {wr y : ClassFunction G ℂ}
    (hwr : ∀ j', wr ∈ A i j') (hy : y ∈ A k j) : wr ≠ y ∧ wr ≠ -y :=
  hG.transpose.common_ne_other_column_mem hκ hik hwr hy

/-- The **combined character family** of a signed-triple grid: row-anchors `m i`, column-anchors
`z c` (indexed by a general `γ`), and interior thirds `φ i c`, packaged as a single family indexed
by `ι ⊕ γ ⊕ ι × γ`.  These are the `χ_{i0}`, `χ_{0j}`, `χ_{ij}` of Peterfalvi (3.5) (up to sign —
all but `χ_{00} = 1_G`).  Used with `γ = κ` (`w₂ ≥ 5`) and `γ = Bool` (`w₂ = 3`). -/
def gridFamily {γ : Type*} (z : γ → ClassFunction G ℂ) (m : ι → ClassFunction G ℂ)
    (φ : ι → γ → ClassFunction G ℂ) : ι ⊕ γ ⊕ (ι × γ) → ClassFunction G ℂ
  | Sum.inl i => m i
  | Sum.inr (Sum.inl c) => z c
  | Sum.inr (Sum.inr ⟨i, c⟩) => φ i c

/-- **Assembly of orthonormality** from the pairwise combinatorial relations: if the row-anchors
`m`, column-anchors `z`, and interior thirds `φ` are signed nontrivial irreducibles satisfying the
six pairwise `≠`/`≠ -` relations (`Rmm`, `Rzz`, `Rzm`, `Rzφ`, `Rmφ`, `Rφφ`), then `gridFamily z m φ`
is orthonormal (diagonal `1`, off-diagonal `0`).  Shared by the `w₂ ≥ 5` (`symm_orthonormal_family`)
and `w₂ = 3` (`two_col_orthonormal_family`) cases — they differ only in how the row-anchor relations
`Rmm`/`Rmφ` are established (row-common vs row-meet). -/
theorem gridFamily_orthonormal {γ : Type*} (z : γ → ClassFunction G ℂ) (m : ι → ClassFunction G ℂ)
    (φ : ι → γ → ClassFunction G ℂ) (hsigz : ∀ c, IsSignedNontrivialIrr (z c))
    (hsigm : ∀ i, IsSignedNontrivialIrr (m i)) (hsigφ : ∀ i c, IsSignedNontrivialIrr (φ i c))
    (Rmm : ∀ i k, i ≠ k → m i ≠ m k ∧ m i ≠ -m k)
    (Rzz : ∀ c d, c ≠ d → z c ≠ z d ∧ z c ≠ -z d)
    (Rzm : ∀ i c, z c ≠ m i ∧ z c ≠ -m i)
    (Rzφ : ∀ c k d, z c ≠ φ k d ∧ z c ≠ -φ k d)
    (Rmφ : ∀ i k d, m i ≠ φ k d ∧ m i ≠ -φ k d)
    (Rφφ : ∀ i c k d, (i, c) ≠ (k, d) → φ i c ≠ φ k d ∧ φ i c ≠ -φ k d) :
    (∀ a, ClassFunction.inner (gridFamily z m φ a) (gridFamily z m φ a) = 1) ∧
      (∀ a b, a ≠ b → ClassFunction.inner (gridFamily z m φ a) (gridFamily z m φ b) = 0) := by
  have flip : ∀ {x y : ClassFunction G ℂ}, x ≠ -y → y ≠ -x := fun h hh => h (by rw [hh, neg_neg])
  have hsig : ∀ a, IsSignedNontrivialIrr (gridFamily z m φ a) := by
    rintro (i | c | ⟨i, c⟩) <;> simp only [gridFamily]
    · exact hsigm i
    · exact hsigz c
    · exact hsigφ i c
  have hinj : Function.Injective (gridFamily z m φ) := by
    rintro (i | c | ⟨i, c⟩) (k | d | ⟨k, d⟩) hab <;> simp only [gridFamily] at hab ⊢
    · by_contra hne; exact (Rmm i k (fun h => hne (by rw [h]))).1 hab
    · exact absurd hab (Ne.symm (Rzm i d).1)
    · exact absurd hab (Rmφ i k d).1
    · exact absurd hab (Rzm k c).1
    · by_contra hne; exact (Rzz c d (fun h => hne (by rw [h]))).1 hab
    · exact absurd hab (Rzφ c k d).1
    · exact absurd hab (Ne.symm (Rmφ k i c).1)
    · exact absurd hab (Ne.symm (Rzφ d i c).1)
    · by_contra hne; exact (Rφφ i c k d (fun h => hne (by rw [h]))).1 hab
  have hneg : ∀ a b, gridFamily z m φ a ≠ -gridFamily z m φ b := by
    rintro (i | c | ⟨i, c⟩) (k | d | ⟨k, d⟩) <;> simp only [gridFamily]
    · rcases eq_or_ne i k with rfl | hik
      · exact (hsigm i).ne_neg_self
      · exact (Rmm i k hik).2
    · exact flip (Rzm i d).2
    · exact (Rmφ i k d).2
    · exact (Rzm k c).2
    · rcases eq_or_ne c d with rfl | hcd
      · exact (hsigz c).ne_neg_self
      · exact (Rzz c d hcd).2
    · exact (Rzφ c k d).2
    · exact flip (Rmφ k i c).2
    · exact flip (Rzφ d i c).2
    · rcases eq_or_ne (Prod.mk i c) (Prod.mk k d) with h | h
      · obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp h
        exact (hsigφ i c).ne_neg_self
      · exact (Rφφ i c k d h).2
  exact orthonormal_of_injective_of_no_neg (gridFamily z m φ) hsig hinj hneg

open scoped Classical in
/-- **(3.5.5)/(3.5) symmetric orthonormal family** (the `w₂ ≥ 5` heart of (3.5)): a symmetric grid
(`≥ 4` rows and columns) with column-commons `z j` (in every `A · j`) and row-commons `w i` (in
every `A i ·`) admits interior thirds `φ i j` with `A i j = {z j, w i, φ i j}`, and the combined
family `(w i, z j, φ i j)` is **orthonormal** (`⟨·, ·⟩ = δ`).  Establishes the six pairwise
relations
(column-commons via `common_ne_other_column_mem`, row-commons via `common_ne_other_row_mem`,
interior
thirds via `third_not_mem_far_cell` for the far case and `L`-relations for the same row/column, plus
the cross relations) and feeds them to `gridFamily_orthonormal`. -/
theorem symm_orthonormal_family [Fintype ι] [Fintype κ] (hG : IsSignedTripleGrid A)
    (hι : 4 ≤ Fintype.card ι) (hκ : 4 ≤ Fintype.card κ)
    {z : κ → ClassFunction G ℂ} {w : ι → ClassFunction G ℂ}
    (hz : ∀ j i, z j ∈ A i j) (hw : ∀ i j, w i ∈ A i j) :
    ∃ φ : ι → κ → ClassFunction G ℂ, (∀ i j, A i j = {z j, w i, φ i j}) ∧
      ∀ a b, ClassFunction.inner (gridFamily z w φ a) (gridFamily z w φ b)
        = if a = b then 1 else 0 := by
  classical
  have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  have : Nonempty κ := Fintype.card_pos_iff.mp (by omega)
  have hcell : ∀ i j, ∃ φ, A i j = {z j, w i, φ} ∧ z j ≠ w i ∧ z j ≠ φ ∧ w i ≠ φ := fun i j =>
    hG.symm_cell_decomposition hι (by omega) (fun i' => hz j i') (fun j' => hw i j')
  choose φ hφcell hd1 hd2 hd3 using hcell
  have hφc : ∀ i j, φ i j ∈ A i j := fun i j => by
    rw [hφcell i j]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  refine ⟨φ, hφcell, ?_⟩
  have hsigz : ∀ j, IsSignedNontrivialIrr (z j) := fun j =>
    hG.signed (Classical.arbitrary ι) j _ (hz j (Classical.arbitrary ι))
  have hsigw : ∀ i, IsSignedNontrivialIrr (w i) := fun i =>
    hG.signed i (Classical.arbitrary κ) _ (hw i (Classical.arbitrary κ))
  have hsigφ : ∀ i j, IsSignedNontrivialIrr (φ i j) := fun i j => hG.signed i j _ (hφc i j)
  have Rww : ∀ i k, i ≠ k → w i ≠ w k ∧ w i ≠ -w k := fun i k hik =>
    hG.common_ne_other_row_mem hκ hik (hw i) (hw k (Classical.arbitrary κ))
  have Rzz : ∀ j l, j ≠ l → z j ≠ z l ∧ z j ≠ -z l := fun j l hjl =>
    hG.common_ne_other_column_mem hι hjl (hz j) (hz l (Classical.arbitrary ι))
  have Rzw : ∀ i j, z j ≠ w i ∧ z j ≠ -w i := fun i j =>
    ⟨hd1 i j, hG.ne_neg_of_mem_same (hz j i) (hw i j)⟩
  have Rzφ : ∀ j k l, z j ≠ φ k l ∧ z j ≠ -φ k l := fun j k l => by
    rcases eq_or_ne l j with rfl | hlj
    · exact ⟨hd2 k l, hG.ne_neg_of_mem_same (hz l k) (hφc k l)⟩
    · exact hG.common_ne_other_column_mem hι (Ne.symm hlj) (hz j) (hφc k l)
  have Rwφ : ∀ i k l, w i ≠ φ k l ∧ w i ≠ -φ k l := fun i k l => by
    rcases eq_or_ne k i with rfl | hki
    · exact ⟨hd3 k l, hG.ne_neg_of_mem_same (hw k l) (hφc k l)⟩
    · exact hG.common_ne_other_row_mem hκ (Ne.symm hki) (hw i) (hφc k l)
  have Rφφ : ∀ i j k l, (i, j) ≠ (k, l) → φ i j ≠ φ k l ∧ φ i j ≠ -φ k l := fun i j k l hne => by
    rcases eq_or_ne i k with rfl | hik
    · have hjl : j ≠ l := fun h => hne (by rw [h])
      have hnm : φ i j ∉ A i l := fun hmem =>
        Ne.symm (hd3 i j) (eq_of_mem_Llinked hG (Or.inl ⟨rfl, hjl⟩) (hw i j) (hw i l)
          (hφc i j) hmem)
      exact ⟨fun h => hnm (h ▸ hφc i l),
        hG.ne_neg_of_Llinked (Or.inl ⟨rfl, hjl⟩) (hφc i j) (hφc i l)⟩
    · rcases eq_or_ne j l with rfl | hjl
      · have hnm : φ i j ∉ A k j := fun hmem =>
          Ne.symm (hd2 i j) (eq_of_mem_Llinked hG (Or.inr ⟨hik, rfl⟩) (hz j i) (hz j k)
            (hφc i j) hmem)
        exact ⟨fun h => hnm (h ▸ hφc k j),
          hG.ne_neg_of_Llinked (Or.inr ⟨hik, rfl⟩) (hφc i j) (hφc k j)⟩
      · obtain ⟨h1, h2⟩ := hG.third_not_mem_far_cell hι hκ hik hjl (hz j) (hw i)
          (hφcell i j) (hd1 i j) (hd2 i j) (hd3 i j)
        exact ⟨fun h => h1 (h ▸ hφc k l), fun h => h2 (by rw [h, neg_neg]; exact hφc k l)⟩
  obtain ⟨hdiag, hoff⟩ :=
    gridFamily_orthonormal z w φ hsigz hsigw hsigφ Rww Rzz Rzw Rzφ Rwφ Rφφ
  intro a b
  split_ifs with hab
  · subst hab; exact hdiag a
  · exact hoff a b hab

open scoped Classical in
/-- **(3.5.5) two-column orthonormal family** (the `w₂ = 3` case of (3.5)): with `≥ 4` rows and just
two distinguished columns `j false ≠ j true` (`j` injective), each row's pair of cells shares a
single *row-meet* `m i ∈ A i (j false) ∩ A i (j true)`, giving `A i (j b) = {z b, m i, φ i b}`
(column-commons `z b`, thirds `φ i b`); the combined family `(m i, z b, φ i b)` over
`ι ⊕ Bool ⊕ ι × Bool` is orthonormal.  Here the row-anchor `m i` lies only in the two reference
columns, so its orthogonality relations come from `L` (the meet is distinct from the column-commons)
rather than from being row-common.  This is the case where Peterfalvi's (3.5) "is complete" after
(3.5.5). -/
theorem two_col_orthonormal_family [Fintype ι] (hG : IsSignedTripleGrid A)
    (hι : 4 ≤ Fintype.card ι) {j : Bool → κ} (hj : Function.Injective j)
    {z : Bool → ClassFunction G ℂ} (hz : ∀ b i, z b ∈ A i (j b)) :
    ∃ (m : ι → ClassFunction G ℂ) (φ : ι → Bool → ClassFunction G ℂ),
      (∀ i b, A i (j b) = {z b, m i, φ i b}) ∧ (∀ i b, m i ∈ A i (j b)) ∧
      ∀ a b, ClassFunction.inner (gridFamily z m φ a) (gridFamily z m φ b)
        = if a = b then 1 else 0 := by
  classical
  have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  have hjft : j false ≠ j true := hj.ne (by decide)
  -- per-row decomposition: row-meet `m i` (in both reference cells) and thirds `φ i b`
  have hdec : ∀ i, ∃ (mi : ClassFunction G ℂ) (φi : Bool → ClassFunction G ℂ),
      (∀ b, A i (j b) = {z b, mi, φi b}) ∧ (∀ b, mi ∈ A i (j b)) ∧
      (∀ b, z b ≠ mi) ∧ (∀ b, mi ≠ φi b) ∧ (∀ b, z b ≠ φi b) := by
    intro i
    obtain ⟨mi, ψf, hf, hmt, _, hzfm, hzfψf, hmψf⟩ := hG.cell_decomposition hι hjft (hz false) i
    have hmf : mi ∈ A i (j false) := by
      rw [hf]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    have hztm : z true ≠ mi := fun h =>
      (hG.common_not_mem_other_column hι (Ne.symm hjft) (hz true) i).1 (h ▸ hmf)
    obtain ⟨ψt, _, hψtz, hψtm, ht⟩ :=
      exists_third_of_card_three (hG.card_eq_three i (j true)) (hz true i) hmt hztm
    refine ⟨mi, fun b => cond b ψt ψf, ?_, ?_, ?_, ?_, ?_⟩
    · intro b; cases b
      · exact hf
      · exact ht
    · intro b; cases b
      · exact hmf
      · exact hmt
    · intro b; cases b
      · exact hzfm
      · exact hztm
    · intro b; cases b
      · exact hmψf
      · exact Ne.symm hψtm
    · intro b; cases b
      · exact hzfψf
      · exact Ne.symm hψtz
  choose m φ hcell hmem hzm hmφ hzφ using hdec
  have hφc : ∀ i b, φ i b ∈ A i (j b) := fun i b => by
    rw [hcell i b]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  refine ⟨m, φ, hcell, hmem, ?_⟩
  have hsigz : ∀ b, IsSignedNontrivialIrr (z b) := fun b =>
    hG.signed (Classical.arbitrary ι) (j b) _ (hz b (Classical.arbitrary ι))
  have hsigm : ∀ i, IsSignedNontrivialIrr (m i) := fun i => hG.signed i (j false) _ (hmem i false)
  have hsigφ : ∀ i b, IsSignedNontrivialIrr (φ i b) := fun i b => hG.signed i (j b) _ (hφc i b)
  have Rmm : ∀ i k, i ≠ k → m i ≠ m k ∧ m i ≠ -m k := fun i k hik => by
    have hnm : m i ∉ A k (j false) := fun hmem' => (hzm i false)
      (eq_of_mem_Llinked hG (Or.inr ⟨hik, rfl⟩) (hz false i) (hz false k) (hmem i false) hmem').symm
    exact ⟨fun h => hnm (h ▸ hmem k false),
      hG.ne_neg_of_Llinked (Or.inr ⟨hik, rfl⟩) (hmem i false) (hmem k false)⟩
  have Rzz : ∀ c d, c ≠ d → z c ≠ z d ∧ z c ≠ -z d := fun c d hcd =>
    hG.common_ne_other_column_mem hι (hj.ne hcd) (hz c) (hz d (Classical.arbitrary ι))
  have Rzm : ∀ i c, z c ≠ m i ∧ z c ≠ -m i := fun i c =>
    ⟨hzm i c, hG.ne_neg_of_mem_same (hz c i) (hmem i c)⟩
  have Rzφ : ∀ c k d, z c ≠ φ k d ∧ z c ≠ -φ k d := fun c k d => by
    rcases eq_or_ne d c with rfl | hdc
    · exact ⟨hzφ k d, hG.ne_neg_of_mem_same (hz d k) (hφc k d)⟩
    · exact hG.common_ne_other_column_mem hι (hj.ne (Ne.symm hdc)) (hz c) (hφc k d)
  have Rmφ : ∀ i k d, m i ≠ φ k d ∧ m i ≠ -φ k d := fun i k d => by
    rcases eq_or_ne k i with rfl | hki
    · exact ⟨hmφ k d, hG.ne_neg_of_mem_same (hmem k d) (hφc k d)⟩
    · have hnm : m i ∉ A k (j d) := fun hmem' => (hzm i d)
        (eq_of_mem_Llinked hG (Or.inr ⟨Ne.symm hki, rfl⟩) (hz d i) (hz d k) (hmem i d) hmem').symm
      exact ⟨fun h => hnm (h ▸ hφc k d),
        hG.ne_neg_of_Llinked (Or.inr ⟨Ne.symm hki, rfl⟩) (hmem i d) (hφc k d)⟩
  have Rφφ : ∀ i c k d, (i, c) ≠ (k, d) → φ i c ≠ φ k d ∧ φ i c ≠ -φ k d := fun i c k d hne => by
    rcases eq_or_ne i k with rfl | hik
    · have hcd : c ≠ d := fun h => hne (by rw [h])
      have hnm : φ i c ∉ A i (j d) := fun hmem' => Ne.symm (hmφ i c)
        (eq_of_mem_Llinked hG (Or.inl ⟨rfl, hj.ne hcd⟩) (hmem i c) (hmem i d) (hφc i c) hmem')
      exact ⟨fun h => hnm (h ▸ hφc i d),
        hG.ne_neg_of_Llinked (Or.inl ⟨rfl, hj.ne hcd⟩) (hφc i c) (hφc i d)⟩
    · rcases eq_or_ne c d with rfl | hcd
      · have hnm : φ i c ∉ A k (j c) := fun hmem' => Ne.symm (hzφ i c)
          (eq_of_mem_Llinked hG (Or.inr ⟨hik, rfl⟩) (hz c i) (hz c k) (hφc i c) hmem')
        exact ⟨fun h => hnm (h ▸ hφc k c),
          hG.ne_neg_of_Llinked (Or.inr ⟨hik, rfl⟩) (hφc i c) (hφc k c)⟩
      · obtain ⟨hz1, hz2⟩ := hG.common_not_mem_other_column hι (hj.ne hcd) (hz c) k
        have hnmm : m i ∉ A k (j d) := fun hmem' => (hzm i d)
          (eq_of_mem_Llinked hG (Or.inr ⟨hik, rfl⟩) (hz d i) (hz d k) (hmem i d) hmem').symm
        have hnmm2 : -m i ∉ A k (j d) := fun hmem' =>
          hG.ne_neg_of_Llinked (Or.inr ⟨hik, rfl⟩) (hmem i d) hmem' (neg_neg (m i)).symm
        obtain ⟨h1, h2⟩ := hG.oStep_both_out (Ne.symm hik) (hj.ne (Ne.symm hcd)) (hcell i c)
          (hzm i c) (hzφ i c) (hmφ i c) hz1 hnmm hz2 hnmm2
        exact ⟨fun h => h1 (h ▸ hφc k d), fun h => h2 (by rw [h, neg_neg]; exact hφc k d)⟩
  obtain ⟨hdiag, hoff⟩ :=
    gridFamily_orthonormal z m φ hsigz hsigm hsigφ Rmm Rzz Rzm Rzφ Rmφ Rφφ
  intro a b
  split_ifs with hab
  · subst hab; exact hdiag a
  · exact hoff a b hab

open scoped Classical in
/-- **(3.5.5) two-column family, reindexed to `κ`** (the `w₂ = 3` shape, in the
`symm_orthonormal_family` interface): when there are exactly two columns (`Fintype.card κ = 2`) with
column-commons `z j` (`z j ∈ A i j` for every row `i`), the `Bool`-indexed
`two_col_orthonormal_family` is reindexed back to `κ` via a bijection `Bool ≃ κ`, yielding
row-anchors
`w i` (the per-row meet of the two cells), interior thirds `φ i j`, cells
`A i j = {z j, w i, φ i j}`,
and an orthonormal `gridFamily z w φ` over `ι ⊕ κ ⊕ ι × κ`.  This lets the `w₂ = 3` and transpose
`w₁ = 3` orientations of (3.5) share the `κ`-indexed χ-assembly. -/
theorem two_col_orthonormal_family_reindexed [Fintype ι] [Fintype κ] (hG : IsSignedTripleGrid A)
    (hι : 4 ≤ Fintype.card ι) (hκ2 : Fintype.card κ = 2)
    {z : κ → ClassFunction G ℂ} (hz : ∀ j i, z j ∈ A i j) :
    ∃ (w : ι → ClassFunction G ℂ) (φ : ι → κ → ClassFunction G ℂ),
      (∀ i j, A i j = {z j, w i, φ i j}) ∧
      ∀ a b, ClassFunction.inner (gridFamily z w φ a) (gridFamily z w φ b)
        = if a = b then 1 else 0 := by
  classical
  -- `κ` has exactly two elements, so fix a bijection `e : Bool ≃ κ`
  have hbc : Fintype.card Bool = Fintype.card κ := by rw [Fintype.card_bool, hκ2]
  let e : Bool ≃ κ := Fintype.equivOfCardEq hbc
  obtain ⟨m, ψ, hcell, _hmem, hortho⟩ := hG.two_col_orthonormal_family hι (j := ⇑e)
    e.injective (z := fun b => z (e b)) (fun b i => hz (e b) i)
  refine ⟨m, fun i j => ψ i (e.symm j), ?_, ?_⟩
  · intro i j
    have h := hcell i (e.symm j)
    rwa [Equiv.apply_symm_apply] at h
  · -- transport orthonormality along the reindex equiv `E : ι ⊕ κ ⊕ ι×κ ≃ ι ⊕ Bool ⊕ ι×Bool`
    let E : ι ⊕ κ ⊕ ι × κ ≃ ι ⊕ Bool ⊕ ι × Bool :=
      Equiv.sumCongr (Equiv.refl ι) (Equiv.sumCongr e.symm (Equiv.prodCongr (Equiv.refl ι) e.symm))
    have hgfeq : ∀ a, gridFamily z m (fun i j => ψ i (e.symm j)) a
        = gridFamily (fun b => z (e b)) m ψ (E a) := by
      rintro (i | j | ⟨i, j⟩)
      · rfl
      · change z j = z (e (e.symm j)); rw [Equiv.apply_symm_apply]
      · rfl
    intro a b
    rw [hgfeq a, hgfeq b]
    split_ifs with hab
    · subst hab; rw [hortho (E a) (E a), if_pos rfl]
    · rw [hortho (E a) (E b), if_neg (fun h => hab (E.injective h))]

end IsSignedTripleGrid

end OddOrder.Peterfalvi.S05


