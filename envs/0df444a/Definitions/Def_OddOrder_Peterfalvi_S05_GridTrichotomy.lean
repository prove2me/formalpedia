-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S05_GridTrichotomy
-- name    : OddOrder_Peterfalvi_S05_GridTrichotomy
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:40:37.416692+00:00
-- url     : https://prove2.me/theorems/56987191-bd9f-4ec9-a24c-215e2ba2e503
-- title:
--   Peterfalvi (3.8): the additive-grid trichotomy
-- statement:
--   Peterfalvi, *Character Theory for the Odd Order Theorem*, §3, pp. 15-20. This file isolates the abstract combinatorial core of Theorem (3.8): the coefficient grid $a_{ij}=\langle\psi,\omega_{ij}^\sigma\rangle$ of a class function against the $\sigma$-images of the irreducible characters of $W=W_1\times W_2$ is additively separable by (3.7).
--
--   Results: `grid_no_constant_column` (the abstract (b)/(c) exclusion: a separable grid cannot have a constant nonzero full column) and its row analogue `grid_no_constant_row`.
--
--   The bundle also proves 8 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S05_GridTrichotomy.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S05_GridTrichotomy.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Common
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

namespace OddOrder.Peterfalvi.S05

open scoped BigOperators

/-- **Additive separability ⟹ rank-one factorisation.**  A grid whose mixed differences vanish
(`a (i,j) + a (i',j') = a (i,j') + a (i',j)`, the (3.7) identity) factors as `a (i, j) = f i + g j`.
Fix base points `i₀, j₀`; take `f i = a (i, j₀)` and `g j = a (i₀, j) - a (i₀, j₀)`. -/
theorem exists_param {ι κ : Type*} [Nonempty ι] [Nonempty κ] (a : ι × κ → ℂ)
    (hadd : ∀ i i' (j j' : κ), a (i, j) + a (i', j') = a (i, j') + a (i', j)) :
    ∃ (f : ι → ℂ) (g : κ → ℂ), ∀ i j, a (i, j) = f i + g j := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  obtain ⟨j₀⟩ := ‹Nonempty κ›
  refine ⟨fun i => a (i, j₀), fun j => a (i₀, j) - a (i₀, j₀), fun i j => ?_⟩
  have h := hadd i i₀ j j₀
  linear_combination h

/-- Support count when the grid depends only on the second coordinate: the nonzero set is a union
of full columns, so its size is `|ι| · #{j | b j ≠ 0}`. -/
theorem card_support_const_snd {ι κ : Type*} [Fintype ι] [Fintype κ] (b : κ → ℂ) :
    (Finset.univ.filter (fun p : ι × κ => b p.2 ≠ 0)).card
      = Fintype.card ι * (Finset.univ.filter (fun j => b j ≠ 0)).card := by
  classical
  have h : (Finset.univ.filter (fun p : ι × κ => b p.2 ≠ 0))
      = (Finset.univ : Finset ι) ×ˢ (Finset.univ.filter (fun j => b j ≠ 0)) := by
    ext ⟨i, j⟩
    simp [Finset.mem_filter, Finset.mem_product]
  rw [h, Finset.card_product, Finset.card_univ]

/-- Support count when the grid depends only on the first coordinate: the nonzero set is a union of
full rows, so its size is `#{i | c i ≠ 0} · |κ|`. -/
theorem card_support_const_fst {ι κ : Type*} [Fintype ι] [Fintype κ] (c : ι → ℂ) :
    (Finset.univ.filter (fun p : ι × κ => c p.1 ≠ 0)).card
      = (Finset.univ.filter (fun i => c i ≠ 0)).card * Fintype.card κ := by
  classical
  have h : (Finset.univ.filter (fun p : ι × κ => c p.1 ≠ 0))
      = (Finset.univ.filter (fun i => c i ≠ 0)) ×ˢ (Finset.univ : Finset κ) := by
    ext ⟨i, j⟩
    simp [Finset.mem_filter, Finset.mem_product]
  rw [h, Finset.card_product, Finset.card_univ]

/-- A function with at most one nonzero value is either identically zero or supported on a single
point `j₀`. -/
theorem eq_zero_or_single {κ : Type*} [Fintype κ] (b : κ → ℂ)
    (h : (Finset.univ.filter (fun j => b j ≠ 0)).card ≤ 1) :
    (∀ j, b j = 0) ∨ ∃ j₀ : κ, b j₀ ≠ 0 ∧ ∀ j, j ≠ j₀ → b j = 0 := by
  classical
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with h0 | h1
  · left
    intro j
    by_contra hj
    have : j ∈ Finset.univ.filter (fun j => b j ≠ 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
    rw [Finset.card_eq_zero.mp h0] at this
    simp at this
  · right
    obtain ⟨j₀, hj₀⟩ := Finset.card_eq_one.mp h1
    have hmem : ∀ j, b j ≠ 0 ↔ j = j₀ := by
      intro j
      rw [← Finset.mem_singleton, ← hj₀, Finset.mem_filter]
      exact ⟨fun hb => ⟨Finset.mem_univ j, hb⟩, fun h => h.2⟩
    refine ⟨j₀, (hmem j₀).mpr rfl, fun j hj => ?_⟩
    by_contra hb
    exact hj ((hmem j).mp hb)

/-- **Both factors non-constant ⟹ large support.**  For a rank-one grid `a (i,j) = f i + g j`
with neither `f` nor `g` constant, the support has at least `|ι| + |κ| - 2` elements.

Counting per row: each row has `≥ 1` nonzero entry (`g` non-constant), and two rows `i₁, i₂` with
`f i₁ ≠ f i₂` together have `≥ |κ|` nonzero entries (their zero-sets `{j | g j = -f i}` are
disjoint).
Summing: `#support = ∑_i (row count) ≥ |κ| + (|ι| - 2)·1 = |ι| + |κ| - 2`. -/
theorem card_support_ge_of_not_const {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → ℂ) (g : κ → ℂ) (hf : ¬ ∀ i i', f i = f i') (hg : ¬ ∀ j j', g j = g j') :
    Fintype.card ι + Fintype.card κ
      ≤ (Finset.univ.filter (fun p : ι × κ => f p.1 + g p.2 ≠ 0)).card + 2 := by
  classical
  -- support card = ∑ i, (nonzeros in row i)
  have hcard : (Finset.univ.filter (fun p : ι × κ => f p.1 + g p.2 ≠ 0)).card
      = ∑ i, (Finset.univ.filter (fun j : κ => f i + g j ≠ 0)).card := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl (fun i _ => (Finset.card_filter _ _).symm)
  -- each row has ≥ 1 nonzero
  have hrow1 : ∀ i, 1 ≤ (Finset.univ.filter (fun j : κ => f i + g j ≠ 0)).card := by
    intro i
    obtain ⟨j, hj⟩ : ∃ j, f i + g j ≠ 0 := by
      by_contra hc; push Not at hc
      exact hg (fun j j' => by linear_combination hc j - hc j')
    exact Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
  -- two distinguished rows together cover all columns
  obtain ⟨i₁, i₂, hi⟩ : ∃ i₁ i₂, f i₁ ≠ f i₂ := by
    by_contra hc; push Not at hc; exact hf hc
  have hi12 : i₁ ≠ i₂ := fun h => hi (by rw [h])
  have hpair : Fintype.card κ
      ≤ (Finset.univ.filter (fun j : κ => f i₁ + g j ≠ 0)).card
        + (Finset.univ.filter (fun j : κ => f i₂ + g j ≠ 0)).card := by
    -- zero-sets are disjoint; nonzero-sets cover κ
    have hcover : (Finset.univ : Finset κ)
        ⊆ (Finset.univ.filter (fun j : κ => f i₁ + g j ≠ 0))
          ∪ (Finset.univ.filter (fun j : κ => f i₂ + g j ≠ 0)) := by
      intro j _
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      by_cases h1 : f i₁ + g j = 0
      · refine Or.inr ⟨Finset.mem_univ j, ?_⟩
        intro h2
        exact hi (by linear_combination h1 - h2)
      · exact Or.inl ⟨Finset.mem_univ j, h1⟩
    calc Fintype.card κ = (Finset.univ : Finset κ).card := (Finset.card_univ).symm
      _ ≤ _ := Finset.card_le_card hcover
      _ ≤ _ := Finset.card_union_le _ _
  -- assemble: split the sum off the pair `{i₁, i₂}`
  rw [hcard]
  have hsub : ({i₁, i₂} : Finset ι) ⊆ Finset.univ := Finset.subset_univ _
  rw [← Finset.sum_sdiff hsub]
  have hpaircard : ({i₁, i₂} : Finset ι).card = 2 := Finset.card_pair hi12
  have hsdiffcard : (Finset.univ \ ({i₁, i₂} : Finset ι)).card + 2 = Fintype.card ι := by
    have hc := Finset.card_sdiff_add_card_eq_card hsub
    rw [hpaircard, Finset.card_univ] at hc
    exact hc
  have hsumpair : ∑ i ∈ ({i₁, i₂} : Finset ι),
      (Finset.univ.filter (fun j : κ => f i + g j ≠ 0)).card
      = (Finset.univ.filter (fun j : κ => f i₁ + g j ≠ 0)).card
        + (Finset.univ.filter (fun j : κ => f i₂ + g j ≠ 0)).card :=
    Finset.sum_pair hi12
  have hsumsdiff : (Finset.univ \ ({i₁, i₂} : Finset ι)).card
      ≤ ∑ i ∈ Finset.univ \ ({i₁, i₂} : Finset ι),
        (Finset.univ.filter (fun j : κ => f i + g j ≠ 0)).card := by
    calc (Finset.univ \ ({i₁, i₂} : Finset ι)).card
        = ∑ _i ∈ Finset.univ \ ({i₁, i₂} : Finset ι), 1 := by
          rw [Finset.sum_const, smul_eq_mul, mul_one]
      _ ≤ _ := Finset.sum_le_sum (fun i _ => hrow1 i)
  rw [hsumpair]
  omega

/-- **Peterfalvi (3.8), abstract trichotomy.**  Let `a : ι × κ → ℂ` be an additively separable grid
(`a (i,j) + a (i',j') = a (i,j') + a (i',j)`) with `|ι| + 2 ≤ |κ|` (the odd-order gap `w₁ + 2 ≤ w₂`)
and whose support has fewer than `2|ι|` elements (`NC(ψ) < 2w₁`).  Then exactly one of:

* (a) `a` is identically zero (`ψ = β`);
* (b) `a` is a constant nonzero indicator of a single column `j₀` (`ψ = c·∑_i ω_{i,j₀}^σ + β`);
* (c) `a` is a constant nonzero indicator of a single row `i₀` (`ψ = c·∑_j ω_{i₀,j}^σ + β`).

Factor `a (i,j) = f i + g j` (`exists_param`).  If `f` is constant the grid depends only on the
column, and `< 2|ι|` support forces `≤ 1` nonzero column (`eq_zero_or_single`) — case (a)/(b).  If
`g`
is constant, symmetrically `≤ 1` nonzero row (using `|κ| > |ι|`) — case (a)/(c).  If neither is
constant, the support has `≥ |ι| + |κ| - 2 ≥ 2|ι|` elements (`card_support_ge_of_not_const`),
contradicting the hypothesis. -/
theorem grid_trichotomy {ι κ : Type*} [Finite ι] [Finite κ] [Nonempty ι] [Nonempty κ]
    (a : ι × κ → ℂ)
    (hadd : ∀ i i' (j j' : κ), a (i, j) + a (i', j') = a (i, j') + a (i', j))
    (hgap : Nat.card ι + 2 ≤ Nat.card κ)
    (hlt : {x | a x ≠ 0}.ncard < 2 * Nat.card ι) :
    (∀ x, a x = 0) ∨
      (∃ (j₀ : κ) (c : ℂ), c ≠ 0 ∧ (∀ i, a (i, j₀) = c) ∧ ∀ i j, j ≠ j₀ → a (i, j) = 0) ∨
      (∃ (i₀ : ι) (c : ℂ), c ≠ 0 ∧ (∀ j, a (i₀, j) = c) ∧ ∀ i j, i ≠ i₀ → a (i, j) = 0) := by
  classical
  have : Fintype ι := Fintype.ofFinite _
  have : Fintype κ := Fintype.ofFinite _
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred, Nat.card_eq_fintype_card] at hlt
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hgap
  obtain ⟨f, g, hfg⟩ := exists_param a hadd
  -- rewrite the support filter in terms of `f, g`
  have hsupp : (Finset.univ.filter (fun x : ι × κ => a x ≠ 0))
      = Finset.univ.filter (fun p : ι × κ => f p.1 + g p.2 ≠ 0) :=
    Finset.filter_congr (fun ⟨i, j⟩ _ => by rw [hfg i j])
  rw [hsupp] at hlt
  by_cases hfc : ∀ i i', f i = f i'
  · -- `f` constant: grid depends only on the column
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    have hbeq : (Finset.univ.filter (fun p : ι × κ => f p.1 + g p.2 ≠ 0))
        = Finset.univ.filter (fun p : ι × κ => (fun j => f i₀ + g j) p.2 ≠ 0) :=
      Finset.filter_congr (fun ⟨i, j⟩ _ => by rw [hfc i i₀])
    rw [hbeq, card_support_const_snd (fun j => f i₀ + g j)] at hlt
    have hNκ : (Finset.univ.filter (fun j => f i₀ + g j ≠ 0)).card ≤ 1 := by
      rw [mul_comm] at hlt
      have := Nat.lt_of_mul_lt_mul_right hlt
      omega
    rcases eq_zero_or_single (fun j => f i₀ + g j) hNκ with hz | ⟨j₀, hj₀, hrest⟩
    · exact Or.inl (fun ⟨i, j⟩ => by rw [hfg i j, hfc i i₀]; exact hz j)
    · refine Or.inr (Or.inl ⟨j₀, f i₀ + g j₀, hj₀, fun i => ?_, fun i j hj => ?_⟩)
      · rw [hfg i j₀, hfc i i₀]
      · rw [hfg i j, hfc i i₀]; exact hrest j hj
  · by_cases hgc : ∀ j j', g j = g j'
    · -- `g` constant: grid depends only on the row
      obtain ⟨j₀⟩ := ‹Nonempty κ›
      have hceq : (Finset.univ.filter (fun p : ι × κ => f p.1 + g p.2 ≠ 0))
          = Finset.univ.filter (fun p : ι × κ => (fun i => f i + g j₀) p.1 ≠ 0) :=
        Finset.filter_congr (fun ⟨i, j⟩ _ => by rw [hgc j j₀])
      rw [hceq, card_support_const_fst (fun i => f i + g j₀)] at hlt
      have hNι : (Finset.univ.filter (fun i => f i + g j₀ ≠ 0)).card ≤ 1 := by
        by_contra hge
        push Not at hge
        have h2 : 2 * Fintype.card κ
            ≤ (Finset.univ.filter (fun i => f i + g j₀ ≠ 0)).card * Fintype.card κ := by
          gcongr
          omega
        omega
      rcases eq_zero_or_single (fun i => f i + g j₀) hNι with hz | ⟨i₀, hi₀, hrest⟩
      · exact Or.inl (fun ⟨i, j⟩ => by rw [hfg i j, hgc j j₀]; exact hz i)
      · refine Or.inr (Or.inr ⟨i₀, f i₀ + g j₀, hi₀, fun j => ?_, fun i j hi => ?_⟩)
        · rw [hfg i₀ j, hgc j j₀]
        · rw [hfg i j, hgc j j₀]; exact hrest i hi
    · -- neither constant: support too large, contradiction
      exfalso
      have hge := card_support_ge_of_not_const f g hfc hgc
      omega

/-- Two distinct elements of a fintype of card `≥ 3`, both different from a given `d`. -/
theorem exists_two_ne_ne {α : Type*} [Fintype α] (h3 : 3 ≤ Fintype.card α) (d : α) :
    ∃ a b : α, a ≠ b ∧ a ≠ d ∧ b ≠ d := by
  classical
  have hcard : 2 ≤ ({d}ᶜ : Finset α).card := by
    rw [Finset.card_compl, Finset.card_singleton]; omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < ({d}ᶜ : Finset α).card)
  exact ⟨a, b, hab, by simpa using ha, by simpa using hb⟩

open scoped Classical in
/-- **The abstract `(b)/(c)` exclusion.**  A separable-grid `a = G − δ-part` cannot have a constant
nonzero full column.  Here `G` has at most two nonzero entries, all in `{0, ±1}`; the `δ`-part is
`s·([P = ·] − [Q = ·])` (`s = ±1`, `P ≠ Q`).  If `a(·, j₀) ≡ c ≠ 0` and `a` vanishes off column
`j₀`, then either both `P, Q` lie in column `j₀` — forcing `G P = c + s`, `G Q = c − s`, which with
`G P, G Q ∈ {0, ±1}` and `G P − G Q = 2s = ±2` gives `c = 0` (contradiction) — or at most one does,
yielding three distinct nonzero `G`-entries (two non-`δ` column rows since `|ι| ≥ 3`, plus one
off-column `δ`-point), contradicting `|Supp G| ≤ 2`.  Used for both `(b)` and `(c)` (the latter via
the transposed grid). -/
theorem grid_no_constant_column {ι κ : Type*} [Fintype ι] [Finite κ]
    (h3 : 3 ≤ Fintype.card ι) (G : ι × κ → ℂ)
    (hG2 : {x | G x ≠ 0}.ncard ≤ 2) (hG01 : ∀ x, G x = 0 ∨ G x = 1 ∨ G x = -1)
    (P Q : ι × κ) (hPQ : P ≠ Q) {s : ℂ} (hs : s = 1 ∨ s = -1) (a : ι × κ → ℂ)
    (ha : ∀ x, a x = G x - s * ((if P = x then (1 : ℂ) else 0) - (if Q = x then (1 : ℂ) else 0)))
    {j₀ : κ} {c : ℂ} (hc : c ≠ 0) (hcol : ∀ i, a (i, j₀) = c)
    (hoff : ∀ i j, j ≠ j₀ → a (i, j) = 0) : False := by
  classical
  have : Finite (ι × κ) := inferInstance
  by_cases hboth : P.2 = j₀ ∧ Q.2 = j₀
  · -- both `P, Q` in column `j₀`: `G P = c + s`, `G Q = c − s` force `c = 0`
    obtain ⟨hPj, hQj⟩ := hboth
    have hGP : G P = c + s := by
      have hP : a P = c := by have h := hcol P.1; rwa [← hPj] at h
      have := ha P; rw [if_pos rfl, if_neg (Ne.symm hPQ)] at this; rw [hP] at this
      linear_combination -this
    have hGQ : G Q = c - s := by
      have hQ : a Q = c := by have h := hcol Q.1; rwa [← hQj] at h
      have := ha Q; rw [if_neg hPQ, if_pos rfl] at this; rw [hQ] at this
      linear_combination -this
    have hsum : G P + G Q = 2 * c := by linear_combination hGP + hGQ
    have hdiff : G P - G Q = 2 * s := by linear_combination hGP - hGQ
    rcases hG01 P with hp | hp | hp <;> rcases hG01 Q with hq | hq | hq <;>
      rcases hs with hsv | hsv <;> rw [hp, hq] at hsum hdiff <;> rw [hsv] at hdiff <;>
      first
      | exact hc (by linear_combination (-1 / 2 : ℂ) * hsum)
      | norm_num at hdiff
  · -- at most one of `P, Q` in column `j₀`: exhibit three distinct nonzero `G`-entries
    obtain ⟨Off, d, hOffmem, hOffj, hnonδ⟩ :
        ∃ (Off : ι × κ) (d : ι), G Off ≠ 0 ∧ Off.2 ≠ j₀ ∧
          ∀ r, r ≠ d → (r, j₀) ≠ P ∧ (r, j₀) ≠ Q := by
      by_cases hPj : P.2 = j₀
      · have hQj : Q.2 ≠ j₀ := fun hQj => hboth ⟨hPj, hQj⟩
        have hGQ : G Q = -s := by
          have h0 : a Q = 0 := hoff Q.1 Q.2 hQj
          have := ha Q; rw [if_neg hPQ, if_pos rfl, h0] at this; linear_combination -this
        refine ⟨Q, P.1, by rw [hGQ]; rcases hs with h | h <;> simp [h], hQj, fun r hr => ?_⟩
        exact ⟨fun hrP => hr (congrArg Prod.fst hrP), fun hrQ => hQj (congrArg Prod.snd hrQ).symm⟩
      · have hGP : G P = s := by
          have h0 : a P = 0 := hoff P.1 P.2 hPj
          have := ha P; rw [if_pos rfl, if_neg (Ne.symm hPQ), h0] at this; linear_combination -this
        refine ⟨P, Q.1, by rw [hGP]; rcases hs with h | h <;> simp [h], hPj, fun r hr => ?_⟩
        exact ⟨fun hrP => hPj (congrArg Prod.snd hrP).symm, fun hrQ => hr (congrArg Prod.fst hrQ)⟩
    obtain ⟨r₁, r₂, hr12, hr1d, hr2d⟩ := exists_two_ne_ne h3 d
    have hG1 : G (r₁, j₀) ≠ 0 := by
      have := hcol r₁
      rw [ha, if_neg (Ne.symm (hnonδ r₁ hr1d).1),
        if_neg (Ne.symm (hnonδ r₁ hr1d).2)] at this
      rw [show G (r₁, j₀) = c by linear_combination this]
      exact hc
    have hG2' : G (r₂, j₀) ≠ 0 := by
      have := hcol r₂
      rw [ha, if_neg (Ne.symm (hnonδ r₂ hr2d).1),
        if_neg (Ne.symm (hnonδ r₂ hr2d).2)] at this
      rw [show G (r₂, j₀) = c by linear_combination this]
      exact hc
    have hsub : ({(r₁, j₀), (r₂, j₀), Off} : Set (ι × κ)) ⊆ {x | G x ≠ 0} := by
      intro x hx; rcases hx with rfl | rfl | rfl
      exacts [hG1, hG2', hOffmem]
    have hcard3 : ({(r₁, j₀), (r₂, j₀), Off} : Set (ι × κ)).ncard = 3 := by
      rw [Set.ncard_eq_three]
      exact ⟨_, _, _, by simp [hr12], fun h => hOffj (congrArg Prod.snd h.symm),
        fun h => hOffj (congrArg Prod.snd h.symm), rfl⟩
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [hcard3] at this; omega

open scoped Classical in
/-- The row analogue of `grid_no_constant_column` (no constant nonzero full row), obtained by
applying the column statement to the transposed grid. -/
theorem grid_no_constant_row {ι κ : Type*} [Finite ι] [Fintype κ]
    (h3 : 3 ≤ Fintype.card κ) (G : ι × κ → ℂ)
    (hG2 : {x | G x ≠ 0}.ncard ≤ 2) (hG01 : ∀ x, G x = 0 ∨ G x = 1 ∨ G x = -1)
    (P Q : ι × κ) (hPQ : P ≠ Q) {s : ℂ} (hs : s = 1 ∨ s = -1) (a : ι × κ → ℂ)
    (ha : ∀ x, a x = G x - s * ((if P = x then (1 : ℂ) else 0) - (if Q = x then (1 : ℂ) else 0)))
    {i₀ : ι} {c : ℂ} (hc : c ≠ 0) (hrow : ∀ j, a (i₀, j) = c)
    (hoff : ∀ i j, i ≠ i₀ → a (i, j) = 0) : False := by
  have hswapG : {x : κ × ι | G (x.2, x.1) ≠ 0}.ncard ≤ 2 :=
    le_trans (Set.ncard_le_ncard_of_injOn Prod.swap (fun x hx => hx)
      (Prod.swap_injective.injOn) (Set.toFinite _)) hG2
  have hflip : ∀ (R : ι × κ) (y : κ × ι), (Prod.swap R = y) ↔ (R = (y.2, y.1)) := fun R y => by
    rw [Prod.ext_iff, Prod.ext_iff, Prod.fst_swap, Prod.snd_swap]; tauto
  refine grid_no_constant_column h3 (fun x => G (x.2, x.1)) hswapG (fun x => hG01 _)
    (Prod.swap P) (Prod.swap Q) (fun he => hPQ (Prod.swap_injective he)) hs
    (fun x => a (x.2, x.1)) (fun x => ?_) hc (fun j => hrow j) (fun j i hi => hoff i j hi)
  simp only [ha, hflip]

/-- **Peterfalvi (5.8), abstract full-column core.**  Let `a : ι × κ → ℂ` be an additively separable
grid (`a (i,q) + a (i',q') = a (i,q') + a (i',q)`) supported on two columns `j ≠ k` (every entry off
`{j, k}` vanishes, witnessed by a third column `q₀ ∉ {j, k}`), with column-`k` entries in `{0, δ}`,
column-`j` entries in `{0, −δ}` (`δ = ±1`), and total squared mass `∑_{p,q} a(p,q)² = |ι|`.  Then
`a` is a single constant full column: either column `k` is constantly `δ` (column `j` zero), or
column `j` is constantly `−δ` (column `k` zero).

Separability together with the zero column `q₀` forces `a` to be column-constant
(`a (i, q) = a (i₀, q)`), so the mass is `|ι| · (a(i₀,j)² + a(i₀,k)²) = |ι|`, i.e.
`a(i₀,j)² + a(i₀,k)² = 1`; with the two entries in `{0, ±1}` exactly one is `±1`.  This is the (5.8)
analogue of the norm-`2` endgame `eq_smul_chiFam_diff_of_vanishOnV` (which instead *kills* every
coefficient). -/
theorem grid_eq_const_column_of_two_col {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι]
    (a : ι × κ → ℂ)
    (hadd : ∀ i i' (q q' : κ), a (i, q) + a (i', q') = a (i, q') + a (i', q))
    {j k : κ} (hjk : j ≠ k) {q₀ : κ} (hq₀j : q₀ ≠ j) (hq₀k : q₀ ≠ k)
    (hsupp : ∀ i q, q ≠ j → q ≠ k → a (i, q) = 0)
    {δ : ℂ} (hδ : δ = 1 ∨ δ = -1)
    (hk : ∀ i, a (i, k) = 0 ∨ a (i, k) = δ)
    (hj : ∀ i, a (i, j) = 0 ∨ a (i, j) = -δ)
    (hnorm : ∑ pq, (a pq) ^ 2 = (Fintype.card ι : ℂ)) :
    ((∀ i, a (i, k) = δ) ∧ (∀ i, a (i, j) = 0)) ∨
      ((∀ i, a (i, j) = -δ) ∧ (∀ i, a (i, k) = 0)) := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  -- separability + the zero column `q₀` make the grid column-constant
  have hconst : ∀ i q, a (i, q) = a (i₀, q) := by
    intro i q
    have h := hadd i i₀ q q₀
    rwa [hsupp i q₀ hq₀j hq₀k, hsupp i₀ q₀ hq₀j hq₀k, add_zero, zero_add] at h
  -- each row's squared mass collapses to the two distinguished column entries
  have hrow : ∀ i, ∑ q, (a (i, q)) ^ 2 = (a (i₀, j)) ^ 2 + (a (i₀, k)) ^ 2 := by
    intro i
    have step1 : ∑ q, (a (i, q)) ^ 2 = ∑ q, (a (i₀, q)) ^ 2 :=
      Finset.sum_congr rfl (fun q _ => by rw [hconst i q])
    have step2 : ∑ q, (a (i₀, q)) ^ 2 = ∑ q ∈ ({j, k} : Finset κ), (a (i₀, q)) ^ 2 := by
      refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
      intro q _ hq
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hq
      rw [hsupp i₀ q hq.1 hq.2]; ring
    rw [step1, step2, Finset.sum_pair hjk]
  -- total mass = |ι| · (a(i₀,j)² + a(i₀,k)²)
  have hmass : ∑ pq, (a pq) ^ 2
      = (Fintype.card ι : ℂ) * ((a (i₀, j)) ^ 2 + (a (i₀, k)) ^ 2) := by
    rw [Fintype.sum_prod_type, Finset.sum_congr rfl (fun i _ => hrow i), Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
  rw [hmass] at hnorm
  have hcard0 : (Fintype.card ι : ℂ) ≠ 0 := by
    have : 0 < Fintype.card ι := Fintype.card_pos
    exact_mod_cast this.ne'
  have hsum1 : (a (i₀, j)) ^ 2 + (a (i₀, k)) ^ 2 = 1 :=
    mul_left_cancel₀ hcard0 (by rw [hnorm, mul_one])
  have hδsq : δ ^ 2 = 1 := by rcases hδ with h | h <;> rw [h] <;> ring
  rcases hk i₀ with hAk0 | hAkδ
  · rcases hj i₀ with hAj0 | hAjδ
    · -- both columns vanish ⟹ total mass `0 ≠ |ι|`
      rw [hAk0, hAj0] at hsum1; norm_num at hsum1
    · -- column `j` carries `−δ`, column `k` vanishes
      exact Or.inr ⟨fun i => by rw [hconst i j]; exact hAjδ,
        fun i => by rw [hconst i k]; exact hAk0⟩
  · -- column `k` carries `δ`, forcing column `j` to vanish
    rw [hAkδ, hδsq] at hsum1
    have hAj0 : a (i₀, j) = 0 :=
      mul_self_eq_zero.mp (by linear_combination hsum1)
    exact Or.inl ⟨fun i => by rw [hconst i k]; exact hAkδ,
      fun i => by rw [hconst i j]; exact hAj0⟩

end OddOrder.Peterfalvi.S05


