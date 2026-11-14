-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Foundations_Data_BitString_WordCount
-- name    : Complexitylib_0ebd467_Foundations_Data_BitString_WordCount
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:34:14.890759+00:00
-- url     : https://prove2.me/theorems/f6a449ed-0a32-4b19-86d6-090bb7448431
-- title:
--   Complexity.Foundations.Data.BitString.WordCount — Counting words
-- statement:
--   This is module `Complexity.Foundations.Data.BitString.WordCount` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   Counting the words `List.ofFn v`, for `v : Fin n → Bool`, that pass a test: the counting arguments
--   of parity and counting classes, which count accepted certificates. A word of length `m + n` is a
--   prefix of length `m` followed by a word of length `n`
--   (`Cslib.BitString.card_filter_ofFn_add`); a word of length `n + 1` is a first bit followed by a
--   word of length `n` (`Cslib.BitString.card_filter_ofFn_succ`); a word of `T` rows of `B` bits
--   whose rows pass independent tests is counted by a product
--   (`Cslib.BitString.card_filter_listRows_all`). Exactly one word has no bit `true`, and exactly one
--   has no bit `false` (`Cslib.BitString.card_filter_not_any`, `Cslib.BitString.card_filter_all`).
--
--   The lexicographic order on words of equal length (`Cslib.BitString.wordLt`) is the order of
--   `Lex (Fin n → Bool)` (`Cslib.BitString.wordLt_ofFn_iff`), so strictly increasing lists of words
--   represent sets of words.
--
--   ### Main definitions
--
--   * `Cslib.BitString.wordLt`: the lexicographic order on words of equal length.
--
--   ### Main results
--
--   * `Cslib.BitString.card_filter_binaryValue_lt`: exact counts below a binary threshold.
--   * `Cslib.BitString.card_filter_ofFn_add`, `Cslib.BitString.card_filter_ofFn_succ`: counting
--     words by a prefix or by their first bit.
--   * `Cslib.BitString.card_filter_take`: counting words by a condition on a prefix.
--   * `Cslib.BitString.card_filter_take_drop`: independent prefix/suffix tests give a product.
--   * `Cslib.BitString.two_mul_two_pow_le_of_four_mul_card_filter_not_le`: a quarter of failures leaves
--     two thirds of successes.
--   * `Cslib.BitString.two_pow_mul_card_filter_card_filter_block_le`: majority votes of `12 e` blocks
--     err on at most a `2 ^ (-e)` fraction.
--   * `Cslib.BitString.card_filter_listRows_all`: counting words by a condition on each row.
--   * `Cslib.BitString.not_any_ofFn_eq_true_iff`, `Cslib.BitString.card_filter_not_any`,
--     `Cslib.BitString.card_filter_all`: the constant words.
--   * `Cslib.BitString.ofFn_decide_lt`: the unary word of `k` bits `true` among `K`.
--   * `Cslib.BitString.wordLt_ofFn_iff`: `wordLt` is the lexicographic order.
--   * `Cslib.BitString.odd_prod_iff`, `Cslib.BitString.odd_one_add_prod_one_add`: parity of products
--     and the parity form of a disjunction.
--   * `Cslib.BitString.card_filter_forall_apply_mem`: counting functions with restricted values on an
--     injective family of points.
--   * `Cslib.BitString.two_pow_mul_card_filter_exists_le`: union bound for random strings.
--   * `Cslib.BitString.sum_range_neg_two_pow_mul_choose`,
--     `Cslib.BitString.sum_range_neg_two_pow_mul_choose_zmod`: the parity of `c` from binomial
--     coefficients, over `ℤ` and modulo `2 ^ K`.
--   * `Cslib.BitString.card_filter_strictMono`, `Cslib.BitString.strictMono_of_lt_succ`: strictly
--     increasing tuples count subsets.
--
--   **Contents.** The module is published as a whole: 22 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_BitString_WordCount`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Foundations/Data/BitString/WordCount.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_BitString_List
public import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_BitString_List_Binary
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Order.PiLex
import Definitions.Def_Complexitylib_0ebd467_Foundations_Combinatorics_MajorityVote
import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_List_Lookup
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/- Prove2me definition bundle for `Complexity.Foundations.Data.BitString.WordCount` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Counting words

Counting the words `List.ofFn v`, for `v : Fin n → Bool`, that pass a test: the counting arguments
of parity and counting classes, which count accepted certificates. A word of length `m + n` is a
prefix of length `m` followed by a word of length `n`
(`Cslib.BitString.card_filter_ofFn_add`); a word of length `n + 1` is a first bit followed by a
word of length `n` (`Cslib.BitString.card_filter_ofFn_succ`); a word of `T` rows of `B` bits
whose rows pass independent tests is counted by a product
(`Cslib.BitString.card_filter_listRows_all`). Exactly one word has no bit `true`, and exactly one
has no bit `false` (`Cslib.BitString.card_filter_not_any`, `Cslib.BitString.card_filter_all`).

The lexicographic order on words of equal length (`Cslib.BitString.wordLt`) is the order of
`Lex (Fin n → Bool)` (`Cslib.BitString.wordLt_ofFn_iff`), so strictly increasing lists of words
represent sets of words.

## Main definitions

* `Cslib.BitString.wordLt`: the lexicographic order on words of equal length.

## Main results

* `Cslib.BitString.card_filter_binaryValue_lt`: exact counts below a binary threshold.
* `Cslib.BitString.card_filter_ofFn_add`, `Cslib.BitString.card_filter_ofFn_succ`: counting
  words by a prefix or by their first bit.
* `Cslib.BitString.card_filter_take`: counting words by a condition on a prefix.
* `Cslib.BitString.card_filter_take_drop`: independent prefix/suffix tests give a product.
* `Cslib.BitString.two_mul_two_pow_le_of_four_mul_card_filter_not_le`: a quarter of failures leaves
  two thirds of successes.
* `Cslib.BitString.two_pow_mul_card_filter_card_filter_block_le`: majority votes of `12 e` blocks
  err on at most a `2 ^ (-e)` fraction.
* `Cslib.BitString.card_filter_listRows_all`: counting words by a condition on each row.
* `Cslib.BitString.not_any_ofFn_eq_true_iff`, `Cslib.BitString.card_filter_not_any`,
  `Cslib.BitString.card_filter_all`: the constant words.
* `Cslib.BitString.ofFn_decide_lt`: the unary word of `k` bits `true` among `K`.
* `Cslib.BitString.wordLt_ofFn_iff`: `wordLt` is the lexicographic order.
* `Cslib.BitString.odd_prod_iff`, `Cslib.BitString.odd_one_add_prod_one_add`: parity of products
  and the parity form of a disjunction.
* `Cslib.BitString.card_filter_forall_apply_mem`: counting functions with restricted values on an
  injective family of points.
* `Cslib.BitString.two_pow_mul_card_filter_exists_le`: union bound for random strings.
* `Cslib.BitString.sum_range_neg_two_pow_mul_choose`,
  `Cslib.BitString.sum_range_neg_two_pow_mul_choose_zmod`: the parity of `c` from binomial
  coefficients, over `ℤ` and modulo `2 ^ K`.
* `Cslib.BitString.card_filter_strictMono`, `Cslib.BitString.strictMono_of_lt_succ`: strictly
  increasing tuples count subsets.
-/

@[expose] public section

namespace Cslib.BitString

open Finset

/-! ### Counting words -/

/-- **Counting words by their prefixes**: the words of length `m + n` are the words `u ++ w`
with `u` of length `m` and `w` of length `n`. -/
theorem card_filter_ofFn_add (m n : ℕ) (g : List Bool → List Bool → Prop)
    [∀ u w, Decidable (g u w)] :
    (univ.filter fun v : Fin (m + n) → Bool =>
      g ((List.ofFn v).take m) ((List.ofFn v).drop m)).card =
      ∑ u : Fin m → Bool,
        (univ.filter fun w : Fin n → Bool => g (List.ofFn u) (List.ofFn w)).card := by
  classical
  rw [← card_map (Fin.appendEquiv m n).symm.toEmbedding]
  have hmap : (univ.filter fun v : Fin (m + n) → Bool =>
      g ((List.ofFn v).take m) ((List.ofFn v).drop m)).map
        (Fin.appendEquiv m n).symm.toEmbedding =
      univ.filter fun x : (Fin m → Bool) × (Fin n → Bool) => g (List.ofFn x.1) (List.ofFn x.2) := by
    ext x
    simp only [mem_map_equiv, Equiv.symm_symm, mem_filter, mem_univ, true_and]
    change g ((List.ofFn (Fin.append x.1 x.2)).take m)
      ((List.ofFn (Fin.append x.1 x.2)).drop m) ↔ _
    rw [List.ofFn_fin_append, List.take_left' List.length_ofFn, List.drop_left' List.length_ofFn]
  rw [hmap, card_filter, Fintype.sum_prod_type]
  simp only [card_filter]

/-- **Counting words by a prefix.** For `k ≤ K`, the words of `K` bits whose prefix of length `k`
satisfies `g` are `2 ^ (K - k)` times as many as the words of `k` bits satisfying `g`. -/
theorem card_filter_take {k K : ℕ} (h : k ≤ K) (g : List Bool → Prop) [DecidablePred g] :
    #{r : Fin K → Bool | g ((List.ofFn r).take k)} =
      2 ^ (K - k) * #{r : Fin k → Bool | g (List.ofFn r)} := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [card_filter_ofFn_add k j fun u _ => g u, Nat.add_sub_cancel_left, card_filter, mul_sum]
  refine sum_congr rfl fun u _ => ?_
  by_cases hu : g (List.ofFn u) <;> simp [hu]

/-- Counting words of length `m` by a condition on their first `a` bits and a condition on the
remaining bits gives the product of the two counts. -/
theorem card_filter_take_drop {m a : ℕ} (h : a ≤ m) (P Q : List Bool → Prop) [DecidablePred P]
    [DecidablePred Q] :
    (Finset.univ.filter fun r : Fin m → Bool =>
      P ((List.ofFn r).take a) ∧ Q ((List.ofFn r).drop a)).card =
      (Finset.univ.filter fun u : Fin a → Bool => P (List.ofFn u)).card *
        (Finset.univ.filter fun v : Fin (m - a) → Bool => Q (List.ofFn v)).card := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [BitString.card_filter_ofFn_add a k (fun u v => P u ∧ Q v), Nat.add_sub_cancel_left]
  simp_rw [Finset.card_filter]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : P (List.ofFn u) <;> simp [hu]

/-- **Error at most `1 / 4` is error at most `1 / 3`**: if at most a quarter of the strings of `m`
bits fail `g`, at least two thirds of them satisfy it. -/
theorem two_mul_two_pow_le_of_four_mul_card_filter_not_le {m : ℕ}
    (g : BitString m → Prop) [DecidablePred g] (h : 4 * #{r | ¬g r} ≤ 2 ^ m) :
    2 * 2 ^ m ≤ 3 * #{r | g r} := by
  have hsum : #{r | g r} + #{r | ¬g r} = 2 ^ m := by
    rw [card_filter_add_card_filter_not, card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin]
  omega

/-- **Majority votes of blocks.** If at least two thirds of the strings of `m` bits satisfy `g`,
then at most a `2 ^ (-e)` fraction of the strings of `2 R = 12 e` blocks of `m` bits have at most
`R` blocks satisfying `g`: the exponential-moment bound `Cslib.card_filter_card_filter_le_le`, with
`2 * 8 ^ 6 ≤ 9 ^ 6`. -/
theorem two_pow_mul_card_filter_card_filter_block_le {m e R : ℕ} (hR : R = 6 * e)
    (g : BitString m → Prop) [DecidablePred g] (hg : 2 * 2 ^ m ≤ 3 * #{s | g s}) :
    2 ^ e * #{x : BitString (2 * R * m) | #{i | g (block x i)} ≤ R} ≤ 2 ^ (2 * R * m) := by
  have hmaj := card_filter_card_filter_le_le (univ.filter g)
    (by simpa only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] using hg) R
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, ← pow_mul, Nat.mul_comm m] at hmaj
  have hc : 9 ^ R * #{x : BitString (2 * R * m) | #{i | g (block x i)} ≤ R} ≤
      8 ^ R * 2 ^ (2 * R * m) := by
    refine (Nat.mul_le_mul_left _ ?_).trans hmaj
    rw [← card_map blocksEquiv.toEmbedding]
    refine card_le_card fun ω hω => ?_
    obtain ⟨x, hx, rfl⟩ := mem_map.1 hω
    refine mem_filter.2 ⟨mem_univ _, ?_⟩
    simpa only [mem_filter, mem_univ, true_and, Equiv.coe_toEmbedding, blocksEquiv_apply] using hx
  have hq : 2 ^ e * 8 ^ R ≤ 9 ^ R := by
    subst hR
    simp only [pow_mul, ← mul_pow]
    exact Nat.pow_le_pow_left (by norm_num) _
  refine Nat.le_of_mul_le_mul_left ?_ (by positivity : 0 < 9 ^ R)
  calc 9 ^ R * (2 ^ e * #{x : BitString (2 * R * m) | #{i | g (block x i)} ≤ R})
      = 2 ^ e * (9 ^ R * #{x : BitString (2 * R * m) | #{i | g (block x i)} ≤ R}) := by
        ring
    _ ≤ 2 ^ e * (8 ^ R * 2 ^ (2 * R * m)) := Nat.mul_le_mul_left _ hc
    _ = 2 ^ e * 8 ^ R * 2 ^ (2 * R * m) := by ring
    _ ≤ 9 ^ R * 2 ^ (2 * R * m) := Nat.mul_le_mul_right _ hq

/-- **Counting words by their first bit.** -/
theorem card_filter_ofFn_succ (n : ℕ) (g : List Bool → Prop) [DecidablePred g] :
    (univ.filter fun v : Fin (n + 1) → Bool => g (List.ofFn v)).card =
      (univ.filter fun w : Fin n → Bool => g (true :: List.ofFn w)).card +
        (univ.filter fun w : Fin n → Bool => g (false :: List.ofFn w)).card := by
  classical
  rw [← card_map (Fin.consEquiv fun _ => Bool).symm.toEmbedding]
  have hmap : (univ.filter fun v : Fin (n + 1) → Bool => g (List.ofFn v)).map
      (Fin.consEquiv fun _ => Bool).symm.toEmbedding =
      univ.filter fun x : Bool × (Fin n → Bool) => g (x.1 :: List.ofFn x.2) := by
    ext x
    simp only [mem_map_equiv, Equiv.symm_symm, mem_filter, mem_univ, true_and]
    change g (List.ofFn (Fin.cons x.1 x.2 : Fin (n + 1) → Bool)) ↔ _
    rw [List.ofFn_succ]
    simp
  rw [hmap, card_filter, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [card_filter]

/-- A bit string `w` has no `true` bits in `List.ofFn w` if and only if `w = 0`. -/
theorem not_any_ofFn_eq_true_iff {n : ℕ} (w : Fin n → Bool) :
    (!(List.ofFn w).any fun b => b) = true ↔ w = 0 := by
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false, List.mem_ofFn,
    forall_exists_index, forall_apply_eq_imp_iff, Bool.not_eq_true]
  exact ⟨fun h => funext h, fun h i => congrFun h i⟩

/-- Only the word of `false`s has no bit `true`. -/
theorem card_filter_not_any (n : ℕ) :
    (univ.filter fun w : Fin n → Bool => (!(List.ofFn w).any fun b => b) = true).card = 1 := by
  rw [card_eq_one]
  refine ⟨0, ext fun w => ?_⟩
  simp only [mem_filter, mem_univ, true_and, not_any_ofFn_eq_true_iff, mem_singleton]

/-- Only the word of `true`s has all bits `true`. -/
theorem card_filter_all (n : ℕ) :
    (univ.filter fun w : Fin n → Bool => ((List.ofFn w).all fun b => b) = true).card = 1 := by
  rw [card_eq_one]
  refine ⟨fun _ => true, ext fun w => ?_⟩
  simp only [mem_filter, mem_univ, true_and, List.all_eq_true, List.mem_ofFn,
    forall_exists_index, forall_apply_eq_imp_iff, mem_singleton]
  exact ⟨fun h => funext h, fun h i => by rw [h]⟩

/-- **Counting words by rows**: the words of `T` rows of `B` bits whose `j`-th row satisfies
`g j` for every `j` are counted by the product of the counts of the rows. -/
theorem card_filter_listRows_all (T B : ℕ) (g : ℕ → List Bool → Bool) :
    (univ.filter fun v : Fin (T * B) → Bool =>
      ((listRows T B (List.ofFn v)).zipIdx.all fun p => g p.2 p.1) = true).card =
      ∏ j : Fin T, (univ.filter fun w : Fin B → Bool => g j (List.ofFn w) = true).card := by
  classical
  have hrows (v : Fin (T * B) → Bool) : listRows T B (List.ofFn v) =
      List.ofFn fun j => List.ofFn (blocksEquiv v j) := by
    rw [listRows_eq_ofFn, ofList_ofFn]
    rfl
  have hall (F : Fin T → List Bool) :
      ((List.ofFn F).zipIdx.all fun p => g p.2 p.1) = true ↔ ∀ j : Fin T, g j (F j) = true := by
    simp only [List.all_eq_true, Prod.forall]
    constructor
    · intro h j
      apply h
      rw [List.mem_zipIdx_iff_getElem?]
      simp
    · intro h w i hw
      rw [List.mem_zipIdx_iff_getElem?, List.getElem?_ofFn] at hw
      simp only at hw
      split at hw
      · rename_i hi
        rw [← Option.some.inj hw]
        exact h ⟨i, hi⟩
      · exact absurd hw (by simp)
  rw [← Fintype.card_piFinset]
  refine card_equiv blocksEquiv fun v => ?_
  simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, hrows, hall]

/-- The unary word of `k ≤ K` bits `true` followed by `false`s. -/
theorem ofFn_decide_lt {K k : ℕ} (hk : k ≤ K) :
    List.ofFn (fun i : Fin K => decide ((i : ℕ) < k)) =
      List.replicate k true ++ List.replicate (K - k) false := by
  apply List.ext_getElem (by
    simp only [List.length_ofFn, List.length_append, List.length_replicate]
    omega)
  intro i h₁ h₂
  simp only [List.length_ofFn] at h₁
  rw [List.getElem_ofFn]
  by_cases hik : i < k
  · rw [List.getElem_append_left (by simpa using hik)]
    simp [hik]
  · rw [List.getElem_append_right (by simpa using hik)]
    simp [hik]

/-! ### The lexicographic order -/

/-- The lexicographic order on words of equal length: `x` is below `y` at the first position
where they differ. -/
def wordLt (x y : List Bool) : Bool :=
  (List.range x.length).any fun i =>
    ((List.range i).all fun j => x.getD j false == y.getD j false) &&
      (!x.getD i false && y.getD i false)

/-- On bit strings, `wordLt` is the lexicographic order. -/
theorem wordLt_ofFn_iff {n : ℕ} (x y : Fin n → Bool) :
    wordLt (List.ofFn x) (List.ofFn y) = true ↔ toLex x < toLex y := by
  change _ ↔ ∃ i, (∀ j, j < i → x j = y j) ∧ x i < y i
  simp only [wordLt, List.any_eq_true, List.mem_range, List.length_ofFn, Bool.and_eq_true,
    List.all_eq_true, beq_iff_eq, Bool.not_eq_true']
  constructor
  · rintro ⟨i, hi, hall, hx, hy⟩
    refine ⟨⟨i, hi⟩, fun j hj => ?_, ?_⟩
    · have := hall j hj
      rwa [List.getD_ofFn_of_lt x (by omega) false, List.getD_ofFn_of_lt y (by omega) false] at this
    · rw [List.getD_ofFn_of_lt x hi false] at hx
      rw [List.getD_ofFn_of_lt y hi false] at hy
      rw [hx, hy]
      decide
  · rintro ⟨i, hall, hlt⟩
    refine ⟨i, i.2, fun j hj => ?_, ?_, ?_⟩
    · rw [List.getD_ofFn_of_lt x (by omega) false, List.getD_ofFn_of_lt y (by omega) false]
      exact hall ⟨j, by omega⟩ hj
    · rw [List.getD_ofFn x i false]
      revert hlt
      cases x i <;> cases y i <;> decide
    · rw [List.getD_ofFn y i false]
      revert hlt
      cases x i <;> cases y i <;> decide

/-- Among all `n`-bit words, precisely `k` represent values below `k ≤ 2^n`. -/
theorem card_filter_binaryValue_lt {n k : ℕ} (hk : k ≤ 2 ^ n) :
    (Finset.univ.filter fun w : Fin n → Bool => binaryValue (List.ofFn w) < k).card = k := by
  classical
  rw [← Finset.card_range k]
  apply Finset.card_bij (fun w _ => binaryValue (List.ofFn w))
  · intro w hw
    simpa using hw
  · intro u hu v hv h
    exact List.ofFn_injective (binaryValue_injective_of_length_eq (by simp) h)
  · intro j hj
    obtain ⟨w, hw⟩ := exists_binaryValue_eq ((Finset.mem_range.mp hj).trans_le hk)
    exact ⟨w, by simpa [hw] using hj, hw⟩

/-! ### Parity, subsets, and binomial amplification -/

/-- A product of naturals is odd exactly when every factor is. -/
theorem odd_prod_iff {ι : Type*} {s : Finset ι} (f : ι → ℕ) :
    Odd (∏ j ∈ s, f j) ↔ ∀ j ∈ s, Odd (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Nat.odd_mul, ih, Finset.forall_mem_insert]

/-- **The parity form of a disjunction**: `1 + ∏ⱼ (1 + cⱼ)` is odd exactly when some `cⱼ` is
odd. -/
theorem odd_one_add_prod_one_add {ι : Type*} [Fintype ι] (c : ι → ℕ) :
    Odd (1 + ∏ j, (1 + c j)) ↔ ∃ j, Odd (c j) := by
  rw [Nat.add_comm, Nat.odd_add_one, odd_prod_iff]
  simp only [mem_univ, true_imp_iff, not_forall]
  refine exists_congr fun j => ?_
  rw [Nat.add_comm, Nat.odd_add_one, not_not]

/-- The functions `s : ι → X` whose values at the `t` distinct points `f i` lie in `F`: `F` is
chosen at those points and anything elsewhere. -/
theorem card_filter_forall_apply_mem {ι X : Type*} [Fintype ι] [DecidableEq ι] [Fintype X]
    [DecidableEq X] {t : ℕ} (f : Fin t → ι) (hf : Function.Injective f) (F : Finset X) :
    (univ.filter fun s : ι → X => ∀ i, s (f i) ∈ F).card =
      #F ^ t * Fintype.card X ^ (Fintype.card ι - t) := by
  classical
  have h : (univ.filter fun s : ι → X => ∀ i, s (f i) ∈ F) =
      Fintype.piFinset fun j => if j ∈ Finset.image f univ then F else univ := by
    ext s
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro hs j
      split
      · rename_i hj
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hj
        exact hs i
      · exact mem_univ _
    · intro hs i
      have := hs (f i)
      rwa [ite_eq_left_iff.2 (fun h => absurd (Finset.mem_image_of_mem f (mem_univ i)) h)]
        at this
  rw [h, Fintype.card_piFinset]
  simp only [apply_ite Finset.card, card_univ]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  have himg : (univ.filter fun j => j ∈ Finset.image f univ) = Finset.image f univ := by
    ext j; simp
  have hcard : #(Finset.image f univ) = t := by
    rw [Finset.card_image_of_injective _ hf, card_univ, Fintype.card_fin]
  rw [himg, hcard, Finset.filter_not, himg, Finset.card_sdiff_of_subset (subset_univ _), hcard,
    card_univ]

/-- **The union bound for random strings**: if each `x` is bad for at most a `2 ^ (-e')` fraction
of the random strings, some `x` of length `M` is bad for at most a `2 ^ (M - e')` fraction. -/
theorem two_pow_mul_card_filter_exists_le {R M e' : ℕ}
    {Bad : (Fin R → Bool) → (Fin M → Bool) → Prop}
    [∀ r x, Decidable (Bad r x)]
    (h : ∀ x, 2 ^ e' * (univ.filter fun r => Bad r x).card ≤ 2 ^ R) :
    2 ^ e' * (univ.filter fun r => ∃ x, Bad r x).card ≤ 2 ^ M * 2 ^ R := by
  classical
  have hsub : (univ.filter fun r => ∃ x, Bad r x) ⊆
      univ.biUnion fun x => univ.filter fun r => Bad r x := by
    intro r hr
    simp only [mem_filter, mem_univ, true_and] at hr
    obtain ⟨x, hx⟩ := hr
    exact mem_biUnion.2 ⟨x, mem_univ _, by simpa using hx⟩
  calc 2 ^ e' * (univ.filter fun r => ∃ x, Bad r x).card
      ≤ 2 ^ e' * ∑ x, (univ.filter fun r => Bad r x).card :=
        Nat.mul_le_mul_left _ ((card_le_card hsub).trans card_biUnion_le)
    _ = ∑ x : Fin M → Bool, 2 ^ e' * (univ.filter fun r => Bad r x).card := mul_sum ..
    _ ≤ ∑ _x : Fin M → Bool, 2 ^ R := sum_le_sum fun x _ => h x
    _ = 2 ^ M * 2 ^ R := by simp

/-- **The parity of `c` from the binomial expansion of `(1 - 2) ^ c`**:
`∑ i < c, (-2) ^ i * choose c (i + 1)` is `1` for odd `c` and `0` for even `c`. -/
theorem sum_range_neg_two_pow_mul_choose (c : ℕ) :
    ∑ i ∈ range c, (-2 : ℤ) ^ i * (c.choose (i + 1) : ℤ) = if Odd c then 1 else 0 := by
  have hbin : ∑ i ∈ range (c + 1), (-2 : ℤ) ^ i * (c.choose i : ℤ) = (-1) ^ c := by
    have := add_pow (-2 : ℤ) 1 c
    simp only [one_pow, mul_one] at this
    rw [show (-2 : ℤ) + 1 = -1 by norm_num] at this
    rw [this]
  rw [sum_range_succ'] at hbin
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one] at hbin
  have h : -2 * ∑ i ∈ range c, (-2 : ℤ) ^ i * (c.choose (i + 1) : ℤ) = (-1) ^ c - 1 := by
    rw [mul_sum]
    rw [← hbin]
    simp only [pow_succ]
    ring_nf
  split
  · rename_i hc
    rw [hc.neg_one_pow] at h
    linarith
  · rename_i hc
    rw [(Nat.not_odd_iff_even.1 hc).neg_one_pow, sub_self] at h
    linarith

/-- **The parity of `c` modulo `2 ^ K`**: only the first `K` binomial terms matter. -/
theorem sum_range_neg_two_pow_mul_choose_zmod (c K : ℕ) :
    ∑ i ∈ range K, (-2 : ZMod (2 ^ K)) ^ i * (c.choose (i + 1) : ZMod (2 ^ K)) =
      if Odd c then 1 else 0 := by
  have hexact := congrArg (Int.cast : ℤ → ZMod (2 ^ K)) (sum_range_neg_two_pow_mul_choose c)
  push_cast at hexact
  rw [← hexact]
  have hK : (-2 : ZMod (2 ^ K)) ^ K = 0 := by
    have h2 : (2 : ZMod (2 ^ K)) ^ K = 0 := by
      exact_mod_cast ZMod.natCast_self (2 ^ K)
    rw [neg_pow, h2, mul_zero]
  have h₁ : ∑ i ∈ range (K + c), (-2 : ZMod (2 ^ K)) ^ i * (c.choose (i + 1) : ZMod (2 ^ K)) =
      ∑ i ∈ range K, (-2 : ZMod (2 ^ K)) ^ i * (c.choose (i + 1) : ZMod (2 ^ K)) := by
    rw [sum_range_add]
    simp [pow_add, hK]
  have h₂ : ∑ i ∈ range (c + K), (-2 : ZMod (2 ^ K)) ^ i * (c.choose (i + 1) : ZMod (2 ^ K)) =
      ∑ i ∈ range c, (-2 : ZMod (2 ^ K)) ^ i * (c.choose (i + 1) : ZMod (2 ^ K)) := by
    rw [sum_range_add]
    simp [Nat.choose_eq_zero_of_lt (by omega : c < c + _ + 1)]
  rw [← h₁, ← h₂, Nat.add_comm]

/-- **Strictly increasing tuples count subsets**: the strictly increasing `k`-tuples of elements
of `A` are as many as the `k`-element subsets of `A`. -/
theorem card_filter_strictMono {β : Type*} [LinearOrder β] [Fintype β] (A : Finset β) (k : ℕ)
    [DecidablePred fun g : Fin k → β => StrictMono g ∧ ∀ i, g i ∈ A] :
    (univ.filter fun g : Fin k → β => StrictMono g ∧ ∀ i, g i ∈ A).card = (#A).choose k := by
  classical
  rw [← card_powersetCard]
  refine card_bij (fun g _ => univ.image g) ?_ ?_ ?_
  · intro g hg
    simp only [mem_filter, mem_univ, true_and] at hg
    rw [mem_powersetCard]
    refine ⟨fun x hx => ?_, ?_⟩
    · obtain ⟨i, -, rfl⟩ := mem_image.1 hx
      exact hg.2 i
    · rw [card_image_of_injective _ hg.1.injective, card_univ, Fintype.card_fin]
  · intro g hg g' hg' h
    simp only [mem_filter, mem_univ, true_and] at hg hg'
    have hc : (univ.image g).card = k := by
      rw [card_image_of_injective _ hg.1.injective, card_univ, Fintype.card_fin]
    have h1 : g = (univ.image g).orderEmbOfFin hc :=
      orderEmbOfFin_unique hc (fun i => mem_image_of_mem g (mem_univ i)) hg.1
    have h2 : g' = (univ.image g).orderEmbOfFin hc :=
      orderEmbOfFin_unique hc (fun i => h ▸ mem_image_of_mem g' (mem_univ i)) hg'.1
    rw [h1, ← h2]
  · intro s hs
    rw [mem_powersetCard] at hs
    refine ⟨s.orderEmbOfFin hs.2, ?_, image_orderEmbOfFin_univ s hs.2⟩
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨(s.orderEmbOfFin hs.2).strictMono, fun i => hs.1 (orderEmbOfFin_mem s hs.2 i)⟩

/-- A tuple increasing at every step is strictly increasing. -/
theorem strictMono_of_lt_succ {β : Type*} [Preorder β] {k : ℕ} {g : Fin k → β}
    (h : ∀ (i : ℕ) (hi : i + 1 < k), g ⟨i, by omega⟩ < g ⟨i + 1, hi⟩) : StrictMono g := by
  cases k with
  | zero => exact fun i => i.elim0
  | succ k => exact Fin.strictMono_iff_lt_succ.2 fun i => h i (by omega)

end Cslib.BitString


