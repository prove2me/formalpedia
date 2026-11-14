-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Foundations_Data_BitString_Weight
-- name    : Complexitylib_0ebd467_Foundations_Data_BitString_Weight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:33:14.893433+00:00
-- url     : https://prove2.me/theorems/3cba63d8-4aae-4482-993b-6dca1dacdadc
-- title:
--   Complexity.Foundations.Data.BitString.Weight — Hamming weight and binary Hamming balls
-- statement:
--   This is module `Complexity.Foundations.Data.BitString.Weight` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   The weight of a Boolean vector is its number of true coordinates (`BitString.weight`), Mathlib's
--   Hamming norm with `false` as `0` (`BitString.weight_eq_hammingNorm`), so the Hamming distance of two
--   bit strings is the weight of their sum (`BitString.hammingDist_eq_weight_add`)
--   [MacWilliams and Sloane, Chapter 1][MacWilliamsSloane1977]. For `x : BitString n`, the weight is the
--   number of `true` entries of `List.ofFn x` (`BitString.count_true_ofFn`) and is at most `n`
--   (`BitString.weight_le_length`). The words of weight `k` in `BitString n` form the `k`-th layer of
--   the cube (`BitString.weightLayer`), of size `n.choose k` (`BitString.card_weightLayer`), and the
--   words of weight at most `e` form a Hamming ball of size `B(n, e) = ∑ j ∈ range (e + 1), n.choose j`
--   (`BitString.ballSize`, `BitString.card_filter_weight_le`,
--   `BitString.card_filter_weight_le_eq_ballSize`).
--
--   ### Main definitions
--
--   * `Cslib.BitString.weight`: the number of true coordinates.
--   * `Cslib.BitString.weightLayer`: the strings of `n` bits of a given weight.
--   * `Cslib.BitString.ballSize`: the size `∑ j ∈ range (e + 1), q.choose j` of the binary Hamming ball
--     of radius `e` in `BitString q`.
--
--   ### Main results
--
--   * `Cslib.BitString.weight_eq_hammingNorm`, `Cslib.BitString.hammingDist_eq_weight_add`: the
--     weight is the Hamming norm.
--   * `Cslib.BitString.weight_le`, `Cslib.BitString.weight_le_length`: the weight is at most the number
--     of coordinates.
--   * `Cslib.BitString.count_true_ofFn`: `(List.ofFn x).count true = weight x`.
--   * `Cslib.BitString.monotone_weight`: the weight is monotone.
--   * `Cslib.BitString.card_weightLayer`: there are `n.choose k` strings of `n` bits of weight `k`.
--   * `Cslib.BitString.card_filter_weight_le`, `Cslib.BitString.card_filter_weight_le_eq_ballSize`: the
--     exact binomial-sum size of a Hamming ball.
--   * `Cslib.BitString.ballSize_succ_succ`: Pascal recurrence for Hamming-ball sizes.
--   * `Cslib.BitString.card_image_le_sum_choose`: bound a finite family of words by a Hamming ball.
--
--   ### References
--
--   * [F. J. MacWilliams, N. J. A. Sloane, *The Theory of Error-Correcting Codes*]
--     [MacWilliamsSloane1977]
--
--   **Contents.** The module is published as a whole: 30 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_BitString_Weight`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Foundations/Data/BitString/Weight.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Definitions.Def_Cslib_254e30e_Foundations_Data_BitString
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.InformationTheory.Hamming
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset

/- Prove2me definition bundle for `Complexity.Foundations.Data.BitString.Weight` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Hamming weight and binary Hamming balls

The weight of a Boolean vector is its number of true coordinates (`BitString.weight`), Mathlib's
Hamming norm with `false` as `0` (`BitString.weight_eq_hammingNorm`), so the Hamming distance of two
bit strings is the weight of their sum (`BitString.hammingDist_eq_weight_add`)
[MacWilliams and Sloane, Chapter 1][MacWilliamsSloane1977]. For `x : BitString n`, the weight is the
number of `true` entries of `List.ofFn x` (`BitString.count_true_ofFn`) and is at most `n`
(`BitString.weight_le_length`). The words of weight `k` in `BitString n` form the `k`-th layer of
the cube (`BitString.weightLayer`), of size `n.choose k` (`BitString.card_weightLayer`), and the
words of weight at most `e` form a Hamming ball of size `B(n, e) = ∑ j ∈ range (e + 1), n.choose j`
(`BitString.ballSize`, `BitString.card_filter_weight_le`,
`BitString.card_filter_weight_le_eq_ballSize`).

## Main definitions

* `Cslib.BitString.weight`: the number of true coordinates.
* `Cslib.BitString.weightLayer`: the strings of `n` bits of a given weight.
* `Cslib.BitString.ballSize`: the size `∑ j ∈ range (e + 1), q.choose j` of the binary Hamming ball
  of radius `e` in `BitString q`.

## Main results

* `Cslib.BitString.weight_eq_hammingNorm`, `Cslib.BitString.hammingDist_eq_weight_add`: the
  weight is the Hamming norm.
* `Cslib.BitString.weight_le`, `Cslib.BitString.weight_le_length`: the weight is at most the number
  of coordinates.
* `Cslib.BitString.count_true_ofFn`: `(List.ofFn x).count true = weight x`.
* `Cslib.BitString.monotone_weight`: the weight is monotone.
* `Cslib.BitString.card_weightLayer`: there are `n.choose k` strings of `n` bits of weight `k`.
* `Cslib.BitString.card_filter_weight_le`, `Cslib.BitString.card_filter_weight_le_eq_ballSize`: the
  exact binomial-sum size of a Hamming ball.
* `Cslib.BitString.ballSize_succ_succ`: Pascal recurrence for Hamming-ball sizes.
* `Cslib.BitString.card_image_le_sum_choose`: bound a finite family of words by a Hamming ball.

## References

* [F. J. MacWilliams, N. J. A. Sloane, *The Theory of Error-Correcting Codes*]
  [MacWilliamsSloane1977]
-/

@[expose] public section

namespace Cslib.BitString

open Finset

variable {ι : Type*} [Fintype ι]

/-- The Hamming weight of a Boolean vector: its number of true coordinates. -/
def weight (x : ι → Bool) : ℕ :=
  #{i | x i = true}

/-- The weight is the sum of the bits read as `0` and `1`. -/
theorem weight_eq_sum_toNat (x : ι → Bool) : weight x = ∑ i, (x i).toNat := by
  rw [weight, card_filter]
  exact sum_congr rfl fun i _ => by cases x i <;> rfl

/-- The weight is Mathlib's Hamming norm, the bit `false` being `0`. -/
theorem weight_eq_hammingNorm (x : ι → Bool) : weight x = hammingNorm x := by
  simp only [weight, hammingNorm, Bool.zero_eq_false, ne_eq, Bool.not_eq_false]

/-- The Hamming distance between two bit strings is the weight of their sum. -/
theorem hammingDist_eq_weight_add (x y : ι → Bool) : hammingDist x y = weight (x + y) := by
  rw [hammingDist_eq_hammingNorm, weight_eq_hammingNorm]
  exact congrArg hammingNorm (funext fun i => BooleanRing.sub_eq_add (x i) (y i))

/-- The weight is at most the number of coordinates. -/
theorem weight_le (x : ι → Bool) : weight x ≤ Fintype.card ι :=
  card_filter_le _ _

/-- The weight of an `n`-bit string is at most `n`. -/
theorem weight_le_length {n : ℕ} (x : BitString n) : weight x ≤ n := by
  simpa using weight_le x

/-- Complementary vectors have weights adding up to the number of coordinates. -/
theorem weight_not_add (x : ι → Bool) :
    weight (fun i => !x i) + weight x = Fintype.card ι := by
  rw [weight, weight, add_comm]
  simpa using card_filter_add_card_filter_not (s := univ) (fun i => x i = true)

/-- The weight of the complement is the number of coordinates minus the weight. -/
theorem weight_not (x : ι → Bool) : weight (fun i => !x i) = Fintype.card ι - weight x := by
  have := weight_not_add x
  omega

/-- The false coordinates of `x` number the coordinates minus the weight. -/
theorem card_filter_eq_false_eq_card_sub_weight (x : ι → Bool) :
    #{i | x i = false} = Fintype.card ι - weight x := by
  rw [← weight_not, weight]
  simp

/-- The weight is monotone in the pointwise order: setting bits cannot lower it. -/
theorem monotone_weight : Monotone (weight : (ι → Bool) → ℕ) := fun x y hxy =>
  card_le_card fun i hi => by
    have hxi : x i = true := (mem_filter.1 hi).2
    exact mem_filter.2 ⟨mem_univ i, le_antisymm (Bool.le_true _) (hxi ▸ hxy i)⟩

/-- The weight of a vector on `ι ⊕ κ` glued from `x` and `y` is the sum of their weights. -/
@[simp] theorem weight_sum_elim {κ : Type*} [Fintype κ] (x : ι → Bool) (y : κ → Bool) :
    weight (Sum.elim x y) = weight x + weight y := by
  simp only [weight_eq_sum_toNat, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]

/-- Splitting off the first bit of a word `z : Fin (q + 1) → Bool` in its Hamming weight. -/
theorem weight_cons_succ {q : ℕ} (z : Fin (q + 1) → Bool) :
    weight z = (z 0).toNat + weight (fun i : Fin q => z i.succ) := by
  simp only [weight_eq_sum_toNat, Fin.sum_univ_succ]

/-- The number of `true` entries in `List.ofFn x` is the weight of `x`. -/
@[simp] theorem count_true_ofFn {n : ℕ} (x : BitString n) :
    (List.ofFn x).count true = weight x := by
  induction n with
  | zero => simp [weight]
  | succ n ih =>
    rw [List.ofFn_succ, List.count_cons, ih, weight_cons_succ]
    cases x 0 <;> simp [Nat.add_comm]

/-- Setting a false coordinate to true adds one to the weight. -/
theorem weight_update_true [DecidableEq ι] {x : ι → Bool} {i : ι} (hi : x i = false) :
    weight (Function.update x i true) = weight x + 1 := by
  have he : ({j | Function.update x i true j = true} : Finset ι) =
      insert i ({j | x j = true} : Finset ι) := by
    ext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  rw [weight, he, card_insert_of_notMem (by simp [hi]), weight]

/-- Setting a true coordinate to false takes one from the weight. -/
theorem weight_update_false [DecidableEq ι] {x : ι → Bool} {i : ι} (hi : x i = true) :
    weight (Function.update x i false) + 1 = weight x := by
  have he : ({j | Function.update x i false j = true} : Finset ι) =
      ({j | x j = true} : Finset ι).erase i := by
    ext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  rw [weight, he, weight]
  exact card_erase_add_one (by simp [hi])

/-- The words `ι → Bool` of weight `r` number `|ι|.choose r`: they are the indicators of the
`r`-element sets of coordinates. -/
theorem card_filter_weight_eq [DecidableEq ι] (r : ℕ) :
    #{x : ι → Bool | weight x = r} = (Fintype.card ι).choose r := by
  refine (?_ : #{x : ι → Bool | weight x = r} = #(powersetCard r (univ : Finset ι))).trans
    (by rw [card_powersetCard, card_univ])
  refine card_nbij' (fun x => ({i | x i = true} : Finset ι)) (fun s i => decide (i ∈ s))
    (fun x hx => ?_) (fun s hs => ?_) (fun x _ => ?_) (fun s _ => ?_)
  · exact mem_powersetCard.2 ⟨subset_univ _, (mem_filter.1 hx).2⟩
  · refine mem_filter.2 ⟨mem_univ _, ?_⟩
    rw [← (mem_powersetCard.1 hs).2, weight]
    congr 1
    ext i
    simp
  · funext i
    simp
  · ext i
    simp

/-- The words of weight at most `e` form a Hamming ball with the exact binomial-sum size.
The radius may exceed the number of coordinates. -/
theorem card_filter_weight_le [DecidableEq ι] (e : ℕ) :
    #{x : ι → Bool | weight x ≤ e} =
      ∑ j ∈ Finset.range (e + 1), (Fintype.card ι).choose j := by
  classical
  simpa only [card_filter_weight_eq, Finset.mem_range, Nat.lt_succ_iff] using
    (Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset (ι → Bool)) (Finset.range (e + 1)) weight).symm

/-- Size `B(q, e) = ∑ j ∈ range (e + 1), q.choose j` of the Hamming ball of radius `e` in
`{0, 1}^q`. -/
def ballSize (q e : ℕ) : ℕ :=
  ∑ j ∈ range (e + 1), q.choose j

/-- The Hamming ball of any radius in the cube of dimension `0` has one point. -/
@[simp]
theorem ballSize_zero_left (e : ℕ) : ballSize 0 e = 1 := by
  induction e with
  | zero => simp [ballSize]
  | succ e ih =>
    rw [ballSize, sum_range_succ, Nat.choose_zero_succ, add_zero]
    exact ih

/-- The Hamming ball of radius `0` has one point. -/
@[simp]
theorem ballSize_zero_right (q : ℕ) : ballSize q 0 = 1 := by
  simp [ballSize]

/-- Hamming balls are nonempty: `0 < ballSize q e`. -/
theorem ballSize_pos (q e : ℕ) : 0 < ballSize q e := by
  rw [ballSize, sum_range_succ']
  simp

/-- Pascal recurrence `B(q + 1, e + 1) = B(q, e + 1) + B(q, e)` for Hamming-ball sizes. -/
theorem ballSize_succ_succ (q e : ℕ) :
    ballSize (q + 1) (e + 1) = ballSize q (e + 1) + ballSize q e := by
  have h1 := sum_range_succ' (fun k => (q + 1).choose k) (e + 1)
  have h2 := sum_range_succ' (fun k => q.choose k) (e + 1)
  simp only [Nat.choose_zero_right, Nat.choose_succ_succ, Nat.succ_eq_add_one,
    sum_add_distrib] at h1 h2
  unfold ballSize
  omega

/-- The number of words `z : Fin q → Bool` of weight at most `e` equals `ballSize q e`. -/
theorem card_filter_weight_le_eq_ballSize (q e : ℕ) :
    #{z : Fin q → Bool | weight z ≤ e} = ballSize q e := by
  simpa [ballSize] using card_filter_weight_le (ι := Fin q) e

/-- The weight of `x` as a number of true coordinates. -/
theorem weight_eq_card_subtype (x : ι → Bool) : weight x = Fintype.card {i // x i = true} :=
  (Fintype.card_subtype _).symm

/-- Selecting distinct coordinates cannot increase the number of true bits. -/
theorem weight_comp_le {κ : Type*} [Fintype κ] (x : ι → Bool) {f : κ → ι}
    (hf : Function.Injective f) : weight (x ∘ f) ≤ weight x := by
  rw [weight_eq_card_subtype, weight_eq_card_subtype]
  exact Fintype.card_le_of_injective
    (fun i : {i : κ // (x ∘ f) i = true} => (⟨f i, i.property⟩ : {j : ι // x j = true}))
    (fun _ _ h => Subtype.ext (hf (congrArg Subtype.val h)))

/-- A finite family of words of weight at most `e` attains at most the Hamming-ball size.
The map need not be injective, and the radius may exceed the number of coordinates. -/
theorem card_image_le_sum_choose {α : Type*} (s : Finset α) (f : α → ι → Bool) {e : ℕ}
    (h : ∀ x ∈ s, weight (f x) ≤ e) :
    (s.image f).card ≤ ∑ j ∈ range (e + 1), (Fintype.card ι).choose j := by
  classical
  calc
    _ ≤ #{z : ι → Bool | weight z ≤ e} := by
      apply card_le_card
      intro z hz
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
      exact mem_filter.mpr ⟨mem_univ _, h x hx⟩
    _ = _ := card_filter_weight_le e

/-- The *layer* of weight `k` of the cube: the strings of `n` bits with `k` true bits. -/
def weightLayer (n k : ℕ) : Finset (BitString n) :=
  {x | weight x = k}

/-- A string lies in the layer of weight `k` exactly when its weight is `k`. -/
@[simp] theorem mem_weightLayer {n k : ℕ} {x : BitString n} : x ∈ weightLayer n k ↔ weight x = k :=
  by simp [weightLayer]

/-- The layer of weight `k` has `n.choose k` strings. -/
theorem card_weightLayer (n k : ℕ) : #(weightLayer n k) = n.choose k := by
  rw [weightLayer, card_filter_weight_eq, Fintype.card_fin]

/-- The layer of weight `k` of the cube of `n` bits is nonempty when `k ≤ n`. -/
theorem weightLayer_nonempty {n k : ℕ} (hk : k ≤ n) : (weightLayer n k).Nonempty :=
  card_pos.1 (by rw [card_weightLayer]; exact Nat.choose_pos hk)

end Cslib.BitString


