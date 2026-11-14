-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Foundations_Data_BitString_Threshold
-- name    : Complexitylib_0ebd467_Foundations_Data_BitString_Threshold
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:33:39.160586+00:00
-- url     : https://prove2.me/theorems/719b39f7-710d-4ffe-9f28-10e9acebcc28
-- title:
--   Complexity.Foundations.Data.BitString.Threshold — Threshold, majority and symmetric Boolean functions
-- statement:
--   This is module `Complexity.Foundations.Data.BitString.Threshold` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   The threshold function `threshold n j` says that at least `j` of `n` bits are true, and majority
--   (`majority`, at least half) and strict majority (`strictMajority`, more than half) are threshold
--   functions. On an arbitrary finite set of voting indices, `BitString.strictMajorityOn` chooses
--   `false` on a tie. A Boolean function is *symmetric* when it depends only on the weight of its input
--   (`BooleanFunction.IsSymmetric`), and then it factors through the weight
--   (`BooleanFunction.IsSymmetric.exists_eq_comp_weight`) [Jukna, Chapter 1][Jukna2012].
--
--   ### Main definitions
--
--   * `Cslib.BitString.strictMajorityOn`: strict majority on a finite set of voting indices.
--   * `Cslib.threshold`, `Cslib.majority`, `Cslib.strictMajority`: threshold functions.
--   * `Cslib.BooleanFunction.IsSymmetric`: Boolean functions depending only on the weight.
--
--   ### Main results
--
--   * `Cslib.monotone_threshold`: threshold functions are monotone.
--   * `Cslib.strictMajority_not`: strict majority of the negated bits is the negation of majority.
--   * `Cslib.le_card_ne_of_strictMajority_ne`,
--     `Cslib.BitString.card_filter_eq_le_half_of_strictMajorityOn_ne`: a wrong majority requires at
--     least half wrong votes.
--   * `Cslib.BooleanFunction.IsSymmetric.exists_eq_comp_weight`: symmetric functions factor through the
--     weight.
--   * `Cslib.isSymmetric_threshold`, `Cslib.isSymmetric_majority`, `Cslib.isSymmetric_strictMajority`:
--     threshold functions are symmetric.
--
--   ### References
--
--   * [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
--
--   **Contents.** The module is published as a whole: 24 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_BitString_Threshold`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Foundations/Data/BitString/Threshold.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_BitString_Weight

/- Prove2me definition bundle for `Complexity.Foundations.Data.BitString.Threshold` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Threshold, majority and symmetric Boolean functions

The threshold function `threshold n j` says that at least `j` of `n` bits are true, and majority
(`majority`, at least half) and strict majority (`strictMajority`, more than half) are threshold
functions. On an arbitrary finite set of voting indices, `BitString.strictMajorityOn` chooses
`false` on a tie. A Boolean function is *symmetric* when it depends only on the weight of its input
(`BooleanFunction.IsSymmetric`), and then it factors through the weight
(`BooleanFunction.IsSymmetric.exists_eq_comp_weight`) [Jukna, Chapter 1][Jukna2012].

## Main definitions

* `Cslib.BitString.strictMajorityOn`: strict majority on a finite set of voting indices.
* `Cslib.threshold`, `Cslib.majority`, `Cslib.strictMajority`: threshold functions.
* `Cslib.BooleanFunction.IsSymmetric`: Boolean functions depending only on the weight.

## Main results

* `Cslib.monotone_threshold`: threshold functions are monotone.
* `Cslib.strictMajority_not`: strict majority of the negated bits is the negation of majority.
* `Cslib.le_card_ne_of_strictMajority_ne`,
  `Cslib.BitString.card_filter_eq_le_half_of_strictMajorityOn_ne`: a wrong majority requires at
  least half wrong votes.
* `Cslib.BooleanFunction.IsSymmetric.exists_eq_comp_weight`: symmetric functions factor through the
  weight.
* `Cslib.isSymmetric_threshold`, `Cslib.isSymmetric_majority`, `Cslib.isSymmetric_strictMajority`:
  threshold functions are symmetric.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib

open Finset

namespace BitString

variable {ι : Type*}

/-- Strict majority of the coordinates in `s`, choosing `false` on a tie. -/
def strictMajorityOn (s : Finset ι) (vote : ι → Bool) : Bool :=
  decide (s.card / 2 < (s.filter fun i => vote i).card)

/-- If strict majority is wrong, at most half of the votes are correct. -/
theorem card_filter_eq_le_half_of_strictMajorityOn_ne (s : Finset ι) (vote : ι → Bool)
    (bit : Bool) (h : strictMajorityOn s vote ≠ bit) :
    (s.filter fun i => vote i = bit).card ≤ s.card / 2 := by
  have hsplit := card_filter_add_card_filter_not (s := s) (fun i => vote i = true)
  cases bit with
  | true => simpa [strictMajorityOn] using h
  | false =>
    simp only [Bool.not_eq_true] at hsplit
    have : s.card / 2 < (s.filter fun i => vote i = true).card := by
      simpa [strictMajorityOn] using h
    lia

/-- A nonempty constant vote has its constant value. -/
@[simp] theorem strictMajorityOn_const (s : Finset ι) (hs : s.Nonempty) (bit : Bool) :
    strictMajorityOn s (fun _ => bit) = bit := by
  cases bit <;> simp [strictMajorityOn, Nat.div_lt_self hs.card_pos Nat.one_lt_two]

end BitString

open BitString

variable {n : ℕ}

/-- The threshold function `Th^n_j` on `n` bits: whether at least `j` of them are true. -/
def threshold (n j : ℕ) : BooleanFunction n :=
  fun x => decide (j ≤ weight x)

/-- The majority function on `n` bits: whether at least half of them are true, that is, the
threshold function `Th^n_⌈n/2⌉`. -/
def majority (n : ℕ) : BooleanFunction n :=
  threshold n ((n + 1) / 2)

/-- The strict majority function on `n` bits: whether more than half of them are true, so that a
tie is false. It is the threshold function `Th^n_{⌊n/2⌋+1}`. -/
def strictMajority (n : ℕ) : BooleanFunction n :=
  threshold n (n / 2 + 1)

/-- `threshold n j x` is the decision of `j ≤ weight x`. -/
theorem threshold_apply (j : ℕ) (x : BitString n) : threshold n j x = decide (j ≤ weight x) :=
  rfl

/-- The threshold function `Th^n_j` is true exactly when at least `j` bits are true. -/
theorem threshold_eq_true_iff {j : ℕ} {x : BitString n} :
    threshold n j x = true ↔ j ≤ weight x := by
  simp [threshold]

/-- Threshold functions are monotone. -/
theorem monotone_threshold (j : ℕ) : Monotone (threshold n j) := fun _ _ hxy => by
  rw [threshold_apply, threshold_apply]
  exact Bool.le_iff_imp.2 fun h =>
    decide_eq_true ((of_decide_eq_true h).trans (monotone_weight hxy))

/-- With cutoff `0`, the threshold function is the constant `true`. -/
@[simp] theorem threshold_zero_right (x : BitString n) : threshold n 0 x = true :=
  threshold_eq_true_iff.2 (Nat.zero_le _)

/-- With a cutoff above `n`, the threshold function is the constant `false`. -/
theorem threshold_eq_false_of_lt {j : ℕ} (h : n < j) (x : BitString n) :
    threshold n j x = false := by
  have := weight_le_length x
  rw [← Bool.not_eq_true, threshold_eq_true_iff]
  omega

/-- With cutoff `1`, the threshold function is the disjunction. -/
theorem threshold_one_right (x : BitString n) : threshold n 1 x = decide (∃ i, x i = true) := by
  rw [Bool.eq_iff_iff, threshold_eq_true_iff, decide_eq_true_iff, weight, one_le_card,
    filter_nonempty_iff]
  simp

/-- With cutoff `n`, the threshold function is the conjunction. -/
theorem threshold_self (x : BitString n) : threshold n n x = decide (∀ i, x i = true) := by
  have h := weight_le_length x
  have key : #{i | x i = true} = n ↔ ({i | x i = true} : Finset (Fin n)) = univ := by
    rw [← card_eq_iff_eq_univ, Fintype.card_fin]
  rw [Bool.eq_iff_iff, threshold_eq_true_iff, decide_eq_true_iff,
    show n ≤ weight x ↔ weight x = n by omega, weight, key, filter_eq_self]
  simp

/-- Majority is true exactly when at least `⌈n/2⌉ = (n + 1) / 2` bits are true. -/
theorem majority_eq_true_iff {x : BitString n} :
    majority n x = true ↔ (n + 1) / 2 ≤ weight x :=
  threshold_eq_true_iff

/-- Strict majority is true exactly when more than `n / 2` bits are true. -/
theorem strictMajority_eq_true_iff {x : BitString n} :
    strictMajority n x = true ↔ n / 2 < weight x :=
  threshold_eq_true_iff

/-- Strict majority is false exactly when at most `n / 2` bits are true. -/
theorem strictMajority_eq_false_iff {x : BitString n} :
    strictMajority n x = false ↔ weight x ≤ n / 2 := by
  rw [← Bool.not_eq_true, strictMajority_eq_true_iff, not_lt]

/-- Strict majority on all coordinates agrees with the finite-set operation. -/
theorem strictMajority_eq_strictMajorityOn (x : BitString n) :
    strictMajority n x = BitString.strictMajorityOn univ x := by
  apply Bool.eq_iff_iff.mpr
  simp [strictMajority_eq_true_iff, BitString.strictMajorityOn, weight]

/-- If the strict majority of `n` bits is not `y`, at least `n - n / 2` differ from `y`. -/
theorem le_card_ne_of_strictMajority_ne {x : BitString n} {y : Bool}
    (h : strictMajority n x ≠ y) : n - n / 2 ≤ #{i | x i ≠ y} := by
  rw [strictMajority_eq_strictMajorityOn] at h
  have hcorrect := card_filter_eq_le_half_of_strictMajorityOn_ne univ x y h
  have hsplit := card_filter_add_card_filter_not (s := univ) (fun i => x i = y)
  simp only [card_univ, Fintype.card_fin] at hcorrect hsplit
  lia

/-- Strict majority of the negated bits is the negation of majority: fewer than half of the bits
are true exactly when not at least half of them are. -/
theorem strictMajority_not (x : BitString n) :
    strictMajority n (fun i => !x i) = !majority n x := by
  have h := weight_not x
  have hle := weight_le_length x
  simp only [Fintype.card_fin] at h
  rw [Bool.eq_iff_iff, strictMajority_eq_true_iff, Bool.not_eq_true', ← Bool.not_eq_true,
    majority_eq_true_iff, h]
  omega

namespace BooleanFunction

/-- A Boolean function is *symmetric* when it depends only on the weight of its input. -/
def IsSymmetric (f : BooleanFunction n) : Prop :=
  ∀ x y, weight x = weight y → f x = f y

/-- A symmetric function factors through the weight. -/
theorem IsSymmetric.exists_eq_comp_weight {f : BooleanFunction n} (hf : f.IsSymmetric) :
    ∃ a : ℕ → Bool, ∀ x, a (weight x) = f x := by
  classical
  refine ⟨fun w => decide (∃ x, weight x = w ∧ f x = true), fun x => Bool.eq_iff_iff.2 ?_⟩
  simp only [decide_eq_true_eq]
  exact ⟨fun ⟨y, hy, hfy⟩ => hf y x hy ▸ hfy, fun hx => ⟨x, rfl, hx⟩⟩

end BooleanFunction

/-- Threshold functions are symmetric. -/
theorem isSymmetric_threshold (j : ℕ) : (threshold n j).IsSymmetric := fun x y h => by
  simp only [threshold, h]

/-- Majority is symmetric. -/
theorem isSymmetric_majority : (majority n).IsSymmetric :=
  isSymmetric_threshold _

/-- Strict majority is symmetric. -/
theorem isSymmetric_strictMajority : (strictMajority n).IsSymmetric :=
  isSymmetric_threshold _

end Cslib


