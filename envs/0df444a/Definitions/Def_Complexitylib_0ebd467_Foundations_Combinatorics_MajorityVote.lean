-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Foundations_Combinatorics_MajorityVote
-- name    : Complexitylib_0ebd467_Foundations_Combinatorics_MajorityVote
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:32:56.070833+00:00
-- url     : https://prove2.me/theorems/1fcb9d20-231a-4ee7-b4c4-eb1fa96b4ffc
-- title:
--   Complexity.Foundations.Combinatorics.MajorityVote — Majority votes
-- statement:
--   This is module `Complexity.Foundations.Combinatorics.MajorityVote` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   If at least two thirds of the elements of a finite type `Ω` are *good*, then among the tuples
--   of `2 r` elements of `Ω`, those in which at most half of the entries are good make up at most an
--   `(8 / 9) ^ r` fraction. This is the error bound for repeating a bounded-error test `2 r` times
--   independently and taking the majority answer, in counting form.
--
--   The proof is the exponential-moment (Chernoff) argument with weight `2` on the bad elements: the
--   weights of all tuples sum to `(|good| + 2 |bad|) ^ (2 r) ≤ (4 |Ω| / 3) ^ (2 r)`, and a tuple with
--   at most `r` good entries has weight at least `2 ^ r`.
--
--   ### Main results
--
--   * `Cslib.card_filter_card_filter_le_le`: the bound.
--   * `Cslib.exists_forall_lt_card_filter_mem`: for a family of at most `2 ^ n` tests, each passed by
--     two thirds of `Ω`, some `12 (n + 1)` elements of `Ω` contain a majority passing each test.
--   * `Cslib.exists_forall_exists_apply_mem`: for a family of at most `2 ^ n` tests, each passed by
--     half of `Ω`, some `n + 1` elements of `Ω` contain one passing each test; this is the exact
--     finite-cover union bound with failure ratio `1 / 2`.
--   * `Cslib.two_pow_mul_eight_pow_lt`: the numeric bound `2 ^ n * 8 ^ (6 n + 6) < 9 ^ (6 n + 6)`
--     behind the choice of `12 (n + 1)` repetitions.
--
--   ### References
--
--   * [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 7.4][AroraBarak09]
--
--   **Contents.** The module is published as a whole: 5 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Foundations_Combinatorics_MajorityVote`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Foundations/Combinatorics/MajorityVote.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Batteries.Tactic.Lint.Basic
public import Mathlib.Init
public import Mathlib.Tactic.Common
public import Definitions.Def_Cslib_254e30e_Tactic_GrindAttrs
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Pi
import Definitions.Def_Complexitylib_0ebd467_Foundations_Combinatorics_FiniteCover_Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/- Prove2me definition bundle for `Complexity.Foundations.Combinatorics.MajorityVote` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Majority votes

If at least two thirds of the elements of a finite type `Ω` are *good*, then among the tuples
of `2 r` elements of `Ω`, those in which at most half of the entries are good make up at most an
`(8 / 9) ^ r` fraction. This is the error bound for repeating a bounded-error test `2 r` times
independently and taking the majority answer, in counting form.

The proof is the exponential-moment (Chernoff) argument with weight `2` on the bad elements: the
weights of all tuples sum to `(|good| + 2 |bad|) ^ (2 r) ≤ (4 |Ω| / 3) ^ (2 r)`, and a tuple with
at most `r` good entries has weight at least `2 ^ r`.

## Main results

* `Cslib.card_filter_card_filter_le_le`: the bound.
* `Cslib.exists_forall_lt_card_filter_mem`: for a family of at most `2 ^ n` tests, each passed by
  two thirds of `Ω`, some `12 (n + 1)` elements of `Ω` contain a majority passing each test.
* `Cslib.exists_forall_exists_apply_mem`: for a family of at most `2 ^ n` tests, each passed by
  half of `Ω`, some `n + 1` elements of `Ω` contain one passing each test; this is the exact
  finite-cover union bound with failure ratio `1 / 2`.
* `Cslib.two_pow_mul_eight_pow_lt`: the numeric bound `2 ^ n * 8 ^ (6 n + 6) < 9 ^ (6 n + 6)`
  behind the choice of `12 (n + 1)` repetitions.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 7.4][AroraBarak09]
-/

@[expose] public section

namespace Cslib

open Finset

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

private theorem sum_prod_weight (G : Finset Ω) (m : ℕ) :
    ∑ ω : Fin m → Ω, ∏ i, (if ω i ∈ G then 1 else 2) =
      (G.card + 2 * (Fintype.card Ω - G.card)) ^ m := by
  rw [← Fintype.sum_pow (f := fun a => if a ∈ G then 1 else 2), Finset.sum_ite, Finset.sum_const,
    Finset.sum_const, smul_eq_mul,
    smul_eq_mul, mul_one, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.filter_not,
    Finset.filter_mem_eq_inter, Finset.univ_inter, ← Finset.compl_eq_univ_sdiff,
    Finset.card_compl, mul_comm]

/-- **Majority votes.** If at least two thirds of `Ω` lie in `G`, then at most an `(8 / 9) ^ r`
fraction of the `2 r`-tuples have at most `r` entries in `G`. -/
theorem card_filter_card_filter_le_le (G : Finset Ω) (hG : 2 * Fintype.card Ω ≤ 3 * G.card)
    (r : ℕ) :
    9 ^ r * (univ.filter fun ω : Fin (2 * r) → Ω => (univ.filter fun i => ω i ∈ G).card ≤ r).card
      ≤ 8 ^ r * Fintype.card Ω ^ (2 * r) := by
  set N := Fintype.card Ω
  set bad := univ.filter fun ω : Fin (2 * r) → Ω => (univ.filter fun i => ω i ∈ G).card ≤ r
  -- A bad tuple has weight at least `2 ^ r`.
  have hweight : ∀ ω ∈ bad, 2 ^ r ≤ ∏ i, (if ω i ∈ G then 1 else 2) := by
    intro ω hω
    have hω := (mem_filter.1 hω).2
    rw [Finset.prod_ite, Finset.prod_const_one, Finset.prod_const, one_mul]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin (2 * r))))
      (fun i => ω i ∈ G)
    rw [Finset.card_univ, Fintype.card_fin] at this
    omega
  have hmarkov : 2 ^ r * bad.card ≤ (G.card + 2 * (N - G.card)) ^ (2 * r) := by
    rw [← sum_prod_weight, mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    exact (Finset.sum_le_sum hweight).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => Nat.zero_le _)
  have hG' : G.card ≤ N := Finset.card_le_univ G
  have hthree : 3 * (G.card + 2 * (N - G.card)) ≤ 4 * N := by omega
  have key : 2 ^ r * (9 ^ r * bad.card) ≤ 2 ^ r * (8 ^ r * N ^ (2 * r)) := by
    calc 2 ^ r * (9 ^ r * bad.card) = 9 ^ r * (2 ^ r * bad.card) := by ring
      _ ≤ 9 ^ r * (G.card + 2 * (N - G.card)) ^ (2 * r) := Nat.mul_le_mul_left _ hmarkov
      _ = (3 * (G.card + 2 * (N - G.card))) ^ (2 * r) := by rw [mul_pow, pow_mul 3 2 r]; norm_num
      _ ≤ (4 * N) ^ (2 * r) := Nat.pow_le_pow_left hthree _
      _ = 2 ^ r * (8 ^ r * N ^ (2 * r)) := by
        rw [mul_pow, pow_mul, ← mul_assoc, ← mul_pow]; norm_num
  exact Nat.le_of_mul_le_mul_left key (by positivity)

/-- For any `n`, `2 ^ n * 8 ^ (6 * n + 6) < 9 ^ (6 * n + 6)`, since `2 * 8 ^ 6 < 9 ^ 6`. -/
theorem two_pow_mul_eight_pow_lt (n : ℕ) : 2 ^ n * 8 ^ (6 * n + 6) < 9 ^ (6 * n + 6) := by
  calc 2 ^ n * 8 ^ (6 * n + 6) = (2 * 8 ^ 6) ^ n * 8 ^ 6 := by
        rw [mul_pow, pow_add, pow_mul]; ring
    _ < (9 ^ 6) ^ n * 9 ^ 6 :=
      Nat.mul_lt_mul_of_le_of_lt (Nat.pow_le_pow_left (by norm_num) n) (by norm_num)
        (by positivity)
    _ = 9 ^ (6 * n + 6) := by rw [pow_add, pow_mul]

/-- **Majority votes good for many tests at once.** If each of at most `2 ^ n` tests is passed by
at least two thirds of `Ω`, then some `12 (n + 1)` elements of `Ω` contain more than `6 (n + 1)`
elements passing each test. -/
theorem exists_forall_lt_card_filter_mem {X : Type*} [Fintype X] [Nonempty Ω] {n : ℕ}
    (hX : Fintype.card X ≤ 2 ^ n) (good : X → Finset Ω)
    (hgood : ∀ x, 2 * Fintype.card Ω ≤ 3 * (good x).card) :
    ∃ ω : Fin (2 * (6 * n + 6)) → Ω, ∀ x,
      6 * n + 6 < (univ.filter fun i => ω i ∈ good x).card := by
  by_contra! h
  set R := 6 * n + 6
  set N := Fintype.card Ω
  let bad : X → Finset (Fin (2 * R) → Ω) := fun x =>
    univ.filter fun ω => (univ.filter fun i => ω i ∈ good x).card ≤ R
  have hcover : (univ : Finset (Fin (2 * R) → Ω)) ⊆ univ.biUnion bad := fun ω _ => by
    obtain ⟨x, hx⟩ := h ω
    exact mem_biUnion.2 ⟨x, mem_univ _, mem_filter.2 ⟨mem_univ _, hx⟩⟩
  have hcard := (card_le_card hcover).trans card_biUnion_le
  rw [card_univ, Fintype.card_fun, Fintype.card_fin] at hcard
  have hsum : 9 ^ R * ∑ x, (bad x).card ≤ 2 ^ n * (8 ^ R * N ^ (2 * R)) := by
    rw [mul_sum]
    calc ∑ x, 9 ^ R * (bad x).card ≤ ∑ _x : X, 8 ^ R * N ^ (2 * R) :=
          sum_le_sum fun x _ => card_filter_card_filter_le_le (good x) (hgood x) R
      _ ≤ 2 ^ n * (8 ^ R * N ^ (2 * R)) := by
          rw [sum_const, card_univ, smul_eq_mul]
          exact Nat.mul_le_mul_right _ hX
  have hpos : 0 < N ^ (2 * R) := pow_pos Fintype.card_pos _
  have := (Nat.mul_le_mul_left (9 ^ R) hcard).trans hsum
  rw [← mul_assoc] at this
  exact absurd (this.trans_lt (Nat.mul_lt_mul_of_pos_right (two_pow_mul_eight_pow_lt n) hpos))
    (lt_irrefl _)

omit [DecidableEq Ω] in
/-- **One good element for many tests at once.** If each of at most `2 ^ n` tests is passed by at
least half of `Ω`, then some `n + 1` elements of `Ω` contain one passing each test. -/
theorem exists_forall_exists_apply_mem {X : Type*} [Fintype X] [Nonempty Ω] {n : ℕ}
    (hX : Fintype.card X ≤ 2 ^ n) (good : X → Finset Ω)
    (hgood : ∀ x, Fintype.card Ω ≤ 2 * (good x).card) :
    ∃ ω : Fin (n + 1) → Ω, ∀ x, ∃ i, ω i ∈ good x := by
  classical
  apply exists_cover_of_scaled_card_lt (fun ω x => ω ∈ good x) 1 2 (n + 1)
  · intro x
    rw [Fintype.card_subtype_compl, Fintype.card_coe]
    have := hgood x
    have := card_le_univ (good x)
    lia
  · simpa only [one_pow, mul_one] using
      hX.trans_lt (Nat.pow_lt_pow_right (by decide) (by lia))

end Cslib


