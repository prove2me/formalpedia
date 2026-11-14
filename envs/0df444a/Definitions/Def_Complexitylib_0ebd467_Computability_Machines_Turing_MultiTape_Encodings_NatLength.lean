-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_NatLength
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_NatLength
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:45:08.808641+00:00
-- url     : https://prove2.me/theorems/24142128-4ee7-4249-bddf-d98318e5d125
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Encodings.NatLength — Binary lengths of natural numbers
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Encodings.NatLength` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   The binary encoding `encNat` of a number has `Nat.size` digits, so numbers below `2 ^ p` have at
--   most `p` digits. Numbers at most `N` have at most `log₂ N + 1` digits, and numbers at most
--   `(N + 1) ^ d` at most `(d + 1) * (log₂ N + 1)`: counters bounded by a polynomial in the length of
--   the input are stored in logarithmic space.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.length_encNat_le_of_lt_two_pow`: numbers below `2 ^ p` have at most `p`
--     digits.
--   * `Turing.MultiTapeTM.length_encNat_le_log2`: numbers at most `N` have at most `log₂ N + 1`
--     digits.
--   * `Turing.MultiTapeTM.length_encNat_le_log2_add_two`: numbers at most `N + 1` have at most
--     `log₂ N + 2` digits.
--   * `Turing.MultiTapeTM.length_encNat_le_of_le_pow`: numbers at most `(N + 1) ^ d` have at most
--     `(d + 1) * (log₂ N + 1)` digits.
--
--   * `Turing.MultiTapeTM.length_encNat_le_of_le_mul_pow`: the corresponding bound with a
--     constant coefficient.
--
--   ### References
--
--   * [M. Sipser, *Introduction to the Theory of Computation*, Section 8.4][Sipser2013]
--
--   **Contents.** The module is published as a whole: 5 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_NatLength`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Encodings/NatLength.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Nat
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Encodings.NatLength` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Binary lengths of natural numbers

The binary encoding `encNat` of a number has `Nat.size` digits, so numbers below `2 ^ p` have at
most `p` digits. Numbers at most `N` have at most `log₂ N + 1` digits, and numbers at most
`(N + 1) ^ d` at most `(d + 1) * (log₂ N + 1)`: counters bounded by a polynomial in the length of
the input are stored in logarithmic space.

## Main results

* `Turing.MultiTapeTM.length_encNat_le_of_lt_two_pow`: numbers below `2 ^ p` have at most `p`
  digits.
* `Turing.MultiTapeTM.length_encNat_le_log2`: numbers at most `N` have at most `log₂ N + 1`
  digits.
* `Turing.MultiTapeTM.length_encNat_le_log2_add_two`: numbers at most `N + 1` have at most
  `log₂ N + 2` digits.
* `Turing.MultiTapeTM.length_encNat_le_of_le_pow`: numbers at most `(N + 1) ^ d` have at most
  `(d + 1) * (log₂ N + 1)` digits.

* `Turing.MultiTapeTM.length_encNat_le_of_le_mul_pow`: the corresponding bound with a
  constant coefficient.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.4][Sipser2013]
-/

@[expose] public section

namespace Turing.MultiTapeTM

/-- A number below `2 ^ p` has at most `p` binary digits. -/
theorem length_encNat_le_of_lt_two_pow {a p : ℕ} (h : a < 2 ^ p) : (encNat a).length ≤ p := by
  rw [encNat_apply, Nat.size_eq_bits_len]
  exact Nat.size_le.mpr h

/-- The binary length of a number at most `N` is at most `log₂ N + 1`. -/
theorem length_encNat_le_log2 {j N : ℕ} (h : j ≤ N) : (encNat j).length ≤ Nat.log2 N + 1 := by
  rw [encNat_apply, Nat.size_eq_bits_len, Nat.size_le]
  exact lt_of_le_of_lt h Nat.lt_log2_self

/-- The binary length of a number at most `N + 1` is at most `log₂ N + 2`. -/
theorem length_encNat_le_log2_add_two {j N : ℕ} (h : j ≤ N + 1) :
    (encNat j).length ≤ Nat.log2 N + 2 := by
  rw [encNat_apply, Nat.size_eq_bits_len, Nat.size_le]
  have := Nat.lt_log2_self (n := N)
  rw [pow_succ]
  omega

/-- A number at most `(N + 1) ^ d` has at most `(d + 1) * (log₂ N + 1)` binary digits. -/
theorem length_encNat_le_of_le_pow {r N d : ℕ} (h : r ≤ (N + 1) ^ d) :
    (encNat r).length ≤ (d + 1) * (Nat.log2 N + 1) := by
  rw [encNat_apply, Nat.size_eq_bits_len, Nat.size_le]
  have h₁ : N + 1 ≤ 2 ^ (Nat.log2 N + 1) := Nat.lt_log2_self
  calc r ≤ (N + 1) ^ d := h
    _ ≤ (2 ^ (Nat.log2 N + 1)) ^ d := Nat.pow_le_pow_left h₁ d
    _ = 2 ^ (d * (Nat.log2 N + 1)) := by rw [← pow_mul, Nat.mul_comm]
    _ < 2 ^ ((d + 1) * (Nat.log2 N + 1)) :=
      Nat.pow_lt_pow_right (by norm_num) (by nlinarith)

/-- A number bounded by a constant times a fixed power has logarithmic binary length. -/
theorem length_encNat_le_of_le_mul_pow {M A D L : ℕ} (h : M ≤ A * (L + 1) ^ D) :
    (encNat M).length ≤ (Nat.size A + 2 * D + 1) * (Nat.log2 L + 1) := by
  have hp := length_encNat_le_of_le_pow (r := (L + 1) ^ D) (N := L) (d := D) le_rfl
  rw [encNat_apply, Nat.size_eq_bits_len] at hp ⊢
  have hM : M < 2 ^ (Nat.size A + (D + 1) * (Nat.log2 L + 1)) := by
    calc
      M ≤ A * (L + 1) ^ D := h
      _ < 2 ^ Nat.size A * 2 ^ ((D + 1) * (Nat.log2 L + 1)) :=
        Nat.mul_lt_mul'' (Nat.lt_size_self A) (Nat.size_le.mp hp)
      _ = _ := (pow_add ..).symm
  exact (Nat.size_le.mpr hM).trans (by nlinarith)

end Turing.MultiTapeTM


