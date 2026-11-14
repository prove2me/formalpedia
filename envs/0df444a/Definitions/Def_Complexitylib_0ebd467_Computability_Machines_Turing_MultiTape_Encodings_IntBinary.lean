-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_IntBinary
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_IntBinary
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:44:53.430192+00:00
-- url     : https://prove2.me/theorems/a296f4c5-8c9c-44cc-84d1-878441f8d254
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Encodings.IntBinary — Binary sign-magnitude integers
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Encodings.IntBinary` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   `encIntBin` encodes an integer by a sign bit, `true` for negative integers, followed by the binary
--   digits of its magnitude (`Turing.MultiTapeTM.encNat`), least significant first. The magnitude is
--   not framed: the sign is a single leading bit, the digits are the rest of the word, and the
--   magnitude is the tail of the code, so the binary natural arithmetic applies to it directly. A
--   negative integer has a nonzero magnitude, so zero has the single code `[false]`. An integer `z`
--   occupies `Nat.size z.natAbs + 1` bits. The unary integers `Turing.MultiTapeTM.encInt` index tape
--   positions; this encoding carries values whose magnitude is exponential in their length.
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.encIntBin`: integers as a sign bit followed by a binary magnitude.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.length_encIntBin`: the code of `z` has `Nat.size z.natAbs + 1` bits.
--   * `Turing.MultiTapeTM.encIntBin_natCast`, `Turing.MultiTapeTM.encIntBin_negSucc`: the codes of
--     nonnegative and negative integers.
--
--   **Contents.** The module is published as a whole: 6 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_IntBinary`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Encodings/IntBinary.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Nat
public import Mathlib.Data.Nat.Size

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Encodings.IntBinary` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Binary sign-magnitude integers

`encIntBin` encodes an integer by a sign bit, `true` for negative integers, followed by the binary
digits of its magnitude (`Turing.MultiTapeTM.encNat`), least significant first. The magnitude is
not framed: the sign is a single leading bit, the digits are the rest of the word, and the
magnitude is the tail of the code, so the binary natural arithmetic applies to it directly. A
negative integer has a nonzero magnitude, so zero has the single code `[false]`. An integer `z`
occupies `Nat.size z.natAbs + 1` bits. The unary integers `Turing.MultiTapeTM.encInt` index tape
positions; this encoding carries values whose magnitude is exponential in their length.

## Main definitions

* `Turing.MultiTapeTM.encIntBin`: integers as a sign bit followed by a binary magnitude.

## Main results

* `Turing.MultiTapeTM.length_encIntBin`: the code of `z` has `Nat.size z.natAbs + 1` bits.
* `Turing.MultiTapeTM.encIntBin_natCast`, `Turing.MultiTapeTM.encIntBin_negSucc`: the codes of
  nonnegative and negative integers.
-/

@[expose] public section

namespace Turing.MultiTapeTM

/-- Integers in binary sign-magnitude form: the bit `z < 0` followed by the binary digits of the
magnitude `z.natAbs`, least significant first. Zero is encoded as `[false]` only. -/
def encIntBin : ℤ ↪ List Bool :=
  ⟨fun z => decide (z < 0) :: encNat z.natAbs, fun z w h => by
    simp only [List.cons.injEq, decide_eq_decide] at h
    have := encNat.injective h.2
    lia⟩

@[simp]
theorem encIntBin_apply (z : ℤ) : encIntBin z = decide (z < 0) :: z.natAbs.bits := rfl

/-- The code of an integer has one sign bit and the binary length of its magnitude. -/
theorem length_encIntBin (z : ℤ) : (encIntBin z).length = z.natAbs.size + 1 := by
  simp [Nat.size_eq_bits_len]

theorem encIntBin_natCast (n : ℕ) : encIntBin n = false :: n.bits := by
  simp

theorem encIntBin_zero : encIntBin 0 = [false] := rfl

theorem encIntBin_negSucc (n : ℕ) : encIntBin (Int.negSucc n) = true :: (n + 1).bits := by
  simp only [encIntBin_apply, Int.negSucc_lt_zero, decide_true, Int.natAbs_negSucc]

end Turing.MultiTapeTM


