-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_BinaryLog
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_BinaryLog
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:57:31.398912+00:00
-- url     : https://prove2.me/theorems/a1d5d4c8-0a09-4338-9137-f527302a6eaf
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog — Polynomial-time binary ceiling logarithms
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   The base-two ceiling logarithm of a binary natural is computed from its bit length and a
--   comparison with the preceding power of two. The primary certificate returns its result in unary,
--   with length at most the binary input length, and binary-output frontends convert that unary
--   counter to `Turing.MultiTapeTM.encNat`. Zero and one both return zero. The ordinary polynomial-time
--   certificates use the existing binary size, power, comparison and unary-to-binary providers; they
--   never expand the input natural into a unary word.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.ComputableInPolyTime.binary_clog_two`: ceiling logarithm from binary
--     input to unary output.
--   * `Turing.MultiTapeTM.ComputableInPolyTime.binary_clog_two_nat`, `.binary_clog_two_nat'`:
--     ceiling logarithm from binary input to binary output (`encNat` to `encNat`), and its
--     compositional rule.
--
--   ### References
--
--   * [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
--
--   **Contents.** The module is published as a whole: 4 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_BinaryLog`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Complexity/PolyTime/Nat/BinaryLog.lean

/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger, Anton Kovsharov
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_Binary
public import Mathlib.Data.Nat.Log
import Definitions.Def_Complexitylib_0ebd467_Tactic_PolyTime_Init

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Polynomial-time binary ceiling logarithms

The base-two ceiling logarithm of a binary natural is computed from its bit length and a
comparison with the preceding power of two. The primary certificate returns its result in unary,
with length at most the binary input length, and binary-output frontends convert that unary
counter to `Turing.MultiTapeTM.encNat`. Zero and one both return zero. The ordinary polynomial-time
certificates use the existing binary size, power, comparison and unary-to-binary providers; they
never expand the input natural into a unary word.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.binary_clog_two`: ceiling logarithm from binary
  input to unary output.
* `Turing.MultiTapeTM.ComputableInPolyTime.binary_clog_two_nat`, `.binary_clog_two_nat'`:
  ceiling logarithm from binary input to binary output (`encNat` to `encNat`), and its
  compositional rule.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

private theorem clog_two_eq (n : ℕ) : Nat.clog 2 n =
    if n ≤ 2 ^ (n.size - 1) then n.size - 1 else n.size := by
  have hlo : n.size - 1 ≤ Nat.clog 2 n := by
    have hs : n.size ≤ Nat.clog 2 n + 1 := Nat.size_le.mpr
      ((Nat.le_pow_clog (by decide : 1 < 2) n).trans_lt (by
        rw [pow_succ]
        have := Nat.two_pow_pos (Nat.clog 2 n)
        omega))
    omega
  have hhi : Nat.clog 2 n ≤ n.size := Nat.clog_le_of_le_pow (Nat.lt_size_self n).le
  split
  · rename_i h
    exact Nat.le_antisymm (Nat.clog_le_of_le_pow h) hlo
  · rename_i h
    have := (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mpr (Nat.lt_of_not_ge h)
    omega

/-- Compute the base-two ceiling logarithm of a binary natural, returning a unary counter.
The full input, intermediate power of two and output have polynomial bit cost. -/
@[fun_prop]
theorem binary_clog_two : ComputableInPolyTime (Nat.clog 2) encNat encUnary := by
  have hp : ComputableInPolyTime (fun n : ℕ => n.size - 1) encNat encUnary :=
    unary_sub.comp (binary_size.prod (const 1))
  have htest := binary_le' (id' (encIn := encNat)) (binary_two_pow.comp hp)
  convert htest.ite_decide hp binary_size using 1
  exact funext clog_two_eq

/-- Compute the base-two ceiling logarithm of a binary natural, returning a binary natural
(`encNat` to `encNat`). -/
@[fun_prop]
theorem binary_clog_two_nat : ComputableInPolyTime (Nat.clog 2) encNat encNat :=
  unary_to_binary.comp binary_clog_two

/-- Compute the base-two ceiling logarithm of a computed binary natural, returning a binary
natural. -/
@[fun_prop]
theorem binary_clog_two_nat' {α : Type} {input : α ↪ List Bool} {f : α → ℕ}
    (hf : ComputableInPolyTime f input encNat) :
    ComputableInPolyTime (fun a => Nat.clog 2 (f a)) input encNat :=
  binary_clog_two_nat.comp hf

end Turing.MultiTapeTM.ComputableInPolyTime


