-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_BinaryDiv
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_BinaryDiv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:57:43.579201+00:00
-- url     : https://prove2.me/theorems/a00c9681-ee89-4e18-b698-1a18566f33e8
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv — Polynomial-time division and remainder on binary naturals
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   Schoolbook shift-and-subtract long division over the binary encoding `Turing.MultiTapeTM.encNat`.
--   The dividend's binary digits are reversed to most-significant-bit-first order and folded with
--   `Turing.MultiTapeTM.BinaryDiv.divModStep`, which shifts the running remainder by one bit, adds the
--   next dividend bit, and subtracts the divisor whenever it fits. A zero divisor never subtracts, so
--   the quotient stays `0` and the remainder reconstructs the dividend, matching `a / 0 = 0` and
--   `a % 0 = a`.
--
--   After consuming any prefix `word` of the reversed digits, the state `(q, r)` is the quotient and
--   remainder of `Cslib.BitString.binaryValue word` by the divisor (`BinaryDiv.foldl_divModStep`). Both
--   components are therefore at most `binaryValue word < 2 ^ word.length`, so their binary encodings
--   have length at most `word.length`, keeping the encoded pair linearly bounded throughout the fold.
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.BinaryDiv.divModStep`: one shift-and-subtract step of binary long division.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.BinaryDiv.foldl_divModStep`: folding `divModStep` over a
--     most-significant-first bit word computes the quotient and remainder of its `binaryValue`.
--   * `Turing.MultiTapeTM.BinaryDiv.divMod_eq`: folding over `a.bits.reverse` computes
--     `(a / b, a % b)`.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_divMod`: joint quotient and remainder on
--     `encNat`.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_div`, `.binary_mod`: binary division and
--     remainder on `encNat`.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_div'`, `.binary_mod'`: composition rules
--     for `fun_prop` and `polytime`.
--
--   ### References
--
--   * [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
--
--   **Contents.** The module is published as a whole: 5 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_BinaryDiv`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Complexity/PolyTime/Nat/BinaryDiv.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_Binary
public import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_BitString_List_Binary
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Nat_Division
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimeBinaryDivision
public import Definitions.Def_Complexitylib_0ebd467_Tactic_PolyTime_Init

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Polynomial-time division and remainder on binary naturals

Schoolbook shift-and-subtract long division over the binary encoding `Turing.MultiTapeTM.encNat`.
The dividend's binary digits are reversed to most-significant-bit-first order and folded with
`Turing.MultiTapeTM.BinaryDiv.divModStep`, which shifts the running remainder by one bit, adds the
next dividend bit, and subtracts the divisor whenever it fits. A zero divisor never subtracts, so
the quotient stays `0` and the remainder reconstructs the dividend, matching `a / 0 = 0` and
`a % 0 = a`.

After consuming any prefix `word` of the reversed digits, the state `(q, r)` is the quotient and
remainder of `Cslib.BitString.binaryValue word` by the divisor (`BinaryDiv.foldl_divModStep`). Both
components are therefore at most `binaryValue word < 2 ^ word.length`, so their binary encodings
have length at most `word.length`, keeping the encoded pair linearly bounded throughout the fold.

## Main definitions

* `Turing.MultiTapeTM.BinaryDiv.divModStep`: one shift-and-subtract step of binary long division.

## Main results

* `Turing.MultiTapeTM.BinaryDiv.foldl_divModStep`: folding `divModStep` over a
  most-significant-first bit word computes the quotient and remainder of its `binaryValue`.
* `Turing.MultiTapeTM.BinaryDiv.divMod_eq`: folding over `a.bits.reverse` computes
  `(a / b, a % b)`.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_divMod`: joint quotient and remainder on
  `encNat`.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_div`, `.binary_mod`: binary division and
  remainder on `encNat`.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_div'`, `.binary_mod'`: composition rules
  for `fun_prop` and `polytime`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-- Compute both quotient and remainder of binary naturals by shift-and-subtract long division. -/
theorem binary_divMod : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => (p.1 / p.2, p.1 % p.2))
    (encPair encNat encNat) (encPair encNat encNat) := by
  have hlist : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => p.1.bits.reverse)
      (encPair encNat encNat) encBits := by
    fun_prop
  have hstep : ComputableTidilyInPolyTime
      (fun q : (ℕ × (ℕ × ℕ)) × Bool => BinaryDiv.divModStep q.1.1 q.1.2 q.2)
      (encPair (encPair encNat (encPair encNat encNat)) encBool)
      (encPair encNat encNat) := by
    unfold BinaryDiv.divModStep
    fun_prop
  have hfold := foldlWith (encP := encNat) (encA := encBool) (encL := encBits)
    (encB := encPair encNat encNat) (par := Prod.snd) (list := fun p : ℕ × ℕ => p.1.bits.reverse)
    (init := fun _ => (0, 0)) (step := BinaryDiv.divModStep)
    (snd encNat encNat) hlist (const (0, 0)) hstep
    (B := fun p => 3 * (encPair encNat encNat p).length + 1)
    (((PolyBounded.const 3).mul .self).add (.const 1))
    (fun p i _ => by
      have hlen := BinaryDiv.length_encPair_foldl_divModStep_le p.2 (p.1.bits.reverse.take i)
      have htake : (p.1.bits.reverse.take i).length ≤ (encPair encNat encNat p).length := by
        calc (p.1.bits.reverse.take i).length
            ≤ p.1.bits.reverse.length := List.length_take_le' _ _
          _ = (encNat p.1).length := by simp
          _ ≤ (encPair encNat encNat p).length := length_le_encPair_left encNat encNat p
      lia)
  simpa only [BinaryDiv.divMod_eq] using hfold

/-- Division of binary naturals. -/
@[fun_prop]
theorem binary_div : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => p.1 / p.2)
    (encPair encNat encNat) encNat :=
  binary_divMod.fst'

/-- Remainder of binary naturals. -/
@[fun_prop]
theorem binary_mod : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => p.1 % p.2)
    (encPair encNat encNat) encNat :=
  binary_divMod.snd'

/-- Divide computed binary values, fixing their intermediate encodings for proof search. -/
@[fun_prop]
theorem binary_div' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableTidilyInPolyTime left input encNat)
    (hright : ComputableTidilyInPolyTime right input encNat) :
    ComputableTidilyInPolyTime (fun a => left a / right a) input encNat :=
  binary_div.comp (hleft.prod hright)

/-- Remainder of computed binary values, fixing their intermediate encodings for proof search. -/
@[fun_prop]
theorem binary_mod' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableTidilyInPolyTime left input encNat)
    (hright : ComputableTidilyInPolyTime right input encNat) :
    ComputableTidilyInPolyTime (fun a => left a % right a) input encNat :=
  binary_mod.comp (hleft.prod hright)

end Turing.MultiTapeTM.ComputableTidilyInPolyTime


