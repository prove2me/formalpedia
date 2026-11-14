-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Nat_Bits
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Nat_Bits
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:43:24.858208+00:00
-- url     : https://prove2.me/theorems/e6dba514-aa8b-4030-a797-e315bc22f9b6
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits — Binary natural encoding and carry increment
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   This module defines the little-endian binary encoding `Turing.MultiTapeTM.encNat` of natural
--   numbers (`Nat.bits`) and the carry-propagation step `Turing.MultiTapeTM.NatSucc.incr` for
--   binary successor, independent of machine resource certificates.
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.encNat`: natural numbers encoded by their binary digits, least significant
--     first.
--   * `Turing.MultiTapeTM.NatSucc.incr`: adds an incoming carry bit to a little-endian binary word.
--
--   ### Main statements
--
--   * `Turing.MultiTapeTM.encNat_apply`: unfolding `encNat n` to `n.bits`.
--   * `Turing.MultiTapeTM.NatSucc.bits_succ`: `(n + 1).bits = incr true n.bits`.
--
--   **Contents.** The module is published as a whole: 4 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Nat_Bits`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Encodings/Nat/Bits.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: subset of crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Mathlib.Data.Nat.Bits
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Pair
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_List
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Ring

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Binary natural encoding and carry increment

This module defines the little-endian binary encoding `Turing.MultiTapeTM.encNat` of natural
numbers (`Nat.bits`) and the carry-propagation step `Turing.MultiTapeTM.NatSucc.incr` for
binary successor, independent of machine resource certificates.

## Main definitions

* `Turing.MultiTapeTM.encNat`: natural numbers encoded by their binary digits, least significant
  first.
* `Turing.MultiTapeTM.NatSucc.incr`: adds an incoming carry bit to a little-endian binary word.

## Main statements

* `Turing.MultiTapeTM.encNat_apply`: unfolding `encNat n` to `n.bits`.
* `Turing.MultiTapeTM.NatSucc.bits_succ`: `(n + 1).bits = incr true n.bits`.
-/

public section

namespace Turing.MultiTapeTM

/-- Natural numbers encoded by their binary digits, least significant first. -/
@[expose] public def encNat : ℕ ↪ List Bool :=
  ⟨Nat.bits, fun m n h => Nat.eq_of_testBit_eq fun i => by simp [Nat.testBit_eq_inth, h]⟩

/-- `encNat n` is the little-endian binary digit list `n.bits`. -/
@[simp]
public lemma encNat_apply (n : ℕ) : encNat n = n.bits := rfl

namespace NatSucc

/-- Adds the carry `c` to the binary digits `l`, least significant first. -/
@[expose] public def incr : Bool → List Bool → List Bool
  | false, l => l
  | true, [] => [true]
  | true, false :: l => true :: l
  | true, true :: l => false :: incr true l

/-- The binary digits of `n + 1` are obtained by incrementing `n.bits` with carry `true`. -/
public lemma bits_succ (n : ℕ) : (n + 1).bits = incr true n.bits := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · rcases Nat.eq_zero_or_pos m with rfl | hm
      · rfl
      · rw [Nat.bit1_bits, Nat.bit0_bits m (by omega), incr]
    · rw [Nat.bit1_bits, show 2 * m + 1 + 1 = 2 * (m + 1) by ring, Nat.bit0_bits _ (by omega),
        ih m (by omega), incr]

end NatSucc

end Turing.MultiTapeTM


