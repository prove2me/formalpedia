-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Nat_Division
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Nat_Division
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:44:35.709817+00:00
-- url     : https://prove2.me/theorems/3a77f5f5-db37-417e-aaf5-39e79a8aa8c5
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat.Division — The existing binary long-division word algorithm
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat.Division` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   The public step, quotient/remainder laws and prefix encoding bound are moved unchanged from
--   the higher division facade, independently of any higher computability calculus.
--
--   **Contents.** The module is published as a whole: 5 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Nat_Division`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Encodings/Nat/Division.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate

public import Batteries.Tactic.Lint.Basic
public import Mathlib.Init
public import Mathlib.Tactic.Common
public import Definitions.Def_Cslib_254e30e_Tactic_GrindAttrs
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Pair
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Nat_Bits
public import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_BitString_List_Binary
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat.Division` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The existing binary long-division word algorithm

The public step, quotient/remainder laws and prefix encoding bound are moved unchanged from
the higher division facade, independently of any higher computability calculus.
-/

@[expose] public section
namespace Turing.MultiTapeTM.BinaryDiv

/-- One shift-and-subtract step of binary long division with divisor `b`, state `(q, r)`, and next
most-significant dividend bit `bit`. When `b = 0`, the quotient remains `0` and the remainder
accumulates the binary value of the dividend. -/
def divModStep (b : ℕ) (state : ℕ × ℕ) (bit : Bool) : ℕ × ℕ :=
  let r' := 2 * state.2 + if bit then 1 else 0
  if b = 0 then (0, r')
  else if b ≤ r' then (2 * state.1 + 1, r' - b)
  else (2 * state.1, r')

lemma divModStep_div_mod (v b : ℕ) (bit : Bool) :
    divModStep b (v / b, v % b) bit = ((2 * v + bit.toNat) / b, (2 * v + bit.toNat) % b) := by
  have hbit : (if bit then 1 else 0) = bit.toNat := by cases bit <;> rfl
  have hdiv := Nat.div_add_mod v b
  have hbit_le : bit.toNat ≤ 1 := Bool.toNat_le bit
  have hmul₀ : 2 * (v / b) * b = 2 * (b * (v / b)) := by ring
  have hmul₁ : (2 * (v / b) + 1) * b = 2 * (b * (v / b)) + b := by ring
  have hmul₂ : (2 * (v / b) + 1 + 1) * b = 2 * (b * (v / b)) + 2 * b := by ring
  have hmul₃ : b * (2 * (v / b)) = 2 * (b * (v / b)) := by ring
  have hmul₄ : b * (2 * (v / b) + 1) = 2 * (b * (v / b)) + b := by ring
  dsimp only [divModStep]
  rw [hbit]
  split_ifs with hb hle
  · subst hb
    simp
  · have hb_pos : 0 < b := Nat.pos_of_ne_zero hb
    have hmod_lt : v % b < b := Nat.mod_lt v hb_pos
    have hq : (2 * v + bit.toNat) / b = 2 * (v / b) + 1 := by
      apply Nat.div_eq_of_lt_le <;> lia
    have hr : (2 * v + bit.toNat) % b = 2 * (v % b) + bit.toNat - b := by
      have := Nat.div_add_mod (2 * v + bit.toNat) b
      rw [hq] at this
      lia
    exact Prod.ext hq.symm hr.symm
  · have hb_pos : 0 < b := Nat.pos_of_ne_zero hb
    have hq : (2 * v + bit.toNat) / b = 2 * (v / b) := by
      apply Nat.div_eq_of_lt_le <;> lia
    have hr : (2 * v + bit.toNat) % b = 2 * (v % b) + bit.toNat := by
      have := Nat.div_add_mod (2 * v + bit.toNat) b
      rw [hq] at this
      lia
    exact Prod.ext hq.symm hr.symm

/-- Folding `divModStep` over any most-significant-first bit word computes the quotient and
remainder of `Cslib.BitString.binaryValue word` by `b`. -/
theorem foldl_divModStep (b : ℕ) (word : List Bool) :
    word.foldl (divModStep b) (0, 0) =
      (Cslib.BitString.binaryValue word / b, Cslib.BitString.binaryValue word % b) := by
  induction word using List.reverseRecOn with
  | nil => simp [Cslib.BitString.binaryValue]
  | append_singleton word bit ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ih,
      Cslib.BitString.binaryValue_snoc, divModStep_div_mod]

/-- Folding `divModStep` over the reversed binary digits of `p.1` computes
`(p.1 / p.2, p.1 % p.2)`. -/
theorem divMod_eq (p : ℕ × ℕ) :
    p.1.bits.reverse.foldl (divModStep p.2) (0, 0) = (p.1 / p.2, p.1 % p.2) := by
  rw [foldl_divModStep, Cslib.BitString.binaryValue_reverse_bits]

/-- The encoded state after folding `word` has length at most `3 * word.length + 1`. -/
theorem length_encPair_foldl_divModStep_le (b : ℕ) (word : List Bool) :
    (encPair encNat encNat (word.foldl (divModStep b) (0, 0))).length ≤ 3 * word.length + 1 := by
  rw [foldl_divModStep]
  have hlt := Cslib.BitString.binaryValue_lt_two_pow word
  have hq : (Cslib.BitString.binaryValue word / b).size ≤ word.length :=
    Nat.size_le.2 ((Nat.div_le_self _ _).trans_lt hlt)
  have hr : (Cslib.BitString.binaryValue word % b).size ≤ word.length :=
    Nat.size_le.2 ((Nat.mod_le _ _).trans_lt hlt)
  simp only [length_encPair, encNat_apply, Nat.size_eq_bits_len]
  lia

end Turing.MultiTapeTM.BinaryDiv


