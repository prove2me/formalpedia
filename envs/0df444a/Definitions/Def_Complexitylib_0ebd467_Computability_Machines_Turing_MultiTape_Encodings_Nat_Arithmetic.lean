-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Nat_Arithmetic
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Nat_Arithmetic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:44:06.69706+00:00
-- url     : https://prove2.me/theorems/dac1c7c0-f7de-4a1f-8d0c-db479978b94e
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat.Arithmetic — Binary word arithmetic and comparison
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat.Arithmetic` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   The word adder and its value law, and the highest-differing-bit characterization of strict
--   order are pure facts about least-significant-first binary words. They do not import a
--   computability calculus. The multiplication bit fold and its prefix-size laws are shared with
--   the direct and legacy resource proofs, retaining the original shift-and-add data.
--
--   **Contents.** The module is published as a whole: 10 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Nat_Arithmetic`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Encodings/Nat/Arithmetic.lean

/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger, Karn Seth
-/
module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Nat_Bits
public import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat.Arithmetic` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Binary word arithmetic and comparison

The word adder and its value law, and the highest-differing-bit characterization of strict
order are pure facts about least-significant-first binary words. They do not import a
computability calculus. The multiplication bit fold and its prefix-size laws are shared with
the direct and legacy resource proofs, retaining the original shift-and-add data.
-/

@[expose] public section
namespace Turing.MultiTapeTM
open NatSucc

namespace NatAdd

/-- The binary digits of `2 * n + b`, if they do not end in a zero. -/
lemma bits_bit (b : Bool) (n : ℕ) (h : n = 0 → b = true) :
    (2 * n + b.toNat).bits = b :: n.bits := by
  rw [← Nat.bit_val]
  exact Nat.bits_append_bit n b h

/-- The carry of adding three digits. -/
def carry (a b c : Bool) : Bool := a && b || c && (a ^^ b)

/-- Adds the digits `l` and `r` with the carry `c`, least significant first; `r` is padded with
zeros. -/
def addBits : Bool → List Bool → List Bool → List Bool
  | c, [], r => incr c r
  | c, a :: l, r => (a ^^ (r.headD false ^^ c)) :: addBits (carry a (r.headD false) c) l r.tail

/-- Incrementing a canonical word represents addition of its incoming carry. -/
lemma incr_bits (c : Bool) (n : ℕ) : incr c n.bits = (n + c.toNat).bits := by
  cases c
  · simp [incr]
  · exact (bits_succ n).symm

/-- The word adder computes the sum of two natural numbers and an incoming carry. -/
lemma addBits_bits (c : Bool) (m n : ℕ) : addBits c m.bits n.bits = (m + n + c.toNat).bits := by
  induction m using Nat.binaryRec' generalizing c n with
  | zero => simp [addBits, incr_bits]
  | bit a m hm ih =>
    rw [Nat.bits_append_bit _ _ hm, addBits]
    induction n using Nat.binaryRec' with
    | zero =>
      have h := ih (carry a false c) 0
      rw [Nat.zero_bits] at h
      rw [Nat.zero_bits, List.headD_nil, List.tail_nil, h, Nat.bit_val,
        show 2 * m + a.toNat + 0 + c.toNat = 2 * (m + 0 + (carry a false c).toNat) +
          (a ^^ (false ^^ c)).toNat by cases a <;> cases c <;> simp [carry]; omega,
        bits_bit]
      cases a <;> cases c <;> simp_all [carry]
    | bit b n hn _ =>
      rw [Nat.bits_append_bit _ _ hn, List.headD_cons, List.tail_cons, ih, Nat.bit_val,
        Nat.bit_val, show 2 * m + a.toNat + (2 * n + b.toNat) + c.toNat =
          2 * (m + n + (carry a b c).toNat) + (a ^^ (b ^^ c)).toNat by
          cases a <;> cases b <;> cases c <;> simp [carry] <;> omega, bits_bit]
      cases a <;> cases b <;> cases c <;> simp_all [carry]

end NatAdd

/-! ### Binary multiplication fold

The existing NatMul word-fold data and laws are moved from Complexity/Arith with Christian
Reitwiessner's source and proof bodies unchanged. Only these four previously module-private
names are exposed for shared direct and legacy resource proofs.
-/

namespace NatMul

/-- One round: add the shifted factor `s.2` to the product `s.1` if the digit `a` is `1`, and shift
the factor. -/
def mulStep (s : ℕ × ℕ) (a : Bool) : ℕ × ℕ := (if a then s.1 + s.2 else s.1, s.2 + s.2)

/-- The bit fold multiplies the shifted factor and adds the initial accumulator. -/
lemma foldl_mulStep (m acc sh : ℕ) : (m.bits.foldl mulStep (acc, sh)).1 = acc + m * sh := by
  induction m using Nat.binaryRec' generalizing acc sh with
  | zero => simp
  | bit a m hm ih =>
    rw [Nat.bits_append_bit _ _ hm, List.foldl_cons, mulStep, ih, Nat.bit_val]
    cases a <;> simp <;> ring

/-- Prefix accumulators and shifts are bounded by the number of processed binary digits. -/
lemma foldl_mulStep_le (l : List Bool) (acc sh : ℕ) :
    (l.foldl mulStep (acc, sh)).1 + sh ≤ acc + 2 ^ l.length * sh ∧
      (l.foldl mulStep (acc, sh)).2 = 2 ^ l.length * sh := by
  induction l generalizing acc sh with
  | nil => simp
  | cons a l ih =>
    obtain ⟨h₁, h₂⟩ := ih (if a then acc + sh else acc) (sh + sh)
    have h : (if a then acc + sh else acc) ≤ acc + sh := by split <;> omega
    simp only [List.foldl_cons, mulStep, List.length_cons, pow_succ] at h₁ h₂ ⊢
    refine ⟨?_, by rw [h₂]; ring⟩
    nlinarith

/-- A shifted numerical bound gives an additive bound on binary size. -/
lemma size_le_of_le {x n : ℕ} (i : ℕ) (h : x ≤ 2 ^ i * n) : x.size ≤ i + n.size :=
  Nat.size_le.2 (h.trans_lt (by
    rw [pow_add]; exact Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self n) (Nat.two_pow_pos i)))

end NatMul

end Turing.MultiTapeTM

namespace Nat

/-- `m < n` exactly when some bit position below the length of `n` holds a zero in `m` and a one
in `n`, and every higher position below the total length agrees. -/
theorem lt_iff_exists_testBit (m n : ℕ) :
    m < n ↔ ∃ i < n.size, m.testBit i = false ∧ n.testBit i = true ∧
      ∀ j < m.size + n.size, i < j → m.testBit j = n.testBit j := by
  have hbig {k j : ℕ} (hj : k.size ≤ j) : k.testBit j = false :=
    Nat.testBit_eq_false_of_lt ((Nat.lt_size_self k).trans_le (Nat.pow_le_pow_right (by lia) hj))
  constructor
  · intro hlt
    obtain ⟨i, hi, hhigh⟩ := Nat.exists_most_significant_bit
      (show m ^^^ n ≠ 0 from fun h => hlt.ne (Nat.eq_of_testBit_eq fun j => by
        have := Nat.testBit_xor m n j
        rw [h, Nat.zero_testBit] at this
        revert this
        cases m.testBit j <;> cases n.testBit j <;> simp))
    rw [Nat.testBit_xor] at hi
    have heq : ∀ j, i < j → m.testBit j = n.testBit j := fun j hj => by
      have := hhigh j hj
      rw [Nat.testBit_xor] at this
      revert this
      cases m.testBit j <;> cases n.testBit j <;> simp
    cases hmi : m.testBit i <;> cases hni : n.testBit i <;> rw [hmi, hni] at hi
    · simp at hi
    · refine ⟨i, ?_, hmi, hni, fun j _ hj => heq j hj⟩
      by_contra h
      rw [hbig (Nat.le_of_not_lt h)] at hni
      exact Bool.false_ne_true hni
    · exact absurd (Nat.lt_of_testBit i hni hmi fun j hj => (heq j hj).symm) (Nat.lt_asymm hlt)
    · simp at hi
  · rintro ⟨i, -, hm, hn, h⟩
    refine Nat.lt_of_testBit i hm hn fun j hj => ?_
    by_cases hj' : j < m.size + n.size
    · exact h j hj' hj
    · rw [hbig (by lia), hbig (by lia)]

end Nat


