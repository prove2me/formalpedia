-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_Binary
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_Binary
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:56:14.8007+00:00
-- url     : https://prove2.me/theorems/247e485f-9d50-4150-9812-12172a5a0e68
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary — Polynomial-time arithmetic on binary naturals
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   Polynomial-time certificates for arithmetic on the binary encoding `Turing.MultiTapeTM.encNat`
--   (digits least significant first), the binary counterparts of the unary certificates in
--   `Complexity/Computability/Machines/Turing/MultiTape/Complexity/PolyTime/Nat.lean`. Addition and
--   multiplication reuse Christian Reitwiessner's plain schoolbook certificates
--   `Turing.MultiTapeTM.ComputableInO.natAdd` and `Turing.MultiTapeTM.ComputableInO.natMul`. A list is
--   summed by a left fold whose accumulator grows by at most one digit more than the length of the
--   element added. Powers of two are computed from a unary exponent by repeated doubling. Comparisons
--   are the linear-time zip transducers of `Turing.MultiTapeTM.computableInTimeAndSpace_natLt` and
--   `Turing.MultiTapeTM.computableInTimeAndSpace_natLe`; bitwise OR is that of
--   `Turing.MultiTapeTM.computableInTimeAndSpace_natOr`. The verifiers and reductions
--   of the number problems (`Cslib.Complexity.SubsetSum` and its relatives) are built from these.
--
--   Truncated subtraction is schoolbook subtraction: a left fold over the digit pairs of both operands
--   keeps a borrow and appends one difference digit per position. A final borrow means that the
--   difference is negative; otherwise the digits are read back as a natural
--   (`Turing.MultiTapeTM.ofBits`, certified by `Turing.MultiTapeTM.Decoder.nat`), dropping trailing
--   zeros. General powers to a unary exponent are computed by repeated
--   multiplication.
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.BinarySub.subStep`: one round of schoolbook subtraction with a borrow.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsToNat`: binary decoding of arbitrary words.
--   * `Nat.size_add_le`: a sum has at most one binary digit more than its summands together.
--   * `Nat.size_add_le_max`, `Nat.size_mul_le`, `Nat.size_pow_le`, `Nat.size_sum_le`: binary lengths
--     of sums, products, powers and list sums.
--   * `Turing.MultiTapeTM.BinarySub.sub_eq`: truncated subtraction through the final borrow.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_add`, `.binary_mul`: addition and
--     multiplication.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_sum`: the sum of a list.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_two_pow`: `2 ^ k` in binary, from `k` in
--     unary.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_lt`, `.binary_le`: comparisons.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_sub`: truncated subtraction.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_pow`: a power to a unary exponent.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_add'`, `.binary_lt'`, `.binary_le'`:
--     composition rules for `fun_prop`.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_mul'`, `.binary_sub'`, `.binary_pow'`:
--     composition rules for `fun_prop`.
--   * `Turing.MultiTapeTM.ComputableInPolyTime.binary_bitwise`, `.binary_and`, `.binary_or`,
--     `.binary_xor`, `.binary_and'`, `.binary_or'`, `.binary_xor'`: bitwise operations on binary
--     naturals, and their composition rules.
--   * `Turing.MultiTapeTM.ComputableInPolyTime.binary_size`, `.binary_min_unary`,
--     `.binary_min_unary'`, `.binary_shiftRight`, `.binary_shiftRight'`: bit-length in unary, capping
--     a binary natural by a unary bound, and binary right shift.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_testBit`: a bit of a binary number at a
--     unary position.
--
--   **Contents.** The module is published as a whole: 46 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_Binary`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Complexity/PolyTime/Nat/Binary.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimeNatFrontends
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimeBinaryPrimitives
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimeBinaryDivision
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_List
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Plain
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_Degree
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Decoder
public import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_Nat_Bits
public import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_Nat_BinarySize
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Nat_Subtraction
import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_BitString_List_Binary
import Definitions.Def_Complexitylib_0ebd467_Tactic_PolyTime_Init
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_BinaryAddition
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Bitwise

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Polynomial-time arithmetic on binary naturals

Polynomial-time certificates for arithmetic on the binary encoding `Turing.MultiTapeTM.encNat`
(digits least significant first), the binary counterparts of the unary certificates in
`Complexity/Computability/Machines/Turing/MultiTape/Complexity/PolyTime/Nat.lean`. Addition and
multiplication reuse Christian Reitwiessner's plain schoolbook certificates
`Turing.MultiTapeTM.ComputableInO.natAdd` and `Turing.MultiTapeTM.ComputableInO.natMul`. A list is
summed by a left fold whose accumulator grows by at most one digit more than the length of the
element added. Powers of two are computed from a unary exponent by repeated doubling. Comparisons
are the linear-time zip transducers of `Turing.MultiTapeTM.computableInTimeAndSpace_natLt` and
`Turing.MultiTapeTM.computableInTimeAndSpace_natLe`; bitwise OR is that of
`Turing.MultiTapeTM.computableInTimeAndSpace_natOr`. The verifiers and reductions
of the number problems (`Cslib.Complexity.SubsetSum` and its relatives) are built from these.

Truncated subtraction is schoolbook subtraction: a left fold over the digit pairs of both operands
keeps a borrow and appends one difference digit per position. A final borrow means that the
difference is negative; otherwise the digits are read back as a natural
(`Turing.MultiTapeTM.ofBits`, certified by `Turing.MultiTapeTM.Decoder.nat`), dropping trailing
zeros. General powers to a unary exponent are computed by repeated
multiplication.

## Main definitions

* `Turing.MultiTapeTM.BinarySub.subStep`: one round of schoolbook subtraction with a borrow.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsToNat`: binary decoding of arbitrary words.
* `Nat.size_add_le`: a sum has at most one binary digit more than its summands together.
* `Nat.size_add_le_max`, `Nat.size_mul_le`, `Nat.size_pow_le`, `Nat.size_sum_le`: binary lengths
  of sums, products, powers and list sums.
* `Turing.MultiTapeTM.BinarySub.sub_eq`: truncated subtraction through the final borrow.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_add`, `.binary_mul`: addition and
  multiplication.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_sum`: the sum of a list.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_two_pow`: `2 ^ k` in binary, from `k` in
  unary.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_lt`, `.binary_le`: comparisons.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_sub`: truncated subtraction.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_pow`: a power to a unary exponent.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_add'`, `.binary_lt'`, `.binary_le'`:
  composition rules for `fun_prop`.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_mul'`, `.binary_sub'`, `.binary_pow'`:
  composition rules for `fun_prop`.
* `Turing.MultiTapeTM.ComputableInPolyTime.binary_bitwise`, `.binary_and`, `.binary_or`,
  `.binary_xor`, `.binary_and'`, `.binary_or'`, `.binary_xor'`: bitwise operations on binary
  naturals, and their composition rules.
* `Turing.MultiTapeTM.ComputableInPolyTime.binary_size`, `.binary_min_unary`,
  `.binary_min_unary'`, `.binary_shiftRight`, `.binary_shiftRight'`: bit-length in unary, capping
  a binary natural by a unary bound, and binary right shift.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_testBit`: a bit of a binary number at a
  unary position.
-/

@[expose] public section

namespace Nat

/-- The binary length of a sum is at most the binary lengths of the summands together, plus one. -/
theorem size_add_le (m n : ℕ) : (m + n).size ≤ m.size + n.size + 1 := by
  refine Nat.size_le.2 ?_
  have hm := Nat.lt_size_self m
  have hn := Nat.lt_size_self n
  have h₁ : 2 ^ m.size ≤ 2 ^ (m.size + n.size) := Nat.pow_le_pow_right (by lia) (by lia)
  have h₂ : 2 ^ n.size ≤ 2 ^ (m.size + n.size) := Nat.pow_le_pow_right (by lia) (by lia)
  rw [Nat.pow_succ]
  lia

/-- The binary length of a sum is at most one more than the longer binary length of the
summands. -/
theorem size_add_le_max (m n : ℕ) : (m + n).size ≤ max m.size n.size + 1 := by
  refine Nat.size_le.2 ?_
  have hm := (Nat.lt_size_self m).trans_le
    (Nat.pow_le_pow_right (by lia) (le_max_left m.size n.size))
  have hn := (Nat.lt_size_self n).trans_le
    (Nat.pow_le_pow_right (by lia) (le_max_right m.size n.size))
  rw [Nat.pow_succ]
  lia

/-- A sum of naturals of binary length at most `b` has binary length at most `b` plus the binary
length of the number of summands. -/
theorem size_sum_le {l : List ℕ} {b : ℕ} (h : ∀ n ∈ l, n.size ≤ b) :
    l.sum.size ≤ b + l.length.size := by
  refine Nat.size_le.2 ?_
  have hsum : l.sum ≤ l.length * 2 ^ b := by
    simpa only [smul_eq_mul] using
      List.sum_le_card_nsmul l (2 ^ b) fun n hn => (Nat.size_le.1 (h n hn)).le
  rw [Nat.pow_add, Nat.mul_comm (2 ^ b)]
  exact hsum.trans_lt (Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self _) (by positivity))

/-- A binary length is at most the number itself. -/
theorem size_le_self (n : ℕ) : n.size ≤ n :=
  Nat.size_le.2 Nat.lt_two_pow_self

end Nat

namespace Turing.MultiTapeTM.BinarySub
private lemma foldl_append_singleton {α β : Type} (f : α → β) (l : List α) (out : List β) :
    l.foldl (fun acc a => acc ++ [f a]) out = out ++ l.map f := by
  induction l generalizing out with
  | nil => simp
  | cons a l ih => simp [ih]

/-- Any zero-preserving bitwise operation on `ℕ` is read off by folding `op` over `digitPairs`. -/
private lemma bitwise_eq (op : Bool → Bool → Bool) (h0 : op false false = false) (p : ℕ × ℕ) :
    Nat.bitwise op p.1 p.2 =
      ofBits ((digitPairs p).foldl (fun acc d => acc ++ [op d.1 d.2]) []) := by
  rw [foldl_append_singleton, List.nil_append, ofBits]
  have hmap : (digitPairs p).map (fun d => op d.1 d.2) =
      (List.range (p.1.bits.length + p.2.bits.length)).map
        (Nat.bitwise op p.1 p.2).testBit := by
    simp only [digitPairs, List.map_map, Function.comp_def, bits_getD, ← Nat.testBit_bitwise h0]
  rw [hmap, Nat.foldr_bit_testBit]
  rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]
  refine Nat.size_le.2 (Nat.bitwise_lt_two_pow ?_ ?_)
  · exact (Nat.lt_size_self p.1).trans_le (Nat.pow_le_pow_right (by lia) (by lia))
  · exact (Nat.lt_size_self p.2).trans_le (Nat.pow_le_pow_right (by lia) (by lia))

private lemma ofBits_tail (w : List Bool) : ofBits w.tail = ofBits w / 2 := by
  cases w with
  | nil => simp [ofBits]
  | cons b w =>
    simp only [List.tail_cons, ofBits, List.foldr_cons, Nat.bit_val]
    cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> lia

private lemma ofBits_drop (w : List Bool) (k : ℕ) : ofBits (w.drop k) = ofBits w / 2 ^ k := by
  induction k generalizing w with
  | zero => simp
  | succ k ih =>
    rw [← List.drop_tail, ih, ofBits_tail, Nat.div_div_eq_div_mul, Nat.pow_succ']

/-- Right shift drops at most the dividend's bit length of least-significant digits. -/
private lemma shiftRight_eq_ofBits_drop (p : ℕ × ℕ) :
    p.1 >>> p.2 = ofBits (p.1.bits.drop (min p.1.bits.length p.2)) := by
  have hdrop : p.1.bits.drop (min p.1.bits.length p.2) = p.1.bits.drop p.2 := by
    rcases le_total p.1.bits.length p.2 with h | h
    · rw [Nat.min_eq_left h, List.drop_eq_nil_of_le le_rfl, List.drop_eq_nil_of_le h]
    · rw [Nat.min_eq_right h]
  rw [hdrop, ofBits_drop, ofBits, Nat.foldr_bit_bits, Nat.shiftRight_eq_div_pow]

end Turing.MultiTapeTM.BinarySub

namespace Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-- Decode arbitrary little-endian bit words to binary naturals. -/
@[fun_prop]
theorem bitsToNat : ComputableTidilyInPolyTime ofBits encBits encNat := by
  obtain ⟨c, d, k, State, hfin, tm, htm⟩ :=
    Internal.NormalForm.polyTime ComputableInPolyTime.bitsToNat
  exact ⟨_, _, .of_forall_le c d (fun _ => le_rfl),
    .of_forall_le c d (fun _ => le_rfl), k, State, hfin, tm, htm⟩

/-- The binary digits of a natural number, as a raw bit string. -/
@[fun_prop]
theorem natBits : ComputableTidilyInPolyTime Nat.bits encNat encBits := of_eq fun _ => rfl

/-- Addition of binary naturals. -/
@[fun_prop]
theorem binary_add : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => p.1 + p.2)
    (encPair encNat encNat) encNat :=
  ComputableInPolyTime.binary_add.tidy

/-- Multiplication of binary naturals. -/
@[fun_prop]
theorem binary_mul : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => p.1 * p.2)
    (encPair encNat encNat) encNat :=
  (ComputableInPolyTime.binary_mul' (ComputableInPolyTime.fst encNat encNat)
    (ComputableInPolyTime.snd encNat encNat)).tidy

/-- Add computed binary values, fixing their intermediate encodings for proof search. -/
@[fun_prop]
theorem binary_add' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableTidilyInPolyTime left input encNat)
    (hright : ComputableTidilyInPolyTime right input encNat) :
    ComputableTidilyInPolyTime (fun a => left a + right a) input encNat :=
  binary_add.comp (hleft.prod hright)

/-- The sum of a list of binary naturals, by a left fold of binary additions. -/
@[fun_prop]
theorem binary_sum : ComputableTidilyInPolyTime List.sum (encList encNat) encNat := by
  have hq := fst (encPair (encList encNat) encNat) encNat
  have h := foldlWith_of_bounded_growth (encA := encNat) (encL := encList encNat)
    (encB := encNat) (par := fun l : List ℕ => l) (list := fun l => l)
    (step := fun _ s a => s + a) id' id' (const 0) (binary_add.comp (hq.snd'.prod (snd _ _)))
    (growth := fun l => (encList encNat l).length + 1) (.add .self (.const 1))
    (fun l s a ha => by
      have := length_le_encList_of_mem encNat ha
      simp only [encNat_apply, Nat.size_eq_bits_len] at this ⊢
      have := Nat.size_add_le s a
      lia)
  simpa only [← List.sum_eq_foldl_nat] using h

/-- `2 ^ k` in binary, from `k` in unary, by doubling. -/
@[fun_prop]
theorem binary_two_pow : ComputableTidilyInPolyTime (fun k : ℕ => 2 ^ k) encUnary encNat := by
  have hfold (k : ℕ) : (List.replicate k true).foldl (fun n _ => n + n) 1 = 2 ^ k := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [List.replicate_succ', List.foldl_append, ih, List.foldl_cons, List.foldl_nil,
        Nat.pow_succ]
      lia
  have hq := fst encNat encBool
  have h := foldl_of_bounded_growth (encA := encBool) (encL := encBits) (encB := encNat)
    (list := fun k => List.replicate k true) (step := fun n _ => n + n)
    (of_eq (encIn := encUnary) (encMid := encBits) fun _ => rfl) (const 1)
    (binary_add.comp (hq.prod hq)) (growth := 1)
    (fun n _ => by
      simp only [encNat_apply, Nat.size_eq_bits_len]
      refine Nat.size_le.2 ?_
      have := Nat.lt_size_self n
      rw [Nat.pow_succ]
      lia)
  simpa only [hfold] using h

/-- Strict comparison of binary naturals, from the linear zip-transducer certificate. -/
@[fun_prop]
theorem binary_lt : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => decide (p.1 < p.2))
    (encPair encNat encNat) encBool :=
  ComputableInPolyTime.binary_lt.tidy

/-- Comparison of binary naturals, from the linear zip-transducer certificate. -/
@[fun_prop]
theorem binary_le : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => decide (p.1 ≤ p.2))
    (encPair encNat encNat) encBool :=
  ComputableInPolyTime.binary_le.tidy

/-- Strictly compare computed binary values, fixing their intermediate encodings. -/
@[fun_prop]
theorem binary_lt' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableTidilyInPolyTime left input encNat)
    (hright : ComputableTidilyInPolyTime right input encNat) :
    ComputableTidilyInPolyTime (fun a => decide (left a < right a)) input encBool :=
  binary_lt.comp (hleft.prod hright)

/-- Compare computed binary values, fixing their intermediate encodings. -/
@[fun_prop]
theorem binary_le' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableTidilyInPolyTime left input encNat)
    (hright : ComputableTidilyInPolyTime right input encNat) :
    ComputableTidilyInPolyTime (fun a => decide (left a ≤ right a)) input encBool :=
  binary_le.comp (hleft.prod hright)

/-- Multiply computed binary values, fixing their intermediate encodings for proof search. -/
@[fun_prop]
theorem binary_mul' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableTidilyInPolyTime left input encNat)
    (hright : ComputableTidilyInPolyTime right input encNat) :
    ComputableTidilyInPolyTime (fun a => left a * right a) input encNat :=
  binary_mul.comp (hleft.prod hright)

/-- A power of a binary natural to a unary exponent, by repeated multiplication. -/
@[fun_prop]
theorem binary_pow : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => p.1 ^ p.2)
    (encPair encNat encUnary) encNat := by
  have hfold (m k : ℕ) : (List.replicate k true).foldl (fun n _ => n * m) 1 = m ^ k := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [List.replicate_succ', List.foldl_append, ih, List.foldl_cons, List.foldl_nil,
        Nat.pow_succ]
  have hlist : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => List.replicate p.2 true)
      (encPair encNat encUnary) encBits :=
    (of_eq (encIn := encUnary) (encMid := encBits) fun _ => rfl).comp (snd encNat encUnary)
  have hq := fst (encPair encNat encNat) encBool
  have h := foldlWith_of_bounded_growth (encA := encBool) (encL := encBits) (encB := encNat)
    (par := fun p : ℕ × ℕ => p.1) (step := fun m n _ => n * m) (init := fun _ => 1)
    (fst encNat encUnary) hlist (const 1) (binary_mul.comp (hq.snd'.prod hq.fst'))
    (growth := fun p => (encPair encNat encUnary p).length) .self
    (fun p n _ _ => by
      have := Nat.size_mul_le n p.1
      have := length_le_encPair_left encNat encUnary p
      simp only [encNat_apply, Nat.size_eq_bits_len] at this ⊢
      lia)
  simpa only [hfold] using h

/-- Raise a computed binary value to a computed unary exponent, fixing the intermediate
encodings. -/
@[fun_prop]
theorem binary_pow' {α : Type} {input : α ↪ List Bool} {base exponent : α → ℕ}
    (hbase : ComputableTidilyInPolyTime base input encNat)
    (hexponent : ComputableTidilyInPolyTime exponent input encUnary) :
    ComputableTidilyInPolyTime (fun a => base a ^ exponent a) input encNat :=
  binary_pow.comp (hbase.prod hexponent)

/-- Truncated subtraction of binary naturals, reusing the shared plain schoolbook certificate. -/
@[fun_prop]
theorem binary_sub : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => p.1 - p.2)
    (encPair encNat encNat) encNat :=
  ComputableInPolyTime.binary_sub.tidy

/-- Subtract computed binary values, truncating at zero and fixing their intermediate
encodings. -/
@[fun_prop]
theorem binary_sub' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableTidilyInPolyTime left input encNat)
    (hright : ComputableTidilyInPolyTime right input encNat) :
    ComputableTidilyInPolyTime (fun a => left a - right a) input encNat :=
  binary_sub.comp (hleft.prod hright)

/-- Read the bit of a computed binary number at a computed unary position. -/
@[fun_prop]
theorem binary_testBit {α : Type} {input : α ↪ List Bool} {n i : α → ℕ}
    (hn : ComputableTidilyInPolyTime n input encNat)
    (hi : ComputableTidilyInPolyTime i input encUnary) :
    ComputableTidilyInPolyTime (fun a => (n a).testBit (i a)) input encBool := by
  refine ((bitsGetD false).comp ((natBits.comp hn).prod hi)).of_enc_eq fun a => ?_
  simp only [Function.comp_apply, Nat.testBit_eq_inth, ← List.getD_default_eq_getI]
  rfl

/-- Any zero-preserving bitwise operation on binary naturals is polynomial-time. -/
private theorem binary_bitwise (op : Bool → Bool → Bool) (h0 : op false false = false) :
    ComputableTidilyInPolyTime (fun p : ℕ × ℕ => Nat.bitwise op p.1 p.2)
      (encPair encNat encNat) encNat := by
  have hpairs : ComputableTidilyInPolyTime BinarySub.digitPairs (encPair encNat encNat)
      (encList (encPair encBool encBool)) := by
    unfold BinarySub.digitPairs
    fun_prop
  have hop : ComputableTidilyInPolyTime (fun d : Bool × Bool => op d.1 d.2)
      (encPair encBool encBool) encBool := of_finite _
  have hstep : ComputableTidilyInPolyTime
      (fun p : List Bool × (Bool × Bool) => p.1 ++ [op p.2.1 p.2.2])
      (encPair encBits (encPair encBool encBool)) encBits :=
    bitsAppend (fst _ _) (bitsCons (hop.comp (snd _ _)) (const []))
  have hfold := foldl_of_bounded_growth (encA := encPair encBool encBool)
    (encL := encList (encPair encBool encBool)) (encB := encBits)
    (step := fun acc d => acc ++ [op d.1 d.2])
    (init := fun _ => []) hpairs (const []) hstep (growth := 1) (fun _ _ => by simp)
  convert bitsToNat.comp hfold using 1
  funext p
  exact BinarySub.bitwise_eq op h0 p

/-- The smaller of a unary natural and a binary natural, returned in unary by saturating binary
decoding. -/
private theorem binary_min_unary : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => min p.1 p.2)
    (encPair encUnary encNat) encUnary := by
  have h := foldlWith (encA := encBool) (encL := encBits) (encP := encUnary)
    (par := Prod.fst) (list := fun p : ℕ × ℕ => p.2.bits.reverse)
    (step := fun cap value bit => min cap (2 * value + bit.toNat))
    (fst encUnary encNat) (bitsReverse.comp (natBits.comp (snd encUnary encNat)))
    (const 0) (by fun_prop) (B := Prod.fst)
    (by simpa only [encUnary_apply, List.length_replicate] using
      (fst encUnary encNat).polyBounded_length)
    (fun p i _ => by
      simpa only [encUnary_apply, List.length_replicate, Cslib.BitString.boundedBinaryValue] using
        Cslib.BitString.boundedBinaryValue_le p.1 (p.2.bits.reverse.take i))
  convert h using 1
  funext p
  rw [← Cslib.BitString.boundedBinaryValue, Cslib.BitString.boundedBinaryValue_eq,
    Cslib.BitString.binaryValue_reverse_bits]

/-- Cap a computed binary natural by a computed unary bound, returning the result in unary. -/
private theorem binary_min_unary' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableTidilyInPolyTime left input encUnary)
    (hright : ComputableTidilyInPolyTime right input encNat) :
    ComputableTidilyInPolyTime (fun a => min (left a) (right a)) input encUnary :=
  binary_min_unary.comp (hleft.prod hright)

/-- Right shift of binary naturals, by dropping at most the dividend's bit length of low-order
digits. -/
private theorem binary_shiftRight : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => p.1 >>> p.2)
    (encPair encNat encNat) encNat := by
  have hbits := natBits.comp (fst encNat encNat)
  have hlen : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => p.1.bits.length)
      (encPair encNat encNat) encUnary := (length encBool).comp hbits
  have hdrop := bitsDropWithInput hbits (binary_min_unary' hlen (snd encNat encNat))
  convert bitsToNat.comp hdrop using 1
  funext p
  exact BinarySub.shiftRight_eq_ofBits_drop p

end Turing.MultiTapeTM.ComputableTidilyInPolyTime

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Any zero-preserving bitwise operation on binary naturals is polynomial-time. -/
theorem binary_bitwise (op : Bool → Bool → Bool) (h0 : op false false = false) :
    ComputableInPolyTime (fun p : ℕ × ℕ => Nat.bitwise op p.1 p.2)
      (encPair encNat encNat) encNat :=
  .of_tidy (ComputableTidilyInPolyTime.binary_bitwise op h0)

/-- Bitwise AND of binary naturals. -/
@[fun_prop]
theorem binary_and : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 &&& p.2)
    (encPair encNat encNat) encNat :=
  .of_tidy <| (ComputableTidilyInPolyTime.binary_bitwise and rfl).of_enc_eq fun p =>
    congrArg encNat <| Nat.eq_of_testBit_eq fun i => by
      rw [Nat.testBit_bitwise rfl, Nat.testBit_and]

/-- Bitwise OR of binary naturals, from the linear zip-transducer certificate
`Turing.MultiTapeTM.computableInTimeAndSpace_natOr`. -/
@[fun_prop]
theorem binary_or : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 ||| p.2)
    (encPair encNat encNat) encNat :=
  (ComputableInO.of_linear ComputableInDegree.natOr).computableInPolyTime
    (PolyBounded.of_forall_le 1 1 (fun _ => by simp))
    (PolyBounded.of_forall_le 1 1 (fun _ => by simp))

/-- Bitwise XOR of binary naturals. -/
@[fun_prop]
theorem binary_xor : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 ^^^ p.2)
    (encPair encNat encNat) encNat :=
  .of_tidy <| (ComputableTidilyInPolyTime.binary_bitwise xor rfl).of_enc_eq fun p =>
    congrArg encNat <| Nat.eq_of_testBit_eq fun i => by
      rw [Nat.testBit_bitwise rfl, Nat.testBit_xor]

/-- Bitwise AND of computed binary naturals. -/
@[fun_prop]
theorem binary_and' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encNat)
    (hright : ComputableInPolyTime right input encNat) :
    ComputableInPolyTime (fun a => left a &&& right a) input encNat :=
  binary_and.comp (hleft.prod hright)

/-- Bitwise OR of computed binary naturals. -/
@[fun_prop]
theorem binary_or' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encNat)
    (hright : ComputableInPolyTime right input encNat) :
    ComputableInPolyTime (fun a => left a ||| right a) input encNat :=
  binary_or.comp (hleft.prod hright)

/-- Bitwise XOR of computed binary naturals. -/
@[fun_prop]
theorem binary_xor' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encNat)
    (hright : ComputableInPolyTime right input encNat) :
    ComputableInPolyTime (fun a => left a ^^^ right a) input encNat :=
  binary_xor.comp (hleft.prod hright)

/-- The bit-length `Nat.size n` of a binary natural, returned in unary. -/
@[fun_prop]
theorem binary_size : ComputableInPolyTime Nat.size encNat encUnary := by
  have hbits : ComputableInPolyTime Nat.bits encNat encBits := of_eq fun _ => rfl
  convert Internal.DecoderWords.unary_degree.computableInPolyTime.comp hbits using 1
  funext n
  exact (Nat.size_eq_bits_len n).symm

/-- The smaller of a unary natural and a binary natural, returned in unary by saturating binary
decoding. -/
@[fun_prop]
theorem binary_min_unary : ComputableInPolyTime (fun p : ℕ × ℕ => min p.1 p.2)
    (encPair encUnary encNat) encUnary :=
  .of_tidy ComputableTidilyInPolyTime.binary_min_unary

/-- Cap a computed binary natural by a computed unary bound, returning the result in unary. -/
@[fun_prop]
theorem binary_min_unary' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encUnary)
    (hright : ComputableInPolyTime right input encNat) :
    ComputableInPolyTime (fun a => min (left a) (right a)) input encUnary :=
  binary_min_unary.comp (hleft.prod hright)

/-- Right shift of binary naturals, by dropping at most the dividend's bit length of low-order
digits. -/
@[fun_prop]
theorem binary_shiftRight : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 >>> p.2)
    (encPair encNat encNat) encNat :=
  .of_tidy ComputableTidilyInPolyTime.binary_shiftRight

/-- Right shift of computed binary naturals. -/
@[fun_prop]
theorem binary_shiftRight' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encNat)
    (hright : ComputableInPolyTime right input encNat) :
    ComputableInPolyTime (fun a => left a >>> right a) input encNat :=
  binary_shiftRight.comp (hleft.prod hright)

/-- The strict order of two computed numbers in binary. -/
@[fun_prop]
theorem binary_lt' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encNat)
    (hright : ComputableInPolyTime right input encNat) :
    ComputableInPolyTime (fun a => decide (left a < right a)) input encBool :=
  binary_lt.comp (hleft.prod hright)

end Turing.MultiTapeTM.ComputableInPolyTime

/-! ### Plain polynomial-time automation -/

namespace Turing.MultiTapeTM.ComputableInPolyTime

-- Preserve the original facade's registration scope for captured binary multiplication.
attribute [fun_prop] binary_mul'

/-- `2 ^ k` in binary, from `k` in unary, by doubling. -/
@[fun_prop]
theorem binary_two_pow :
    ComputableInPolyTime (fun (k : ℕ) => 2 ^ k)
  encUnary encNat :=
  .of_tidy Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_two_pow

end Turing.MultiTapeTM.ComputableInPolyTime

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Subtract computed binary values using the shared plain certificate. -/
theorem binary_sub' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encNat)
    (hright : ComputableInPolyTime right input encNat) :
    ComputableInPolyTime (fun a => left a - right a) input encNat :=
  binary_sub.comp (hleft.prod hright)

/-- `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_pow'` for plain certificates. -/
theorem binary_pow' {α : Type} {input : α ↪ List Bool} {base exponent : α → ℕ}
    (hbase : ComputableInPolyTime base input encNat)
    (hexponent : ComputableInPolyTime exponent input encUnary) :
    ComputableInPolyTime (fun a => base a ^ exponent a) input encNat :=
  .of_tidy (ComputableTidilyInPolyTime.binary_pow' (hbase := hbase.tidy)
    (hexponent := hexponent.tidy))

end Turing.MultiTapeTM.ComputableInPolyTime


