-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Foundations_Data_BitString_Basic
-- name    : Complexitylib_0ebd467_Foundations_Data_BitString_Basic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:33:12.557483+00:00
-- url     : https://prove2.me/theorems/f3d4b9f1-aa97-4b21-9d9d-816d2ea638d8
-- title:
--   Complexity.Foundations.Data.BitString.Basic — Counting, numbering and adding bit strings
-- statement:
--   This is module `Complexity.Foundations.Data.BitString.Basic` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   There are `2 ^ n` strings of `n` bits (`BitString.card`), numbered `0, …, 2 ^ n - 1` by reading
--   their bits as binary digits, least significant first (`BitString.equivFin`).
--
--   Bits form the two-element Boolean ring (Mathlib's `BooleanRing Bool`), in which `a + b = (a ^^ b)`
--   and `a * b = (a && b)`, so bit strings `ι → Bool` form an additive group under coordinatewise
--   exclusive or, the vector space `𝔽₂ⁿ` of [O'Donnell, Chapter 1][ODonnell2014]:
--   `(x + y) i = (x i ^^ y i)` holds by definition. Every bit string is its own negative
--   (`BitString.add_self`). Translating by a fixed string is the permutation `Equiv.addLeft x`.
--
--   Throughout the library, bit strings are added with `+`, while single bits, such as the values of
--   Boolean functions, are combined with `^^`.
--
--   ### Main definitions
--
--   * `Cslib.BitString.equivFin`: the numbering of the strings of `n` bits by `Fin (2 ^ n)`.
--   * `Cslib.BitString.fstBits`, `Cslib.BitString.sndBits`: the two parts of an appended word.
--   * `Cslib.BitString.zeroExtend`: prefix / zero-extension of a bit string to another length.
--   * `Cslib.BitString.indexBits`: a finite index represented in `⌈log₂ n⌉` bits.
--
--   ### Main results
--
--   * `Cslib.BitString.card`: the number of strings of `n` bits.
--   * `Cslib.BitString.val_equivFin_eq_sum`: the unsigned value as a sum of binary digits.
--   * `Cslib.BitString.val_equivFin_cons`: a new first bit is the least significant binary digit.
--   * `Cslib.BitString.val_equivFin_succ`, `Cslib.BitString.decide_equivFin_le_succ`: numbering and
--     comparing words by their highest bit.
--   * `Cslib.BitString.fstBits_apply`, `Cslib.BitString.sndBits_apply`,
--     `Cslib.BitString.fstBits_append`, `Cslib.BitString.sndBits_append`,
--     `Cslib.BitString.append_fstBits_sndBits`: splitting and reassembling an appended word.
--   * `Cslib.BitString.zeroExtend_self`, `Cslib.BitString.init_zeroExtend_succ`,
--     `Cslib.BitString.last_zeroExtend_succ`, `Cslib.BitString.zeroExtend_injective`: properties of
--     `Cslib.BitString.zeroExtend`.
--   * `Cslib.BitString.indexBits_injective`: distinct finite indices have distinct encodings.
--   * `Cslib.BitString.add_self`, `Cslib.BitString.add_cancel_left`,
--     `Cslib.BitString.add_cancel_right`: every bit string is its own negative.
--
--   ### References
--
--   * [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
--
--   **Contents.** The module is published as a whole: 24 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_BitString_Basic`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Foundations/Data/BitString/Basic.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Foundations/Data/BitString.lean`)

public import Definitions.Def_Cslib_254e30e_Foundations_Data_BitString
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Log
import Mathlib.Data.Fintype.BigOperators

/- Prove2me definition bundle for `Complexity.Foundations.Data.BitString.Basic` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Counting, numbering and adding bit strings

There are `2 ^ n` strings of `n` bits (`BitString.card`), numbered `0, …, 2 ^ n - 1` by reading
their bits as binary digits, least significant first (`BitString.equivFin`).

Bits form the two-element Boolean ring (Mathlib's `BooleanRing Bool`), in which `a + b = (a ^^ b)`
and `a * b = (a && b)`, so bit strings `ι → Bool` form an additive group under coordinatewise
exclusive or, the vector space `𝔽₂ⁿ` of [O'Donnell, Chapter 1][ODonnell2014]:
`(x + y) i = (x i ^^ y i)` holds by definition. Every bit string is its own negative
(`BitString.add_self`). Translating by a fixed string is the permutation `Equiv.addLeft x`.

Throughout the library, bit strings are added with `+`, while single bits, such as the values of
Boolean functions, are combined with `^^`.

## Main definitions

* `Cslib.BitString.equivFin`: the numbering of the strings of `n` bits by `Fin (2 ^ n)`.
* `Cslib.BitString.fstBits`, `Cslib.BitString.sndBits`: the two parts of an appended word.
* `Cslib.BitString.zeroExtend`: prefix / zero-extension of a bit string to another length.
* `Cslib.BitString.indexBits`: a finite index represented in `⌈log₂ n⌉` bits.

## Main results

* `Cslib.BitString.card`: the number of strings of `n` bits.
* `Cslib.BitString.val_equivFin_eq_sum`: the unsigned value as a sum of binary digits.
* `Cslib.BitString.val_equivFin_cons`: a new first bit is the least significant binary digit.
* `Cslib.BitString.val_equivFin_succ`, `Cslib.BitString.decide_equivFin_le_succ`: numbering and
  comparing words by their highest bit.
* `Cslib.BitString.fstBits_apply`, `Cslib.BitString.sndBits_apply`,
  `Cslib.BitString.fstBits_append`, `Cslib.BitString.sndBits_append`,
  `Cslib.BitString.append_fstBits_sndBits`: splitting and reassembling an appended word.
* `Cslib.BitString.zeroExtend_self`, `Cslib.BitString.init_zeroExtend_succ`,
  `Cslib.BitString.last_zeroExtend_succ`, `Cslib.BitString.zeroExtend_injective`: properties of
  `Cslib.BitString.zeroExtend`.
* `Cslib.BitString.indexBits_injective`: distinct finite indices have distinct encodings.
* `Cslib.BitString.add_self`, `Cslib.BitString.add_cancel_left`,
  `Cslib.BitString.add_cancel_right`: every bit string is its own negative.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

@[expose] public section

namespace Cslib.BitString

variable {n : ℕ}

/-- There are `2 ^ n` strings of `n` bits. -/
theorem card : Fintype.card (BitString n) = 2 ^ n := by
  simp

variable (n) in
/-- The strings of `n` bits numbered `0, …, 2 ^ n - 1`, reading the bits as binary digits with
the least significant bit first. -/
def equivFin : BitString n ≃ Fin (2 ^ n) :=
  (Equiv.arrowCongr (Equiv.refl (Fin n)) finTwoEquiv.symm).trans finFunctionFinEquiv

/-- A new first bit is the least significant digit of the number of a bit string. -/
theorem val_equivFin_cons (b : Bool) (z : BitString n) :
    (equivFin (n + 1) (Fin.cons b z : BitString (n + 1)) : ℕ) = b.toNat + 2 * equivFin n z := by
  have hbit (b : Bool) : ((finTwoEquiv.symm b : Fin 2) : ℕ) = b.toNat := by cases b <;> rfl
  simp only [equivFin, Equiv.trans_apply, finFunctionFinEquiv_apply, Fin.sum_univ_succ,
    Equiv.arrowCongr_apply, Function.comp_apply, Equiv.refl_symm, Equiv.refl_apply, hbit,
    Fin.val_zero, pow_zero, Nat.mul_one, Fin.val_succ, pow_succ, Fin.cons_zero, Fin.cons_succ,
    Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by
    rw [Nat.mul_comm (2 ^ (i : ℕ)) 2, Nat.mul_left_comm]

/-- The number of a word of `n + 1` bits is the number of its first `n` bits plus its last bit
times `2 ^ n`. -/
theorem val_equivFin_succ (x : BitString (n + 1)) :
    (BitString.equivFin (n + 1) x : ℕ) =
      BitString.equivFin n (Fin.init x) + (x (Fin.last n)).toNat * 2 ^ n := by
  simp only [BitString.equivFin, Equiv.trans_apply, finFunctionFinEquiv_apply,
    Fin.sum_univ_castSucc, Equiv.arrowCongr_apply, Function.comp_apply, Equiv.refl_symm,
    Equiv.refl_apply, Fin.init, Fin.val_last]
  congr 1
  cases x (Fin.last n) <;> rfl

/-- The unsigned value of an `n`-bit word (least significant bit first) as an explicit sum. -/
theorem val_equivFin_eq_sum (x : BitString n) :
    (BitString.equivFin n x : ℕ) = ∑ i : Fin n, (x i).toNat * 2 ^ (i : ℕ) := by
  induction n with
  | zero =>
    have h := (BitString.equivFin 0 x).isLt
    simp only [pow_zero, Nat.lt_one_iff] at h
    simp
  | succ n ih =>
    rw [BitString.val_equivFin_succ, ih, Fin.sum_univ_castSucc, Fin.val_last]
    rfl

/-- The zero word of `n` bits has unsigned value zero. -/
@[simp] theorem val_equivFin_false (n : ℕ) :
    (BitString.equivFin n (fun _ => false) : ℕ) = 0 := by
  rw [val_equivFin_eq_sum]
  simp

/-- The first `a` bits of an `(a + b)`-bit word. -/
def fstBits {a b : ℕ} (x : BitString (a + b)) : BitString a :=
  ((Fin.appendEquiv a b).symm x).1

/-- The last `b` bits of an `(a + b)`-bit word. -/
def sndBits {a b : ℕ} (x : BitString (a + b)) : BitString b :=
  ((Fin.appendEquiv a b).symm x).2

/-- Bit `i` of `fstBits x` is bit `Fin.castAdd b i` of `x`. -/
@[simp] theorem fstBits_apply {a b : ℕ} (x : BitString (a + b)) (i : Fin a) :
    fstBits x i = x (Fin.castAdd b i) :=
  rfl

/-- Bit `i` of `sndBits x` is bit `Fin.natAdd a i` of `x`. -/
@[simp] theorem sndBits_apply {a b : ℕ} (x : BitString (a + b)) (i : Fin b) :
    sndBits x i = x (Fin.natAdd a i) :=
  rfl

/-- The first `a` bits of `Fin.append u v` are `u`. -/
@[simp] theorem fstBits_append {a b : ℕ} (u : BitString a) (v : BitString b) :
    fstBits (Fin.append u v) = u :=
  funext fun i => Fin.append_left u v i

/-- The last `b` bits of `Fin.append u v` are `v`. -/
@[simp] theorem sndBits_append {a b : ℕ} (u : BitString a) (v : BitString b) :
    sndBits (Fin.append u v) = v :=
  funext fun i => Fin.append_right u v i

/-- Appending the first `a` bits and last `b` bits of an `(a + b)`-bit word recovers it. -/
@[simp] theorem append_fstBits_sndBits {a b : ℕ} (x : BitString (a + b)) :
    Fin.append (fstBits x) (sndBits x) = x :=
  (Fin.appendEquiv a b).apply_symm_apply x

/-- The `d'`-bit prefix or zero-extension of a point `x : BitString d`, padded with `false` on
coordinates `i ≥ d`. -/
def zeroExtend {d d' : ℕ} (x : BitString d) : BitString d' :=
  fun i => if h : i.val < d then x ⟨i.val, h⟩ else false

@[simp]
theorem zeroExtend_self {d : ℕ} (x : BitString d) :
    zeroExtend (d' := d) x = x := by
  funext j
  simp [zeroExtend, j.isLt]

@[simp]
theorem init_zeroExtend_succ {d k : ℕ} (x : BitString d) :
    Fin.init (zeroExtend (d' := k + 1) x) = zeroExtend (d' := k) x := by
  funext j
  simp [Fin.init, zeroExtend]

@[simp]
theorem last_zeroExtend_succ {d k : ℕ} (hk : k < d) (x : BitString d) :
    zeroExtend (d' := k + 1) x (Fin.last k) = x ⟨k, hk⟩ := by
  simp [Fin.last, zeroExtend, hk]

/-- Extension by zeros from `BitString d` to `BitString d'` is injective when `d ≤ d'`. -/
theorem zeroExtend_injective {d d' : ℕ} (h : d ≤ d') :
    Function.Injective (zeroExtend (d := d) (d' := d')) := by
  intro x y hxy
  funext i
  have := congrFun hxy ⟨i.val, by omega⟩
  simpa [zeroExtend, i.isLt] using this

/-- Comparing words of `n + 1` bits: `x ≤ y` when the last bit of `x` is below that of `y`, or when
they are equal and `x ≤ y` on the first `n` bits. -/
theorem decide_equivFin_le_succ (x y : BitString (n + 1)) :
    decide (BitString.equivFin (n + 1) x ≤ BitString.equivFin (n + 1) y) =
      ((!x (Fin.last n) && y (Fin.last n)) || ((!x (Fin.last n) || y (Fin.last n)) &&
        decide (BitString.equivFin n (Fin.init x) ≤ BitString.equivFin n (Fin.init y)))) := by
  have hx := (BitString.equivFin n (Fin.init x)).isLt
  have hy := (BitString.equivFin n (Fin.init y)).isLt
  have e : BitString.equivFin (n + 1) x ≤ BitString.equivFin (n + 1) y ↔
      (BitString.equivFin n (Fin.init x) : ℕ) + (x (Fin.last n)).toNat * 2 ^ n ≤
        BitString.equivFin n (Fin.init y) + (y (Fin.last n)).toNat * 2 ^ n := by
    rw [Fin.le_iff_val_le_val, BitString.val_equivFin_succ, BitString.val_equivFin_succ]
  rw [Bool.eq_iff_iff, decide_eq_true_iff, e]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_iff, Fin.le_iff_val_le_val]
  generalize (BitString.equivFin n (Fin.init x) : ℕ) = a at hx ⊢
  generalize (BitString.equivFin n (Fin.init y) : ℕ) = b at hy ⊢
  generalize 2 ^ n = P at hx hy ⊢
  cases x (Fin.last n) <;> cases y (Fin.last n) <;>
    simp only [Bool.toNat_false, Bool.toNat_true, zero_mul, one_mul, add_zero,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, and_false, or_false, true_and,
      false_or, and_self, or_self, true_or, iff_true, false_and, iff_false, not_le,
      add_le_add_iff_right, and_true, or_true] <;> omega

/-- The binary numeral of `i : Fin n` in `⌈log₂ n⌉` bits. -/
def indexBits (i : Fin n) : BitString (Nat.clog 2 n) :=
  (equivFin _).symm (Fin.castLE (Nat.le_pow_clog one_lt_two n) i)

/-- Distinct finite indices have distinct binary numerals. -/
theorem indexBits_injective : Function.Injective (indexBits (n := n)) :=
  (equivFin _).symm.injective.comp (Fin.castLE_injective _)

variable {ι : Type*}

/-- A bit string added to itself gives zero. -/
@[simp] protected theorem add_self (x : ι → Bool) : x + x = 0 :=
  funext fun i => Bool.xor_self (x i)

/-- Adding `x` twice cancels: `x + (x + y) = y`. -/
@[simp] protected theorem add_cancel_left (x y : ι → Bool) : x + (x + y) = y := by
  rw [← add_assoc, BitString.add_self, zero_add]

/-- Adding `y` twice cancels: `x + y + y = x`. -/
@[simp] protected theorem add_cancel_right (x y : ι → Bool) : x + y + y = x := by
  rw [add_assoc, BitString.add_self, add_zero]

end Cslib.BitString


