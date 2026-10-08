-- Prove2me | Definitions.Def_APSPSource_ThreeSumApsp_Util_Digits
-- name    : APSPSource_ThreeSumApsp_Util_Digits
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T07:36:52.274186+00:00
-- url     : https://prove2.me/theorems/db8bcec5-31cb-47c7-9cc1-57bcdd151640
-- title:
--   Fixed-length digit encodings and finite-alphabet equivalences
-- statement:
--   For a natural base $b$ and digits $d_0,\ldots,d_{n-1}$ written most significant first, define
--
--   $$\operatorname{code}_b(d)=\sum_{i=0}^{n-1}d_i b^{n-1-i},\qquad
--   \operatorname{digit}_{b,n}(c,i)=\left\lfloor\frac{c}{b^{n-1-i}}\right\rfloor\bmod b.$$
--
--   The bundle also forms the list of $n$ digits and evaluates a digit list by Horner's rule. Its supporting properties show that digits below $b$ encode a number below $b^n$, that decoding recovers each digit, and that a number below $b^n$ is recovered by encoding its digits. These properties construct the equivalence
--
--   $$\{0,\ldots,b-1\}^{\{0,\ldots,n-1\}}\simeq\{0,\ldots,b^n-1\}.$$
--
--   Given a numbering of a finite alphabet by $0,\ldots,b-1$, the same construction supplies codes, digit lists, and an equivalence for strings over that alphabet. The standalone alphabet decoder assumes $b>0$.
--
--   These interfaces turn fixed-length symbolic strings into natural-number array indices. The underlying arithmetic functions are total, including zero-base cases; digit interpretations use the bounds stated above.
--
--   References:
--
--   1. [Source formalization, lines 44–57](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/Digits.lean#L44-L57).
--   2. [Source formalization, lines 79–140](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/Digits.lean#L79-L140).
--   3. [Source formalization, lines 148–160](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/Digits.lean#L148-L160).
--   4. [Source formalization, lines 229–235](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/Digits.lean#L229-L235).
--   5. [Source formalization, lines 282–284](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/Digits.lean#L282-L284).
--   6. [Source formalization, lines 288–290](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/Digits.lean#L288-L290).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/Digits.lean#L44-L57; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/Digits.lean#L79-L140; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/Digits.lean#L148-L160; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/Digits.lean#L229-L235; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/Digits.lean#L282-L284; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/Digits.lean#L288-L290

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Count
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Strings of digits as numbers

The paper indexes its arrays by strings (Section 2.3.1).  A program indexes them by numbers: the
string `d₁ d₂ ⋯ d_n` of digits in base `b` is coded by the number `d₁ b^{n-1} + ⋯ + d_n`.  The first
digit (the paper's level 1) is the most significant one, so the strings that begin with a given
digit have consecutive codes, and a slice of an array is a contiguous part of it.

* `code` is the number of a string, `digit` reads one digit of a number, `digitList` all of them,
  and `ofDigitList` is Horner's rule.
* `code` and `digit` undo each other (`digit_code`, `code_digit`), so the strings of length `n`
  correspond to the numbers below `b^n` (`codeEquiv`).
* For lists of digits, `digitList` undoes `ofDigitList` (`digitList_ofDigitList`). A list of `n`
  digits has a value below `b^n` (`ofDigitList_lt`), which determines it (`eq_of_ofDigitList_eq`).
  One more digit at the end is one more step of Horner's rule (`ofDigitList_append_singleton`,
  `ofDigitList_take_succ`).
* For an alphabet `α` whose letters are numbered by `e : α ≃ Fin b`, `codeStr e` and `decodeStr e`
  go from strings over `α` to numbers and back, so these strings, too, correspond to the numbers
  below `b^n` (`strEquiv`).  `digitsStr e` is the list of the digits of such a string; Horner's rule
  computes the code from it (`ofDigitList_digitsStr`).

Mathlib's `Nat.ofDigits` and `finFunctionFinEquiv` put the least significant digit first, so they
would make a slice a scattered part of an array; this is why the codes are defined here.
-/

@[expose] public section

namespace ThreeSumApsp

/-! ## Strings of numbers below `b` -/

/-- The number with the digits `d 0, d 1, …, d (n-1)` in base `b`, most significant digit first. -/
def code (b : ℕ) : {n : ℕ} → (Fin n → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, d => d 0 * b ^ n + code b (Fin.tail d)

/-- The digit number `ℓ` (counted from 0, most significant first) of the `n`-digit number `c` in
base `b`. -/
def digit (b n c ℓ : ℕ) : ℕ := c / b ^ (n - 1 - ℓ) % b

/-- The `n` digits of `c` in base `b`, most significant first, as a list. -/
def digitList (b n c : ℕ) : List ℕ := (List.range n).map (digit b n c)

/-- Horner's rule: the number with the given list of digits, most significant first. -/
def ofDigitList (b : ℕ) (l : List ℕ) : ℕ := l.foldl (fun acc x => acc * b + x) 0





















/-- An `n`-digit number is less than `b^n`. -/
theorem code_lt {b n : ℕ} {d : Fin n → ℕ} (hd : ∀ ℓ, d ℓ < b) : code b d < b ^ n := by
  induction n with
  | zero => simp [code]
  | succ n ih =>
    have hrest : code b (Fin.tail d) < b ^ n := ih fun ℓ => hd _
    have hfirst : d 0 * b ^ n + b ^ n ≤ b * b ^ n := by
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right _ (hd 0)
    rw [code, pow_succ']
    omega

/-- The first digit and the rest, by division. -/
theorem code_div_mod {b n : ℕ} {d : Fin (n + 1) → ℕ} (hd : ∀ ℓ, d ℓ < b) :
    code b d / b ^ n = d 0 ∧ code b d % b ^ n = code b (Fin.tail d) := by
  have hrest : code b (Fin.tail d) < b ^ n := code_lt fun ℓ => hd _
  have hpos : 0 < b ^ n := Nat.zero_lt_of_lt hrest
  rw [code, Nat.add_comm]
  exact ⟨by rw [Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hrest, Nat.zero_add],
    by rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hrest]⟩

/-- The digits after the first one are the digits of the remainder modulo `b^n`. -/
theorem digit_succ (b n c k : ℕ) (hk : k < n) :
    digit b (n + 1) c (k + 1) = digit b n (c % b ^ n) k := by
  obtain ⟨e, rfl⟩ : ∃ e, n = e + (k + 1) := ⟨n - (k + 1), by omega⟩
  rw [digit, digit, show e + (k + 1) + 1 - 1 - (k + 1) = e by omega,
    show e + (k + 1) - 1 - k = e by omega, pow_add, Nat.mod_mul_right_div_self,
    Nat.mod_mod_of_dvd _ (dvd_pow_self b k.succ_ne_zero)]

/-- The digits of the code are the digits. -/
theorem digit_code {b n : ℕ} {d : Fin n → ℕ} (hd : ∀ ℓ, d ℓ < b) (ℓ : Fin n) :
    digit b n (code b d) ℓ = d ℓ := by
  induction n with
  | zero => exact ℓ.elim0
  | succ n ih =>
    obtain ⟨hdiv, hmod⟩ := code_div_mod hd
    refine Fin.cases ?_ (fun k => ?_) ℓ
    · rw [digit, Fin.val_zero, Nat.sub_zero, Nat.add_sub_cancel, hdiv, Nat.mod_eq_of_lt (hd 0)]
    · rw [Fin.val_succ, digit_succ b n _ k k.isLt, hmod]
      exact ih (d := Fin.tail d) (fun ℓ => hd _) k

/-- A digit is less than the base. -/
theorem digit_lt {b : ℕ} (hb : 0 < b) (n c ℓ : ℕ) : digit b n c ℓ < b :=
  Nat.mod_lt _ hb

/-- A number below `b^n` is the code of its digits. -/
theorem code_digit {b n c : ℕ} (hc : c < b ^ n) : code b (fun ℓ : Fin n => digit b n c ℓ) = c := by
  induction n generalizing c with
  | zero =>
    rw [pow_zero, Nat.lt_one_iff] at hc
    rw [hc, code]
  | succ n ih =>
    rw [pow_succ'] at hc
    have hpos : 0 < b ^ n := Nat.pos_of_mul_pos_left (Nat.zero_lt_of_lt hc)
    have hfirst : digit b (n + 1) c 0 = c / b ^ n := by
      rw [digit, Nat.sub_zero, Nat.add_sub_cancel]
      exact Nat.mod_eq_of_lt ((Nat.div_lt_iff_lt_mul hpos).mpr hc)
    have hrest : (Fin.tail fun ℓ : Fin (n + 1) => digit b (n + 1) c ℓ)
        = fun ℓ : Fin n => digit b n (c % b ^ n) ℓ :=
      funext fun k => digit_succ b n c k k.isLt
    rw [code, hrest, ih (Nat.mod_lt _ hpos), Fin.val_zero, hfirst]
    exact Nat.div_add_mod' c (b ^ n)







/-- If some number is below `b^n` and `n` is not 0, the base is not 0. -/
theorem pos_of_lt_pow {b n c : ℕ} (hc : c < b ^ n) (hn : n ≠ 0) : 0 < b := by
  refine Nat.pos_of_ne_zero fun hb => ?_
  rw [hb, zero_pow hn] at hc
  exact Nat.not_lt_zero _ hc

/-- The strings of `n` digits in base `b` correspond to the numbers below `b^n`. -/
def codeEquiv (b n : ℕ) : (Fin n → Fin b) ≃ Fin (b ^ n) where
  toFun d := ⟨code b fun ℓ => (d ℓ : ℕ), code_lt fun ℓ => (d ℓ).isLt⟩
  invFun c := fun ℓ =>
    ⟨digit b n c ℓ, digit_lt (pos_of_lt_pow c.isLt (Nat.ne_zero_of_lt ℓ.isLt)) n c ℓ⟩
  left_inv d := funext fun ℓ => Fin.ext (digit_code (fun ℓ => (d ℓ).isLt) ℓ)
  right_inv c := Fin.ext (code_digit c.isLt)

/-! ## Lists of digits -/






























































/-! ## Strings over a numbered alphabet -/

variable {α : Type} {b : ℕ} (e : α ≃ Fin b)

/-- Strings over an alphabet `α` whose letters are numbered by `e : α ≃ Fin b`: the code of a
string. -/
def codeStr {n : ℕ} (u : Fin n → α) : ℕ := code b fun ℓ => (e (u ℓ) : ℕ)

/-- The string with a given code. -/
def decodeStr [NeZero b] (n c : ℕ) : Fin n → α :=
  fun ℓ => e.symm ⟨digit b n c ℓ, digit_lt (NeZero.pos b) n c ℓ⟩














































/-- The strings of length `n` over `α` correspond to the numbers below `b^n`. -/
def strEquiv (n : ℕ) : (Fin n → α) ≃ Fin (b ^ n) :=
  (Equiv.arrowCongr (Equiv.refl _) e).trans (codeEquiv b n)

/-! ## The list of the digits of a string -/

/-- The digits of a string over an alphabet with numbered symbols, level 1 first. -/
def digitsStr {α : Type} {b : ℕ} (e : α ≃ Fin b) {n : ℕ} (u : Fin n → α) : List ℕ :=
  List.ofFn fun ℓ => (e (u ℓ) : ℕ)

section

variable {α : Type} {b : ℕ} (e : α ≃ Fin b) {n : ℕ}















































end

end ThreeSumApsp


