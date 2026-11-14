-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Foundations_Data_BitString_Binary
-- name    : Complexitylib_0ebd467_Foundations_Data_BitString_Binary
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:33:33.671174+00:00
-- url     : https://prove2.me/theorems/a8468f72-c6f3-484e-9a5d-5231deca4a9b
-- title:
--   Complexity.Foundations.Data.BitString.Binary — Bridges between `BitString.equivFin` and binary numeral views
-- statement:
--   This is module `Complexity.Foundations.Data.BitString.Binary` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   `Cslib.BitString.equivFin n` numbers `n`-bit strings `Fin n → Bool` with `0` as the least
--   significant coordinate. This module connects `equivFin n` to the list-based numeral views
--   `Cslib.BitString.lsbValue` (least significant bit first) and `Cslib.BitString.binaryValue` (most
--   significant bit first), as well as `Nat.ofBits` and `Nat.testBit`, without adding a
--   `BitString.Basic` dependency to the list-level modules `BitString.Counter` or
--   `BitString.List.Binary`.
--
--   ### Main results
--
--   * `Cslib.BitString.val_equivFin_eq_ofBits`: `equivFin` agrees with `Nat.ofBits`.
--   * `Cslib.BitString.equivFin_symm_apply`: the `i`-th bit of `(equivFin n).symm k` is
--     `(k : ℕ).testBit i`.
--   * `Cslib.BitString.lsbValue_eq_binaryValue_reverse`: little-endian digits are the reversed
--     big-endian ones.
--   * `Cslib.BitString.lsbValue_ofFn`: reading the bits of an `n`-bit word in order gives its number in
--     `equivFin n`.
--   * `Cslib.BitString.binaryValue_reverse_ofFn`: reading the reversed list of bits of an `n`-bit word
--     gives its number in `equivFin n`.
--   * `Cslib.BitString.lsbValue_lowBits`: reading `lowBits n x` with `lsbValue` recovers `x < 2 ^ n`.
--   * `Cslib.BitString.lowBits_lsbValue`: re-encoding `lsbValue w` with `lowBits` recovers `w`.
--   * `Cslib.BitString.val_equivFin_add`: addition in `BitString n` is bitwise XOR (`^^^`) on
--     `equivFin n` coordinates.
--
--   **Contents.** The module is published as a whole: 9 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_BitString_Binary`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Foundations/Data/BitString/Binary.lean

/-
Copyright (c) 2026 Samuel Schlesinger, Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Renfei Zhou
-/

module
-- upstream: candidate

public import Batteries.Data.Nat.Basic
public import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_BitString_Basic
public import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_BitString_Counter
public import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_BitString_List_Binary
public import Batteries.Tactic.Lint.Basic
public import Mathlib.Init
public import Mathlib.Tactic.Common
public import Definitions.Def_Cslib_254e30e_Tactic_GrindAttrs
public import Mathlib.Data.List.OfFn

/- Prove2me definition bundle for `Complexity.Foundations.Data.BitString.Binary` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Bridges between `BitString.equivFin` and binary numeral views

`Cslib.BitString.equivFin n` numbers `n`-bit strings `Fin n → Bool` with `0` as the least
significant coordinate. This module connects `equivFin n` to the list-based numeral views
`Cslib.BitString.lsbValue` (least significant bit first) and `Cslib.BitString.binaryValue` (most
significant bit first), as well as `Nat.ofBits` and `Nat.testBit`, without adding a
`BitString.Basic` dependency to the list-level modules `BitString.Counter` or
`BitString.List.Binary`.

## Main results

* `Cslib.BitString.val_equivFin_eq_ofBits`: `equivFin` agrees with `Nat.ofBits`.
* `Cslib.BitString.equivFin_symm_apply`: the `i`-th bit of `(equivFin n).symm k` is
  `(k : ℕ).testBit i`.
* `Cslib.BitString.lsbValue_eq_binaryValue_reverse`: little-endian digits are the reversed
  big-endian ones.
* `Cslib.BitString.lsbValue_ofFn`: reading the bits of an `n`-bit word in order gives its number in
  `equivFin n`.
* `Cslib.BitString.binaryValue_reverse_ofFn`: reading the reversed list of bits of an `n`-bit word
  gives its number in `equivFin n`.
* `Cslib.BitString.lsbValue_lowBits`: reading `lowBits n x` with `lsbValue` recovers `x < 2 ^ n`.
* `Cslib.BitString.lowBits_lsbValue`: re-encoding `lsbValue w` with `lowBits` recovers `w`.
* `Cslib.BitString.val_equivFin_add`: addition in `BitString n` is bitwise XOR (`^^^`) on
  `equivFin n` coordinates.
-/

@[expose] public section

namespace Cslib.BitString

/-- `equivFin` agrees with `Nat.ofBits` on `n`-bit words. -/
theorem val_equivFin_eq_ofBits {n : ℕ} (x : BitString n) : (equivFin n x : ℕ) = Nat.ofBits x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h := val_equivFin_cons (x 0) (Fin.tail x)
    rw [Fin.cons_self_tail] at h
    rw [h, Nat.ofBits, Fin.foldr_succ, ← Nat.ofBits, ih (Fin.tail x), Nat.add_comm]
    rfl

/-- The `i`-th bit of `(equivFin n).symm k` is the `i`-th binary digit of `k`. -/
@[simp] theorem equivFin_symm_apply {n : ℕ} (k : Fin (2 ^ n)) (i : Fin n) :
    (equivFin n).symm k i = (k : ℕ).testBit i := by
  have hfin (x : Fin 2) : finTwoEquiv x = decide ((x : ℕ) = 1) := by
    rcases x with ⟨_ | _ | _, h⟩ <;> rfl
  rw [Nat.testBit_eq_decide_div_mod_eq]
  simp only [equivFin, Equiv.symm_trans_apply, Equiv.arrowCongr_symm, Equiv.refl_symm,
    Equiv.symm_symm, Equiv.arrowCongr_apply, Function.comp_apply, Equiv.refl_apply, hfin]
  rfl

/-- Reading the bits of an `n`-bit word in order gives its number in `equivFin n`. -/
theorem lsbValue_ofFn {n : ℕ} (x : BitString n) : lsbValue (List.ofFn x) = equivFin n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ, lsbValue, ih]
    have h := val_equivFin_cons (x 0) (Fin.tail x)
    rw [Fin.cons_self_tail] at h
    exact h.symm

/-- Reading the bits of an input, least significant first, gives its number in the order of
`BitString.equivFin`. -/
theorem binaryValue_reverse_ofFn {n : ℕ} (y : BitString n) :
    binaryValue (List.ofFn y).reverse = equivFin n y := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ, List.reverse_cons, binaryValue_snoc, ih fun i => y i.succ]
    have h := val_equivFin_cons (y 0) (Fin.tail y)
    rw [Fin.cons_self_tail] at h
    rw [h, Nat.add_comm]
    rfl

/-- Reading little-endian digits (`lsbValue`) is reading the reversed digits most significant
first (`binaryValue`). -/
theorem lsbValue_eq_binaryValue_reverse (w : List Bool) : lsbValue w = binaryValue w.reverse := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    rw [lsbValue, List.reverse_cons, binaryValue_snoc, ih]
    omega

/-- The fixed-width word `lowBits n k` equals the bits of `(equivFin n).symm k`. -/
theorem lowBits_eq_ofFn_equivFin_symm (n : ℕ) (k : Fin (2 ^ n)) :
    lowBits n (k : ℕ) = List.ofFn ((equivFin n).symm k) := by
  rw [lowBits_eq_ofFn]
  congr 1
  funext i
  exact (equivFin_symm_apply k i).symm

/-- For any `x < 2 ^ n`, reading `lowBits n x` with `lsbValue` recovers `x`. -/
@[simp]
theorem lsbValue_lowBits {n : ℕ} {x : ℕ} (hx : x < 2 ^ n) :
    lsbValue (lowBits n x) = x := by
  have := lsbValue_ofFn ((equivFin n).symm ⟨x, hx⟩)
  rw [← lowBits_eq_ofFn_equivFin_symm n ⟨x, hx⟩] at this
  simpa using this

/-- Converting a bit word to a natural with `lsbValue` and re-encoding with `lowBits` of the same
length recovers the original word. -/
@[simp]
theorem lowBits_lsbValue (w : List Bool) : lowBits w.length (lsbValue w) = w := by
  refine lsbValue_injective (by simp) ?_
  exact lsbValue_lowBits (lsbValue_lt w)

/-- Addition in `BitString n` is bitwise XOR (`^^^`) on `equivFin n` coordinates. -/
theorem val_equivFin_add {n : ℕ} (a b : BitString n) :
    (equivFin n (a + b)).val = (equivFin n a).val ^^^ (equivFin n b).val := by
  let ka := equivFin n a
  let kb := equivFin n b
  let k : Fin (2 ^ n) := ⟨ka.val ^^^ kb.val, Nat.xor_lt_two_pow ka.isLt kb.isLt⟩
  have hsymm : (equivFin n).symm k = a + b := by
    ext i
    rw [equivFin_symm_apply, show (k : ℕ) = ka.val ^^^ kb.val from rfl,
      Nat.testBit_xor, ← equivFin_symm_apply ka i,
      ← equivFin_symm_apply kb i, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rfl
  have hk : equivFin n (a + b) = k := by
    rw [← hsymm, Equiv.apply_symm_apply]
  exact congrArg Fin.val hk

end Cslib.BitString


