-- Prove2me | Definitions.Def_MIPRE_Foundations_Cost_BinaryCompare
-- name    : MIPRE_Foundations_Cost_BinaryCompare
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:46:18.073473+00:00
-- url     : https://prove2.me/theorems/ffb2f40d-6f3c-4251-a6b9-fc10cca00039
-- title:
--   Polynomial-time comparison of binary natural numbers by a bitwise scan
-- statement:
--   Let `BitStr = List Bool` be the binary numerals, least significant bit first, `bitsVal l = l.foldr Nat.bit 0` the value of a string, and `PolyTimeFun α β` the polynomial-time functions of the ambient model (a function, a closed program, a polynomial bound in the encoded size and a correctness proof), with `foldlAdd`, `append`, `replicate`, `length`, `zip`, `ite`, `const`, `fst`, `snd` and `ofEncodeEq` from earlier bundles.
--
--   The private step `compareStep (acc : Bool) (p : Bool × Bool) : Bool` is `if p.1 then (if p.2 then acc else false) else (if p.2 then true else acc)`: scanning the two strings from the least significant bit, the accumulator records whether the prefix read so far has first value at most second value, and a more significant position overrides it unless its two bits agree. The private `compareStepProg : PolyTimeFun (Bool × (Bool × Bool)) Bool` is the same step as a program (by `ite`). `MIPRE.Cost.PolyTimeFun.leBits : PolyTimeFun (BitStr × BitStr) Bool` pads each string with `false` bits to the length of the other, zips them, and folds `compareStepProg` from `true`; `MIPRE.Cost.PolyTimeFun.leNat : PolyTimeFun (ℕ × ℕ) Bool` is `leBits` on the bits of the two numbers. Their values are
--
--   $$\mathrm{leBits}\,(a, b) = \mathrm{decide}\,(\mathrm{bitsVal}\ a \le \mathrm{bitsVal}\ b), \qquad \mathrm{leNat}\,(m, n) = \mathrm{decide}\,(m \le n).$$
--
--   Lemmas: `compare_fold` (for strings of equal length, the fold from `acc` is `true` iff `bitsVal a < bitsVal b`, or `bitsVal a = bitsVal b` and `acc = true`), `bitsVal_append_false` (padding with `false` bits preserves the value), `esize_bool_le` (a Boolean encodes with size at most $3$), `compareStepProg_apply`, `leBits_apply` and `leNat_apply`.
--
--   The comparison scans the coefficient bits directly and never expands a binary number to unary, so its cost is polynomial in the encodings even for values far larger than the work space.
--
--   **Formalization Note**. `leBits` compares arbitrary strings, leading (most significant) zero bits allowed, which is why padding is harmless and why it is specified through `bitsVal`. The bits of a number are read by `ofEncodeEq Nat.bits`, whose program is `var 0`. The step function and its program are private declarations of the module and carry no docstrings. The definitions carrying a `Polynomial ℕ` are noncomputable.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/BinaryCompare.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/BinaryCompare.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Reader

/-!
# Polynomial-time comparison of binary natural numbers

The comparison scans coefficient bits directly, padding only by the supplied
bit-string lengths. It never expands a binary number to unary.
-/

namespace MIPRE.Cost

open Polynomial PolyTimeFun

def compareStep (acc : Bool) (p : Bool × Bool) : Bool :=
  if p.1 then (if p.2 then acc else false) else (if p.2 then true else acc)

theorem compare_fold (a b : BitStr) (acc : Bool) (h : a.length = b.length) :
    (a.zip b).foldl compareStep acc = true ↔
      bitsVal a < bitsVal b ∨ (bitsVal a = bitsVal b ∧ acc = true) := by
  induction a generalizing b acc with
  | nil =>
    have hb : b = [] := List.length_eq_zero_iff.mp h.symm
    subst b
    simp
  | cons a as ih =>
    cases b with
    | nil => simp at h
    | cons b bs =>
      simp only [List.zip_cons_cons, List.foldl_cons]
      rw [ih bs _ (by simpa using h)]
      cases a <;> cases b <;> cases acc <;>
        simp [compareStep, bitsVal_cons, Nat.bit] <;> omega

theorem bitsVal_append_false (a : BitStr) (n : ℕ) :
    bitsVal (a ++ List.replicate n false) = bitsVal a := by
  induction a with
  | nil =>
    induction n with
    | zero => rfl
    | succ n ih => simpa [List.replicate_succ, bitsVal_cons, Nat.bit] using ih
  | cons b a ih => simp only [List.cons_append, bitsVal_cons, ih]

theorem esize_bool_le (b : Bool) : esize b ≤ 3 := by cases b <;> decide

noncomputable def compareStepProg : PolyTimeFun (Bool × (Bool × Bool)) Bool :=
  ite (fst.comp snd) (ite (snd.comp snd) fst (const false))
    (ite (snd.comp snd) (const true) fst)

theorem compareStepProg_apply (b : Bool) (p : Bool × Bool) :
    compareStepProg (b, p) = compareStep b p := rfl

/-- Compare arbitrary little-endian strings, allowing leading zeroes. -/
noncomputable def PolyTimeFun.leBits : PolyTimeFun (BitStr × BitStr) Bool :=
  let scan := foldlAdd compareStepProg 3 (by
    intro s a
    have hb := esize_bool_le (compareStepProg (s, a))
    simp only [Polynomial.eval_ofNat]
    omega)
  let a : PolyTimeFun (BitStr × BitStr) BitStr :=
    append.comp (fst.pair (replicate.comp ((length.comp snd).pair (const false))))
  let b : PolyTimeFun (BitStr × BitStr) BitStr :=
    append.comp (snd.pair (replicate.comp ((length.comp fst).pair (const false))))
  congr (scan.comp ((zip.comp (a.pair b)).pair (const true)))
    (fun p => decide (bitsVal p.1 ≤ bitsVal p.2)) (by
      intro p
      simp only [scan, a, b, comp_apply, foldlAdd_apply, pair_apply, zip_apply,
        append_apply, fst_apply, snd_apply, replicate_apply, length_apply,
        length_unary, const_apply, compareStepProg_apply]
      apply Bool.eq_iff_iff.mpr
      rw [compare_fold _ _ true (by simp [Nat.add_comm])]
      simp only [bitsVal_append_false, and_true, decide_eq_true_eq]
      omega)

@[simp] theorem PolyTimeFun.leBits_apply (p : BitStr × BitStr) :
    leBits p = decide (bitsVal p.1 ≤ bitsVal p.2) := rfl

/-- Binary natural comparison, with a global polynomial cost in the encodings. -/
noncomputable def PolyTimeFun.leNat : PolyTimeFun (ℕ × ℕ) Bool :=
  let bits : PolyTimeFun ℕ BitStr := ofEncodeEq Nat.bits (fun _ => rfl)
  congr (leBits.comp ((bits.comp fst).pair (bits.comp snd)))
    (fun p => decide (p.1 ≤ p.2)) (by intro p; simp only [comp_apply, leBits_apply,
      pair_apply, bits, ofEncodeEq_apply, fst_apply, snd_apply, bitsVal_bits])

@[simp] theorem PolyTimeFun.leNat_apply (p : ℕ × ℕ) : leNat p = decide (p.1 ≤ p.2) := rfl

end MIPRE.Cost


