-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasisProg
-- name    : MIPRE_Foundations_LowDegree_BinaryBasisProg
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:02:08.702144+00:00
-- url     : https://prove2.me/theorems/dab54424-2c5e-4416-be8b-969ae4616a85
-- title:
--   Definitions of BinaryBasisProg: Uniform construction of a binary pivot basis
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.BinaryBasisProg` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Uniform construction of a binary pivot basis
--
--   **Definitions** (7): `MIPRE.LowDegree.BinaryLinear.basisRows` (The complete forward elimination scan.); `MIPRE.LowDegree.BinaryLinear.basisRowsProg` (Uniform polynomial-time construction of a pivot basis with coefficient certificates.); `MIPRE.LowDegree.BinaryLinear.firstOne` (First set bit, or the list length if the vector is zero.); `MIPRE.LowDegree.BinaryLinear.firstOneProg` (Finding a pivot scans the vector, without enumerating its binary magnitude.); `MIPRE.LowDegree.BinaryLinear.insertRow` (Reduce the candidate, then append it only when its remainder has a pivot.); `MIPRE.LowDegree.BinaryLinear.insertRowProg`; `_private.MIPRE.Foundations.LowDegree.BinaryBasisProg.0.MIPRE.LowDegree.BinaryLinear.firstOneStep`.
--
--   **Embedded lemmas** (6): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `basisRowsProg_apply`, `firstOneProg_apply`, `firstOne_le`, `insertRowProg_apply`, `insertRow_size`, `firstOne_fold`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.BinaryBasisProg` (`MIPRE/Foundations/LowDegree/BinaryBasisProg.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 21 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryBasisProg.lean; blueprint lem:effective-binary-linear-algebra

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryBasisProg.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.List.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryLinear
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryElimination

/-! # Uniform construction of a binary pivot basis -/

namespace MIPRE.LowDegree.BinaryLinear

open Cost Cost.PolyTimeFun Polynomial

/-- First set bit, or the list length if the vector is zero. -/
def firstOne (v : BitStr) : ℕ := v.findIdx id

theorem firstOne_le (v : BitStr) : firstOne v ≤ v.length := List.findIdx_le_length

noncomputable def firstOneStep : PolyTimeFun (ℕ × Bool) ℕ :=
  ite snd (const 0) (inc.comp fst)

theorem firstOne_fold (v : BitStr) :
    v.reverse.foldl firstOneStep.step 0 = firstOne v := by
  rw [List.foldl_reverse]
  induction v with
  | nil => rfl
  | cons b v ih =>
    change (if b then 0 else v.foldr (fun b n => firstOneStep (n, b)) 0 + 1) = _
    rw [ih]
    cases b <;> simp [firstOne, List.findIdx_cons]

/-- Finding a pivot scans the vector, without enumerating its binary magnitude. -/
noncomputable def firstOneProg : PolyTimeFun BitStr ℕ :=
  let scan := foldlAdd firstOneStep 4 (by
    intro n b
    change esize (if b then 0 else n + 1) ≤ _
    cases b
    · simpa only [Bool.false_eq_true, if_false, Polynomial.eval_ofNat] using esize_succ_le n
    · have hn := esize_pos n
      change 1 ≤ esize n + _
      omega)
  congr (scan.comp (reverse.pair (const 0))) firstOne firstOne_fold

@[simp] theorem firstOneProg_apply (v : BitStr) : firstOneProg v = firstOne v := rfl

/-- Reduce the candidate, then append it only when its remainder has a pivot. -/
def insertRow (b : List RawPivot) (r : RawRow) : List RawPivot :=
  let s := reduceRows b r
  let j := firstOne s.1
  if s.1.getD j false then b ++ [(j, s)] else b

noncomputable def insertRowProg : PolyTimeFun (List RawPivot × RawRow) (List RawPivot) :=
  let prepared : PolyTimeFun (List RawPivot × RawRow) (List RawPivot × RawRow) :=
    fst.pair reduceRowsProg
  let value : PolyTimeFun (List RawPivot × RawRow) BitStr := fst.comp snd
  let j := firstOneProg.comp value
  let test := (SAT.ArrayProg.getD false).comp (j.pair value)
  let row := j.pair snd
  congr ((ite test (append.comp (fst.pair (cons row (const [])))) fst).comp prepared)
    (fun p => insertRow p.1 p.2) (by intro p; rfl)

@[simp] theorem insertRowProg_apply (b : List RawPivot) (r : RawRow) :
    insertRowProg (b, r) = insertRow b r := rfl

/-- The new row's encoded size is bounded by the input row, independent of the
existing basis. This additive bound is the polynomial fold invariant. -/
theorem insertRow_size (b : List RawPivot) (r : RawRow) :
    esize (insertRow b r) ≤ esize b + 20 * esize r + 20 := by
  obtain ⟨hv, hw⟩ := reduceRows_width b r
  have hj := firstOne_le (reduceRows b r).1
  have hjn : Nat.size (firstOne (reduceRows b r).1) ≤ firstOne (reduceRows b r).1 :=
    Nat.size_le.mpr (Nat.lt_two_pow_self)
  have hjc := esize_nat_le (firstOne (reduceRows b r).1)
  have hvc := esize_bitStr_le (reduceRows b r).1
  have hwc := esize_bitStr_le (reduceRows b r).2
  have hv0 := length_le_esize_list r.1
  have hw0 := length_le_esize_list r.2
  have hr : esize r = esize r.1 + esize r.2 + 1 := rfl
  unfold insertRow
  dsimp only
  split
  · have he := esize_list_append b [(firstOne (reduceRows b r).1, reduceRows b r)]
    simp only [esize_list_cons, esize_list_nil, esize_prod] at he
    have hs : esize (reduceRows b r) =
        esize (reduceRows b r).1 + esize (reduceRows b r).2 + 1 := rfl
    omega
  · omega

/-- The complete forward elimination scan. -/
def basisRows (rows : List RawRow) : List RawPivot := rows.foldl insertRow []

/-- Uniform polynomial-time construction of a pivot basis with coefficient certificates. -/
noncomputable def basisRowsProg : PolyTimeFun (List RawRow) (List RawPivot) :=
  let scan := foldlAdd insertRowProg (20 * X + 20) (by
    intro b r
    simpa only [insertRowProg_apply, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_ofNat, Polynomial.eval_X, Nat.add_assoc] using insertRow_size b r)
  congr (scan.comp ((PolyTimeFun.id _).pair (const []))) basisRows (by intro rows; rfl)

@[simp] theorem basisRowsProg_apply (rows : List RawRow) : basisRowsProg rows = basisRows rows := rfl

end MIPRE.LowDegree.BinaryLinear


