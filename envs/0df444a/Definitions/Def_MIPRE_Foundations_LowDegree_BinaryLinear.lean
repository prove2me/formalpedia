-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_BinaryLinear
-- name    : MIPRE_Foundations_LowDegree_BinaryLinear
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:57:06.013593+00:00
-- url     : https://prove2.me/theorems/f04ffee7-23db-41dc-9748-61b045539b9e
-- title:
--   Definitions of BinaryLinear: Executable binary vector and matrix arithmetic
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.BinaryLinear` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Executable binary vector and matrix arithmetic
--
--   **Definitions** (14): `MIPRE.LowDegree.BinaryLinear.applyBits` (A matrix is represented by its rows.); `MIPRE.LowDegree.BinaryLinear.applyBitsProg` (Binary matrix application is polynomial-time on arbitrary raw row lists.); `MIPRE.LowDegree.BinaryLinear.bit` (Canonical binary scalar coordinates.); `MIPRE.LowDegree.BinaryLinear.dotBits`; `MIPRE.LowDegree.BinaryLinear.dotBitsProg` (The parity dot product is one uniform ambient program.); `MIPRE.LowDegree.BinaryLinear.dotStep`; `MIPRE.LowDegree.BinaryLinear.matrixBits`; `MIPRE.LowDegree.BinaryLinear.mulBits` (A rectangular matrix product with an explicit output width.); `MIPRE.LowDegree.BinaryLinear.mulBitsProg` (Matrix multiplication is globally polynomial-time in its raw inputs.); `MIPRE.LowDegree.BinaryLinear.transposeBits` (The number of columns is explicit; short raw rows are padded with zero.); `MIPRE.LowDegree.BinaryLinear.transposeBitsProg` (Transposition is polynomial-time in the rows and the unary column count.); `MIPRE.LowDegree.BinaryLinear.vectorBits`; `_private.MIPRE.Foundations.LowDegree.BinaryLinear.0.MIPRE.LowDegree.BinaryLinear.columnProg`; `_private.MIPRE.Foundations.LowDegree.BinaryLinear.0.MIPRE.LowDegree.BinaryLinear.dotStepProg`.
--
--   **Embedded lemmas** (6): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `applyBitsProg_apply`, `bit_ofBool`, `dotBitsProg_apply`, `mulBitsProg_apply`, `ofBool_bit`, `transposeBitsProg_apply`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.BinaryLinear` (`MIPRE/Foundations/LowDegree/BinaryLinear.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 19 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryLinear.lean; blueprint lem:effective-binary-linear-algebra

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryLinear.lean (definition bundle: declarations the uploaded statements rest on);
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

/-! # Executable binary vector and matrix arithmetic -/

namespace MIPRE.LowDegree.BinaryLinear

open Cost Cost.PolyTimeFun

/-- Canonical binary scalar coordinates. -/
def bit (x : ZMod 2) : Bool := decide (x = 1)

@[simp] theorem ofBool_bit (x : ZMod 2) : ofBool (bit x) = x := by
  revert x
  decide

@[simp] theorem bit_ofBool (x : Bool) : bit (ofBool x) = x := by cases x <;> decide

def vectorBits {n : ℕ} (v : Fin n → ZMod 2) : BitStr := List.ofFn (fun i => bit (v i))

def matrixBits {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) : List BitStr :=
  List.ofFn (fun i => vectorBits (A i))

def dotStep (b : Bool) (p : Bool × Bool) : Bool := b ^^ (p.1 && p.2)

def dotBits (a b : BitStr) : Bool := (a.zip b).foldl dotStep false

/-- A matrix is represented by its rows. -/
def applyBits (A : List BitStr) (v : BitStr) : BitStr := A.map (fun r => dotBits r v)

noncomputable def dotStepProg : PolyTimeFun (Bool × Bool × Bool) Bool :=
  let t := ite (fst.comp snd) (snd.comp snd) (const false)
  congr (ite fst (ite t (const false) (const true)) t)
    (fun p => dotStep p.1 p.2) (by
      rintro ⟨b, c, d⟩
      cases b <;> cases c <;> cases d <;> rfl)

/-- The parity dot product is one uniform ambient program. -/
noncomputable def dotBitsProg : PolyTimeFun (BitStr × BitStr) Bool :=
  let scan := foldlAdd dotStepProg 3 (by
    intro s a
    have hb : esize (dotStepProg (s, a)) ≤ 3 := by
      generalize dotStepProg (s, a) = b
      cases b <;> decide
    simp only [Polynomial.eval_ofNat]
    omega)
  congr (scan.comp (zip.pair (const false))) (fun p => dotBits p.1 p.2)
    (by intro p; rfl)

@[simp] theorem dotBitsProg_apply (a b : BitStr) : dotBitsProg (a, b) = dotBits a b := rfl

/-- Binary matrix application is polynomial-time on arbitrary raw row lists. -/
noncomputable def applyBitsProg : PolyTimeFun (List BitStr × BitStr) BitStr :=
  congr (mapWith dotBitsProg) (fun p => applyBits p.1 p.2) (by intro p; rfl)

@[simp] theorem applyBitsProg_apply (A : List BitStr) (v : BitStr) :
    applyBitsProg (A, v) = applyBits A v := rfl

/-- The number of columns is explicit; short raw rows are padded with zero. -/
def transposeBits (n : ℕ) (A : List BitStr) : List BitStr :=
  (List.range n).map (fun j => A.map (fun r => r.getD j false))

/-- A rectangular matrix product with an explicit output width. -/
def mulBits (n : ℕ) (A B : List BitStr) : List BitStr :=
  A.map (fun r => applyBits (transposeBits n B) r)

noncomputable def columnProg : PolyTimeFun (ℕ × List BitStr) BitStr :=
  (mapWith ((SAT.ArrayProg.getD false).comp (snd.pair fst))).comp (snd.pair fst)

/-- Transposition is polynomial-time in the rows and the unary column count. -/
noncomputable def transposeBitsProg : PolyTimeFun (Unary × List BitStr) (List BitStr) :=
  congr ((mapWith columnProg).comp
    ((SAT.range'P.comp ((const 0).pair fst)).pair snd))
    (fun p => transposeBits p.1.length p.2) (by
      intro p
      simp only [comp_apply, mapWith_apply, pair_apply, fst_apply, snd_apply,
        SAT.range'P_apply, const_apply]
      change (List.range' 0 p.1.length).map (fun j => p.2.map (fun r => r.getD j false)) = _
      rw [← List.range_eq_range']
      rfl)

@[simp] theorem transposeBitsProg_apply (u : Unary) (A : List BitStr) :
    transposeBitsProg (u, A) = transposeBits u.length A := rfl

/-- Matrix multiplication is globally polynomial-time in its raw inputs. -/
noncomputable def mulBitsProg :
    PolyTimeFun (Unary × List BitStr × List BitStr) (List BitStr) :=
  congr ((mapWith (applyBitsProg.comp (snd.pair fst))).comp
    ((fst.comp snd).pair (transposeBitsProg.comp (fst.pair (snd.comp snd)))))
    (fun p => mulBits p.1.length p.2.1 p.2.2) (by intro p; rfl)

@[simp] theorem mulBitsProg_apply (u : Unary) (A B : List BitStr) :
    mulBitsProg (u, A, B) = mulBits u.length A B := rfl

end MIPRE.LowDegree.BinaryLinear


