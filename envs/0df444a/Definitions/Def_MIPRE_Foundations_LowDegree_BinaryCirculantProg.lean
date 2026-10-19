-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCirculantProg
-- name    : MIPRE_Foundations_LowDegree_BinaryCirculantProg
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:22:03.976069+00:00
-- url     : https://prove2.me/theorems/18da197b-715f-441e-afc4-236ff5f746d3
-- title:
--   Definitions of BinaryCirculantProg: Executable circulant matrices and their inverse square roots
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.BinaryCirculantProg` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Executable circulant matrices and their inverse square roots
--
--   **Definitions** (5): `MIPRE.LowDegree.BinaryLinear.circulantBitsProg` (Print a circulant from its first column.); `MIPRE.LowDegree.BinaryLinear.rotateLeftBits`; `MIPRE.LowDegree.BinaryLinear.rotateLeftBitsProg`; `MIPRE.LowDegree.BinaryLinear.rotateRightBits`; `MIPRE.LowDegree.BinaryLinear.rotateRightBitsProg`.
--
--   **Embedded lemmas** (3): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `esize_rotateLeftBits`, `esize_rotateRightBits`, `rotateRightBitsProg_iterate_size`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.BinaryCirculantProg` (`MIPRE/Foundations/LowDegree/BinaryCirculantProg.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 27 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryCirculantProg.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryCirculantProg.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Rotate
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.LinearAlgebra.Matrix.ToLin
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasisProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasis
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve
import Definitions.Def_MIPRE_Foundations_Cost_Iterates
import Theorems.Thm_MIPRE_Cost_esize_list_reverse

/-! # Executable circulant matrices and their inverse square roots -/

namespace MIPRE.LowDegree.BinaryLinear

open Cost Cost.PolyTimeFun

def rotateLeftBits : BitStr → BitStr
  | [] => []
  | a :: l => l ++ [a]

def rotateRightBits (l : BitStr) : BitStr := (rotateLeftBits l.reverse).reverse

theorem esize_rotateLeftBits (l : BitStr) : esize (rotateLeftBits l) = esize l := by
  cases l with
  | nil => rfl
  | cons a l =>
    have h := esize_list_append l [a]
    simp only [rotateLeftBits, esize_list_cons, esize_list_nil] at *
    omega

theorem esize_rotateRightBits (l : BitStr) : esize (rotateRightBits l) = esize l := by
  rw [rotateRightBits, esize_list_reverse, esize_rotateLeftBits, esize_list_reverse]

noncomputable def rotateLeftBitsProg : PolyTimeFun BitStr BitStr :=
  congr ((casesList (const [])
    (append.comp ((snd.comp snd).pair (cons (fst.comp snd) (const []))))).comp
      ((const ()).pair (PolyTimeFun.id _))) rotateLeftBits (by intro l; cases l <;> rfl)

noncomputable def rotateRightBitsProg : PolyTimeFun BitStr BitStr :=
  reverse.comp (rotateLeftBitsProg.comp reverse)

theorem rotateRightBitsProg_iterate_size (n : ℕ) (l : BitStr) :
    esize ((rotateRightBitsProg : BitStr → BitStr)^[n] l) ≤ Polynomial.X.eval (esize l) := by
  have hf : (rotateRightBitsProg : BitStr → BitStr) = rotateRightBits := by funext l; rfl
  rw [hf, Polynomial.eval_X]
  induction n with
  | zero => exact le_rfl
  | succ n ih => rw [Function.iterate_succ_apply', esize_rotateRightBits]; exact ih

/-- Print a circulant from its first column. The size and all iteration counts come from the input. -/
noncomputable def circulantBitsProg : PolyTimeFun BitStr (List BitStr) :=
  let columns := (recordIteratesProg rotateRightBitsProg Polynomial.X
    rotateRightBitsProg_iterate_size).comp (length.pair (PolyTimeFun.id _))
  transposeBitsProg.comp (length.pair columns)

end MIPRE.LowDegree.BinaryLinear


