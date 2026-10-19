-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve
-- name    : MIPRE_Foundations_LowDegree_BinaryMatrixSolve
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:21:11.181295+00:00
-- url     : https://prove2.me/theorems/8738db2e-5121-418d-93ef-6f5789b5085e
-- title:
--   Definitions of BinaryMatrixSolve: A uniform solver for binary matrices
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.BinaryMatrixSolve` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # A uniform solver for binary matrices
--
--   **Definitions** (8): `MIPRE.LowDegree.BinaryLinear.addMatrixBitsProg` (Coordinatewise addition of binary matrices.); `MIPRE.LowDegree.BinaryLinear.columnRows`; `MIPRE.LowDegree.BinaryLinear.coordinateRows` (Attach the standard coordinate certificate to each supplied column.); `MIPRE.LowDegree.BinaryLinear.coordinateRowsProg`; `MIPRE.LowDegree.BinaryLinear.identityBits`; `MIPRE.LowDegree.BinaryLinear.identityBitsProg`; `MIPRE.LowDegree.BinaryLinear.unitBits`; `MIPRE.LowDegree.BinaryLinear.unitBitsProg`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.BinaryMatrixSolve` (`MIPRE/Foundations/LowDegree/BinaryMatrixSolve.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 25 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryMatrixSolve.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryMatrixSolve.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
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
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
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

/-! # A uniform solver for binary matrices -/

namespace MIPRE.LowDegree.BinaryLinear

open Cost Cost.PolyTimeFun

def unitBits (n j : ℕ) : BitStr := (List.range n).map (fun i => decide (i = j))

def identityBits (n : ℕ) : List BitStr := (List.range n).map (unitBits n)

noncomputable def unitBitsProg : PolyTimeFun (ℕ × Unary) BitStr :=
  congr ((mapWith SAT.ArrayProg.eqNat).comp
    ((SAT.range'P.comp ((const 0).pair snd)).pair fst))
    (fun p => unitBits p.2.length p.1) (by
      intro p
      simp only [comp_apply, pair_apply, mapWith_apply, SAT.ArrayProg.eqNat_apply,
        SAT.range'P_apply, fst_apply, snd_apply, const_apply, ← List.range_eq_range']
      rfl)

noncomputable def identityBitsProg : PolyTimeFun Unary (List BitStr) :=
  congr ((mapWith unitBitsProg).comp
    ((SAT.range'P.comp ((const 0).pair (PolyTimeFun.id _))).pair (PolyTimeFun.id _)))
    (fun u => identityBits u.length) (by
      intro u
      simp only [comp_apply, pair_apply, mapWith_apply, SAT.range'P_apply,
        fst_apply, snd_apply, id_apply, const_apply, ← List.range_eq_range']
      rfl)

/-- Attach the standard coordinate certificate to each supplied column. -/
def coordinateRows (columns : List BitStr) : List RawRow :=
  columns.zip (identityBits columns.length)

noncomputable def coordinateRowsProg : PolyTimeFun (List BitStr) (List RawRow) :=
  congr (zip.comp ((PolyTimeFun.id _).pair (identityBitsProg.comp length))) coordinateRows
    (by intro columns; change columns.zip (identityBits (unary columns.length).length) = _
        rw [length_unary]; rfl)

def columnRows {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) : List (Row m n) :=
  List.ofFn (fun j => (A.col j, Pi.single j 1))

/-- Coordinatewise addition of binary matrices. -/
noncomputable def addMatrixBitsProg : PolyTimeFun (List BitStr × List BitStr) (List BitStr) :=
  (map BinaryPolynomial.xorBitsProg).comp zip

end MIPRE.LowDegree.BinaryLinear


