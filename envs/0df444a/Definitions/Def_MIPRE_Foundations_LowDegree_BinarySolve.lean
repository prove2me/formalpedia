-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve
-- name    : MIPRE_Foundations_LowDegree_BinarySolve
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:20:38.134987+00:00
-- url     : https://prove2.me/theorems/ebd0e853-e433-41b4-861b-35eca6434526
-- title:
--   Definitions of BinarySolve: Solving binary linear systems with certified elimination
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.BinarySolve` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Solving binary linear systems with certified elimination
--
--   **Definitions** (1): `MIPRE.LowDegree.BinaryLinear.vectorValue`.
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `pivotSpan_nil`, `vectorValue_vectorBits`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.BinarySolve` (`MIPRE/Foundations/LowDegree/BinarySolve.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 24 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinarySolve.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinarySolve.lean (definition bundle: declarations the uploaded statements rest on);
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
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_getD_vectorBits

/-! # Solving binary linear systems with certified elimination -/

namespace MIPRE.LowDegree.BinaryLinear

open Cost Cost.PolyTimeFun

variable {n t : ℕ}

@[simp] theorem pivotSpan_nil : pivotSpan ([] : List (Pivot n t)) = ⊥ := by
  simp [pivotSpan]

def vectorValue (n : ℕ) (v : BitStr) : Fin n → ZMod 2 := fun i => ofBool (v.getD i false)

@[simp] theorem vectorValue_vectorBits (v : Fin n → ZMod 2) :
    vectorValue n (vectorBits v) = v := by
  funext i
  rw [vectorValue, getD_vectorBits, ofBool_bit]

end MIPRE.LowDegree.BinaryLinear


