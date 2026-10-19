-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve_B
-- name    : MIPRE_Foundations_LowDegree_BinaryMatrixSolve_B
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:47:20.598993+00:00
-- url     : https://prove2.me/theorems/d31982a8-6c5e-483a-82be-5139784df204
-- title:
--   Definitions of BinaryMatrixSolve (addendum): A uniform solver for binary matrices
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.BinaryMatrixSolve` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # A uniform solver for binary matrices
--
--   This bundle **adds** the declarations below to the already published bundle `MIPRE_Foundations_LowDegree_BinaryMatrixSolve` of the same module, which the new statements of this upload need and the earlier bundle left out.
--
--   **Definitions** (1): `MIPRE.LowDegree.BinaryLinear.matrixSolveProg` (The output width is unary; matrix rows and the right-hand side are raw bits.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.BinaryMatrixSolve` (`MIPRE/Foundations/LowDegree/BinaryMatrixSolve.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 28 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryMatrixSolve.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryMatrixSolve.lean (delta bundle: declarations the new statements need that the published bundle Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve does not carry);
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasis
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_coordinateRows_matrixBits
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_xorBits_vectorBits

/-! # A uniform solver for binary matrices -/

namespace MIPRE.LowDegree.BinaryLinear

open Cost Cost.PolyTimeFun

/-- The output width is unary; matrix rows and the right-hand side are raw bits. -/
noncomputable def matrixSolveProg : PolyTimeFun (Unary × List BitStr × BitStr) BitStr :=
  basisSolveProg.comp (fst.pair
    ((coordinateRowsProg.comp (transposeBitsProg.comp (fst.pair (fst.comp snd)))).pair
      (snd.comp snd)))

end MIPRE.LowDegree.BinaryLinear


