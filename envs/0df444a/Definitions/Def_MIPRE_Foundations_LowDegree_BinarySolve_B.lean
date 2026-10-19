-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve_B
-- name    : MIPRE_Foundations_LowDegree_BinarySolve_B
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:46:45.973992+00:00
-- url     : https://prove2.me/theorems/c6ba7845-47b7-43c8-8839-da6fec4aef82
-- title:
--   Definitions of BinarySolve (addendum): Solving binary linear systems with certified elimination
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.BinarySolve` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Solving binary linear systems with certified elimination
--
--   This bundle **adds** the declarations below to the already published bundle `MIPRE_Foundations_LowDegree_BinarySolve` of the same module, which the new statements of this upload need and the earlier bundle left out.
--
--   **Definitions** (2): `MIPRE.LowDegree.BinaryLinear.basisSolveProg` (Construct a basis and solve, all within one ambient polynomial-time program.); `MIPRE.LowDegree.BinaryLinear.solveBitsProg` (Solve using a supplied pivot basis; the certificate width is unary.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.BinarySolve` (`MIPRE/Foundations/LowDegree/BinarySolve.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 26 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinarySolve.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinarySolve.lean (delta bundle: declarations the new statements need that the published bundle Def_MIPRE_Foundations_LowDegree_BinarySolve does not carry);
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasis
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_IsPivotBasis_eq_zero_of_pivots_zero
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_typedBasis_span

/-! # Solving binary linear systems with certified elimination -/

namespace MIPRE.LowDegree.BinaryLinear

open Cost Cost.PolyTimeFun

variable {n t : ℕ}

/-- Solve using a supplied pivot basis; the certificate width is unary. -/
noncomputable def solveBitsProg : PolyTimeFun (Unary × List RawPivot × BitStr) BitStr :=
  snd.comp (reduceRowsProg.comp ((fst.comp snd).pair
    ((snd.comp snd).pair (replicate.comp (fst.pair (const false))))))

/-- Construct a basis and solve, all within one ambient polynomial-time program. -/
noncomputable def basisSolveProg : PolyTimeFun (Unary × List RawRow × BitStr) BitStr :=
  solveBitsProg.comp (fst.pair ((basisRowsProg.comp (fst.comp snd)).pair (snd.comp snd)))

end MIPRE.LowDegree.BinaryLinear


