-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon_B
-- name    : MIPRE_Foundations_LowDegree_BinaryEchelon_B
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:20:18.402+00:00
-- url     : https://prove2.me/theorems/44c27432-3fd4-41ec-8c29-3fe2ea636f39
-- title:
--   Definitions of BinaryEchelon (addendum): Triangular pivot bases and certified binary reduction
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.BinaryEchelon` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Triangular pivot bases and certified binary reduction
--
--   This bundle **adds** the declarations below to the already published bundle `MIPRE_Foundations_LowDegree_BinaryEchelon` of the same module, which the new statements of this upload need and the earlier bundle left out.
--
--   **Definitions** (1): `MIPRE.LowDegree.BinaryLinear.pivotVectors` (The vector family extracted in insertion order.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.BinaryEchelon` (`MIPRE/Foundations/LowDegree/BinaryEchelon.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 22 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryEchelon.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryEchelon.lean (delta bundle: declarations the new statements need that the published bundle Def_MIPRE_Foundations_LowDegree_BinaryEchelon does not carry);
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_binary_eq_zero_or_one

/-! # Triangular pivot bases and certified binary reduction -/

namespace MIPRE.LowDegree.BinaryLinear

variable {n t : ℕ}

/-- The vector family extracted in insertion order. -/
def pivotVectors (b : List (Pivot n t)) : Fin b.length → (Fin n → ZMod 2) :=
  fun i => (b[i]).2.1

end MIPRE.LowDegree.BinaryLinear


