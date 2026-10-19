-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon
-- name    : MIPRE_Foundations_LowDegree_BinaryEchelon
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:02:37.377971+00:00
-- url     : https://prove2.me/theorems/45777a8d-f759-4766-8d46-511c6cbc49ff
-- title:
--   Definitions of BinaryEchelon: Triangular pivot bases and certified binary reduction
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.BinaryEchelon` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Triangular pivot bases and certified binary reduction
--
--   **Definitions** (1): `MIPRE.LowDegree.BinaryLinear.IsPivotBasis` (In insertion order, each row has pivot one and every later row vanishes at that pivot.).
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `instFactPrimeOfNatNat_mIPRE`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.BinaryEchelon` (`MIPRE/Foundations/LowDegree/BinaryEchelon.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 21 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryEchelon.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryEchelon.lean (definition bundle: declarations the uploaded statements rest on);
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

/-! # Triangular pivot bases and certified binary reduction -/

namespace MIPRE.LowDegree.BinaryLinear

variable {n t : ℕ}

local instance instFactPrimeOfNatNat_mIPRE : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- In insertion order, each row has pivot one and every later row vanishes
at that pivot. Pivots need not be numerically ordered. -/
def IsPivotBasis : List (Pivot n t) → Prop
  | [] => True
  | p :: b => p.2.1 p.1 = 1 ∧ (∀ q ∈ b, q.2.1 p.1 = 0) ∧ IsPivotBasis b

end MIPRE.LowDegree.BinaryLinear


