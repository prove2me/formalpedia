-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasis
-- name    : MIPRE_Foundations_LowDegree_BinaryBasis
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:03:50.232737+00:00
-- url     : https://prove2.me/theorems/f3943b8f-0ee8-473c-9326-2d8c4299236e
-- title:
--   Definitions of BinaryBasis: Correctness of the effective binary basis construction
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.BinaryBasis` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Correctness of the effective binary basis construction
--
--   **Definitions** (4): `MIPRE.LowDegree.BinaryLinear.pivotSpan`; `MIPRE.LowDegree.BinaryLinear.rowSpan`; `MIPRE.LowDegree.BinaryLinear.typedBasis` (Forward elimination, with its vectors and coefficient certificates retained.); `MIPRE.LowDegree.BinaryLinear.typedInsert` (The program's pivot choice, applied to typed coordinate vectors.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.BinaryBasis` (`MIPRE/Foundations/LowDegree/BinaryBasis.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 23 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryBasis.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryBasis.lean (definition bundle: declarations the uploaded statements rest on);
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

/-! # Correctness of the effective binary basis construction -/

namespace MIPRE.LowDegree.BinaryLinear

variable {n t : ℕ}

/-- The program's pivot choice, applied to typed coordinate vectors. -/
def typedInsert (b : List (Pivot n t)) (r : Row n t) : List (Pivot n t) :=
  let s := typedReduce b r
  let j := firstOne (vectorBits s.1)
  if h : j < n then b ++ [(⟨j, h⟩, s)] else b

/-- Forward elimination, with its vectors and coefficient certificates retained. -/
def typedBasis (rows : List (Row n t)) : List (Pivot n t) := rows.foldl typedInsert []

def pivotSpan (b : List (Pivot n t)) : Submodule (ZMod 2) (Fin n → ZMod 2) :=
  Submodule.span (ZMod 2) {v | ∃ p ∈ b, p.2.1 = v}

def rowSpan (rows : List (Row n t)) : Submodule (ZMod 2) (Fin n → ZMod 2) :=
  Submodule.span (ZMod 2) {v | ∃ r ∈ rows, r.1 = v}

end MIPRE.LowDegree.BinaryLinear


