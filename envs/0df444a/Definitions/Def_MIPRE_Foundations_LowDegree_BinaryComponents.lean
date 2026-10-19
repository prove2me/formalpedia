-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponents
-- name    : MIPRE_Foundations_LowDegree_BinaryComponents
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:24:24.041765+00:00
-- url     : https://prove2.me/theorems/a8c7195a-3067-4816-b40a-dc4407063d2c
-- title:
--   Definitions of BinaryComponents: Primitive components computed by fixed-space separation
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.BinaryComponents` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Primitive components computed by fixed-space separation
--
--   **Definitions** (4): `MIPRE.LowDegree.BinaryLinear.nonzeroRow`; `MIPRE.LowDegree.BinaryLinear.splitBits` (One raw split uses cyclic multiplication and XOR, then omits zero vectors.); `MIPRE.LowDegree.BinaryLinear.splitBitsCapped` (Raw refinement is clipped to the unary dimension; on valid components this clip is inert.); `MIPRE.LowDegree.BinaryLinear.zeroRow` (Canonical zero of the same raw width.).
--
--   **Embedded lemmas** (3): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `instFactPrimeOfNatNat_mIPRE_2`, `nonzeroRow_zero`, `zeroRow_vectorBits`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.BinaryComponents` (`MIPRE/Foundations/LowDegree/BinaryComponents.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 32 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryComponents.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryComponents.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCirculantProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryKernel
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGroupAlgebra
import Definitions.Def_MIPRE_Foundations_LowDegree_FiniteReducedComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_IdempotentSplit

/-! # Primitive components computed by fixed-space separation -/

noncomputable section

namespace MIPRE.LowDegree.BinaryLinear

open Cost

local instance instFactPrimeOfNatNat_mIPRE_2 : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- Canonical zero of the same raw width. -/
def zeroRow (v : BitStr) : BitStr := v.map (fun _ => false)

theorem zeroRow_vectorBits {k : ℕ} (v : Fin k → ZMod 2) :
    zeroRow (vectorBits v) = vectorBits (0 : Fin k → ZMod 2) := by
  simp [zeroRow, vectorBits, bit]

def nonzeroRow (v : BitStr) : Bool := decide (v ≠ zeroRow v)

@[simp] theorem nonzeroRow_zero {k : ℕ} :
    nonzeroRow (vectorBits (0 : Fin k → ZMod 2)) = false := by
  simp [nonzeroRow, zeroRow_vectorBits]

/-- One raw split uses cyclic multiplication and XOR, then omits zero vectors. -/
def splitBits (e b : BitStr) : List BitStr :=
  let x := groupMulBitsProg (e, b)
  [x, BinaryPolynomial.xorBits e x].filter nonzeroRow

/-- Raw refinement is clipped to the unary dimension; on valid components this clip is inert. -/
def splitBitsCapped (u : Unary) (l : List BitStr) (b : BitStr) : List BitStr :=
  (l.flatMap (fun e => splitBits e b)).take u.length

end MIPRE.LowDegree.BinaryLinear

end


