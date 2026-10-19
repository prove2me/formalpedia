-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGroupAlgebra_B
-- name    : MIPRE_Foundations_LowDegree_BinaryGroupAlgebra_B
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:53:22.261485+00:00
-- url     : https://prove2.me/theorems/7cdb1741-0ca6-4b63-b37d-3bfa2d4dbb8f
-- title:
--   Definitions of BinaryGroupAlgebra (addendum): Effective binary cyclic group algebra coordinates
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.BinaryGroupAlgebra` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Effective binary cyclic group algebra coordinates
--
--   This bundle **adds** the declarations below to the already published bundle `MIPRE_Foundations_LowDegree_BinaryGroupAlgebra` of the same module, which the new statements of this upload need and the earlier bundle left out.
--
--   **Definitions** (9): `MIPRE.LowDegree.BinaryLinear.groupCoordinates` (All cyclic group-algebra coefficients as a binary linear equivalence.); `MIPRE.LowDegree.BinaryLinear.groupFixedGenerator`; `MIPRE.LowDegree.BinaryLinear.groupFixedGeneratorsProg` (At most `k` coefficient vectors generate all idempotents of the binary cyclic algebra.); `MIPRE.LowDegree.BinaryLinear.groupFixedMatrix` (The fixed-space equation is squaring plus the identity, in characteristic two.); `MIPRE.LowDegree.BinaryLinear.groupFixedMatrixProg` (Construct the binary fixed-space equation.); `MIPRE.LowDegree.BinaryLinear.groupSquareCoordinates`; `MIPRE.LowDegree.BinaryLinear.groupSquareLinear` (Squaring in a binary commutative group algebra is a linear map.); `MIPRE.LowDegree.BinaryLinear.groupSquareMatrix`; `MIPRE.LowDegree.BinaryLinear.groupSquareMatrixProg` (Print the squaring matrix by applying cyclic convolution to the coordinate units.).
--
--   **Embedded lemmas** (6): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `groupCoordinates_apply`, `groupCoordinates_finGroupOfVector`, `groupCoordinates_symm_apply`, `groupSquareCoordinates_apply`, `groupSquareLinear_apply`, `instFactPrimeOfNatNat_mIPRE_1`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.BinaryGroupAlgebra` (`MIPRE/Foundations/LowDegree/BinaryGroupAlgebra.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 38 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryGroupAlgebra.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryGroupAlgebra.lean (delta bundle: declarations the new statements need that the published bundle Def_MIPRE_Foundations_LowDegree_BinaryGroupAlgebra does not carry);
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasis
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixInverse
import Definitions.Def_MIPRE_Foundations_LowDegree_SelfDualize
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySquareRoot
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCirculant
import Definitions.Def_MIPRE_Foundations_Cost_Iterates
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCirculantProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCirculantProg_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryKernel
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGroupAlgebra
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_kernelGeneratorsProg_encoding
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_transposeBits_matrixBits

/-! # Effective binary cyclic group algebra coordinates -/

noncomputable section

namespace MIPRE.LowDegree.BinaryLinear

open Cost Cost.PolyTimeFun

local instance instFactPrimeOfNatNat_mIPRE_1 : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- All cyclic group-algebra coefficients as a binary linear equivalence. -/
def groupCoordinates (k : ℕ) :
    AddMonoidAlgebra (ZMod 2) (Fin k) ≃ₗ[ZMod 2] (Fin k → ZMod 2) :=
  (AddMonoidAlgebra.coeffLinearEquiv (ZMod 2)).trans
    (Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) (Fin k))

@[simp] theorem groupCoordinates_apply (k : ℕ)
    (z : AddMonoidAlgebra (ZMod 2) (Fin k)) (i : Fin k) : groupCoordinates k z i = z.coeff i := rfl

@[simp] theorem groupCoordinates_finGroupOfVector {k : ℕ} [NeZero k] (v : Fin k → ZMod 2) :
    groupCoordinates k (finGroupOfVector v) = v := by
  ext i
  simp

@[simp] theorem groupCoordinates_symm_apply {k : ℕ} [NeZero k] (v : Fin k → ZMod 2) :
    (groupCoordinates k).symm v = finGroupOfVector v := by
  apply (groupCoordinates k).injective
  simp

/-- Squaring in a binary commutative group algebra is a linear map. -/
def groupSquareLinear (k : ℕ) [NeZero k] :
    AddMonoidAlgebra (ZMod 2) (Fin k) →ₗ[ZMod 2] AddMonoidAlgebra (ZMod 2) (Fin k) :=
  (FiniteField.frobeniusAlgHom (ZMod 2) (AddMonoidAlgebra (ZMod 2) (Fin k))).toLinearMap

@[simp] theorem groupSquareLinear_apply (k : ℕ) [NeZero k]
    (z : AddMonoidAlgebra (ZMod 2) (Fin k)) : groupSquareLinear k z = z * z := by
  simp [groupSquareLinear, FiniteField.frobeniusAlgHom, pow_two]

def groupSquareCoordinates (k : ℕ) [NeZero k] :
    (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) :=
  (groupCoordinates k).toLinearMap.comp
    ((groupSquareLinear k).comp (groupCoordinates k).symm.toLinearMap)

@[simp] theorem groupSquareCoordinates_apply (k : ℕ) [NeZero k]
    (z : AddMonoidAlgebra (ZMod 2) (Fin k)) :
    groupSquareCoordinates k (groupCoordinates k z) = groupCoordinates k (z * z) := by
  simp [groupSquareCoordinates]

def groupSquareMatrix (k : ℕ) [NeZero k] : Matrix (Fin k) (Fin k) (ZMod 2) :=
  LinearMap.toMatrix' (groupSquareCoordinates k)

/-- Print the squaring matrix by applying cyclic convolution to the coordinate units. -/
def groupSquareMatrixProg : PolyTimeFun Unary (List BitStr) :=
  let square := groupMulBitsProg.comp ((PolyTimeFun.id _).pair (PolyTimeFun.id _))
  transposeBitsProg.comp ((PolyTimeFun.id _).pair ((map square).comp identityBitsProg))

/-- The fixed-space equation is squaring plus the identity, in characteristic two. -/
def groupFixedMatrix (k : ℕ) [NeZero k] : Matrix (Fin k) (Fin k) (ZMod 2) :=
  groupSquareMatrix k + 1

/-- Construct the binary fixed-space equation. -/
def groupFixedMatrixProg : PolyTimeFun Unary (List BitStr) :=
  addMatrixBitsProg.comp (groupSquareMatrixProg.pair identityBitsProg)

/-- At most `k` coefficient vectors generate all idempotents of the binary cyclic algebra. -/
def groupFixedGeneratorsProg : PolyTimeFun Unary (List BitStr) :=
  kernelGeneratorsProg.comp ((PolyTimeFun.id _).pair groupFixedMatrixProg)

def groupFixedGenerator (k : ℕ) [NeZero k] (j : Fin k) :
    AddMonoidAlgebra (ZMod 2) (Fin k) :=
  (groupCoordinates k).symm (kernelMap (groupFixedMatrix k) (Pi.single j 1))

end MIPRE.LowDegree.BinaryLinear

end


