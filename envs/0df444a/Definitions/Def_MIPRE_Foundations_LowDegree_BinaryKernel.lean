-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_BinaryKernel
-- name    : MIPRE_Foundations_LowDegree_BinaryKernel
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:22:08.608631+00:00
-- url     : https://prove2.me/theorems/86a7285b-fc19-4ec5-9388-f6a68a0e7bf2
-- title:
--   Definitions of BinaryKernel: Effective generators for a binary matrix kernel
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.BinaryKernel` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Effective generators for a binary matrix kernel
--
--   **Definitions** (4): `MIPRE.LowDegree.BinaryLinear.kernelGeneratorsProg` (Compute at most `n` generators of an `m`-by-`n` binary matrix kernel.); `MIPRE.LowDegree.BinaryLinear.kernelMap` (Reduce the graph of the original matrix map and retain the certificate.); `MIPRE.LowDegree.BinaryLinear.reduceLinear`; `MIPRE.LowDegree.BinaryLinear.reduceStepLinear`.
--
--   **Embedded lemmas** (3): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `reduceLinear_apply`, `reduceStepLinear_apply`, `typedReduceStep_eq_linear`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.BinaryKernel` (`MIPRE/Foundations/LowDegree/BinaryKernel.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 26 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryKernel.lean; blueprint lem:effective-binary-linear-algebra

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryKernel.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_binary_eq_zero_or_one

/-! # Effective generators for a binary matrix kernel -/

namespace MIPRE.LowDegree.BinaryLinear

open Cost Cost.PolyTimeFun

variable {n t : ℕ}

/-- In characteristic two, conditional row addition is a linear map. -/
theorem typedReduceStep_eq_linear (r : Row n t) (p : Pivot n t) :
    typedReduceStep r p = r + (r.1 p.1) • p.2 := by
  rcases binary_eq_zero_or_one (r.1 p.1) with h | h
  · simp [typedReduceStep, h]
  · simp [typedReduceStep, h]
    rfl

def reduceStepLinear (p : Pivot n t) : Row n t →ₗ[ZMod 2] Row n t :=
  LinearMap.id +
    (((LinearMap.proj p.1 : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2).comp
      (LinearMap.fst (ZMod 2) (Fin n → ZMod 2) (Fin t → ZMod 2))).smulRight p.2)

@[simp] theorem reduceStepLinear_apply (p : Pivot n t) (r : Row n t) :
    reduceStepLinear p r = typedReduceStep r p := (typedReduceStep_eq_linear r p).symm

def reduceLinear : List (Pivot n t) → (Row n t →ₗ[ZMod 2] Row n t)
  | [] => LinearMap.id
  | p :: b => (reduceLinear b).comp (reduceStepLinear p)

@[simp] theorem reduceLinear_apply (b : List (Pivot n t)) (r : Row n t) :
    reduceLinear b r = typedReduce b r := by
  induction b generalizing r with
  | nil => rfl
  | cons p b ih =>
    rw [reduceLinear, LinearMap.comp_apply, ih, reduceStepLinear_apply]
    rfl

/-- Reduce the graph of the original matrix map and retain the certificate.
This is a projection onto its kernel. -/
def kernelMap {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) :=
  (LinearMap.snd (ZMod 2) (Fin m → ZMod 2) (Fin n → ZMod 2)).comp
    ((reduceLinear (typedBasis (columnRows A))).comp (A.mulVecLin.prod LinearMap.id))

/-- Compute at most `n` generators of an `m`-by-`n` binary matrix kernel.
The explicit unary input is the number of columns. -/
noncomputable def kernelGeneratorsProg : PolyTimeFun (Unary × List BitStr) (List BitStr) :=
  let rows := coordinateRowsProg.comp transposeBitsProg
  let basis := basisRowsProg.comp rows
  let reduce := reduceRowsProg.comp (snd.pair fst)
  (map snd).comp ((mapWith reduce).comp (rows.pair basis))

end MIPRE.LowDegree.BinaryLinear


