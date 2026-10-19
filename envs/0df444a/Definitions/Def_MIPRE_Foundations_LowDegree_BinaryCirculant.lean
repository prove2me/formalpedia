-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCirculant
-- name    : MIPRE_Foundations_LowDegree_BinaryCirculant
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:51:30.121088+00:00
-- url     : https://prove2.me/theorems/153fb84f-7da8-40c1-a230-8f25687e0126
-- title:
--   Definitions of BinaryCirculant: Binary cyclic group algebras as circulant matrices
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.BinaryCirculant` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Binary cyclic group algebras as circulant matrices
--
--   **Definitions** (4): `MIPRE.LowDegree.BinaryLinear.finGroupOfVector` (Coefficient vectors are encoded with the same ordering as binary matrices.); `MIPRE.LowDegree.BinaryLinear.groupMatrix` (The regular representation of a finite binary group algebra is circulant.); `MIPRE.LowDegree.BinaryLinear.groupMatrixHom` (The identity and product laws allow algebraic square roots to be used as matrices.); `MIPRE.LowDegree.BinaryLinear.inverseRootMatrix` (The inverse circulant's square root is read from doubled indices of its first column.).
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `coeff_finGroupOfVector`, `groupMatrix_mul`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.BinaryCirculant` (`MIPRE/Foundations/LowDegree/BinaryCirculant.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 32 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryCirculant.lean; blueprint lem:effective-normal-selfdualization

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryCirculant.lean (definition bundle: declarations the uploaded statements rest on);
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

/-! # Binary cyclic group algebras as circulant matrices -/

noncomputable section

namespace MIPRE.LowDegree.BinaryLinear

open Cost

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The regular representation of a finite binary group algebra is circulant. -/
def groupMatrix (z : AddMonoidAlgebra (ZMod 2) G) : Matrix G G (ZMod 2) :=
  Matrix.circulant z.coeff

theorem groupMatrix_mul (z w : AddMonoidAlgebra (ZMod 2) G) :
    groupMatrix (z * w) = groupMatrix z * groupMatrix w := by
  rw [groupMatrix, groupMatrix, groupMatrix, Matrix.circulant_mul]
  congr 1
  funext g
  rw [AddMonoidAlgebra.coeff_mul_apply_right]
  rw [Finsupp.sum_fintype _ _ (by intro j; simp)]
  simp only [Matrix.mulVec, dotProduct, Matrix.circulant_apply, sub_eq_add_neg]

/-- The identity and product laws allow algebraic square roots to be used as matrices. -/
def groupMatrixHom : AddMonoidAlgebra (ZMod 2) G →+* Matrix G G (ZMod 2) where
  toFun := groupMatrix
  map_one' := by
    ext i j
    change (AddMonoidAlgebra.single (0 : G) (1 : ZMod 2)).coeff (i - j) =
      (1 : Matrix G G (ZMod 2)) i j
    simp [Matrix.one_apply, Finsupp.single_apply, sub_eq_zero, eq_comm]
  map_mul' := groupMatrix_mul
  map_zero' := by simp [groupMatrix]
  map_add' := fun z w => by
    ext i j
    simp [groupMatrix]

/-- Coefficient vectors are encoded with the same ordering as binary matrices. -/
def finGroupOfVector {k : ℕ} [NeZero k] (v : Fin k → ZMod 2) :
    AddMonoidAlgebra (ZMod 2) (Fin k) :=
  .ofCoeff (Finsupp.onFinset Finset.univ v (fun i _ => Finset.mem_univ i))

@[simp] theorem coeff_finGroupOfVector {k : ℕ} [NeZero k]
    (v : Fin k → ZMod 2) (i : Fin k) : (finGroupOfVector v).coeff i = v i := by
  simp [finGroupOfVector]

/-- The inverse circulant's square root is read from doubled indices of its first column. -/
def inverseRootMatrix {k : ℕ} [NeZero k] (A : Matrix (Fin k) (Fin k) (ZMod 2)) :
    Matrix (Fin k) (Fin k) (ZMod 2) :=
  Matrix.circulant (fun i => inverseMatrix A (i + i) 0)

end MIPRE.LowDegree.BinaryLinear

end


