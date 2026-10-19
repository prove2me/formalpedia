-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixInverse
-- name    : MIPRE_Foundations_LowDegree_BinaryMatrixInverse
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:50:18.971681+00:00
-- url     : https://prove2.me/theorems/7812d534-d3e0-4606-9ea8-51ed73c87623
-- title:
--   Definitions of BinaryMatrixInverse: Uniform binary matrix inversion
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.BinaryMatrixInverse` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Uniform binary matrix inversion
--
--   **Definitions** (4): `MIPRE.LowDegree.BinaryLinear.inverseMatrix` (The inverse is assembled column by column, solving for each standard basis vector.); `MIPRE.LowDegree.BinaryLinear.inverseMatrixProg` (One globally polynomial-time ambient program for binary matrix inversion.); `MIPRE.LowDegree.BinaryLinear.matrixSolution` (The coefficient vector selected by the deterministic elimination algorithm.); `_private.MIPRE.Foundations.LowDegree.BinaryMatrixInverse.0.MIPRE.LowDegree.BinaryLinear.inverseColumnsProg`.
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `matrixSolveProg_encoding`, `inverseColumnsProg_encoding`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.BinaryMatrixInverse` (`MIPRE/Foundations/LowDegree/BinaryMatrixInverse.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 29 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryMatrixInverse.lean; blueprint lem:effective-binary-linear-algebra

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryMatrixInverse.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve_B
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_coordinateRows_matrixBits
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_transposeBits_matrixBits
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_basisSolveProg_encoding
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_identityBits_eq_matrixBits

/-! # Uniform binary matrix inversion -/

namespace MIPRE.LowDegree.BinaryLinear

open Cost Cost.PolyTimeFun

/-- The coefficient vector selected by the deterministic elimination algorithm. -/
def matrixSolution {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (v : Fin m → ZMod 2) : Fin n → ZMod 2 :=
  (typedReduce (typedBasis (columnRows A)) (v, 0)).2

theorem matrixSolveProg_encoding {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) (v : Fin m → ZMod 2) :
    matrixSolveProg (unary n, matrixBits A, vectorBits v) = vectorBits (matrixSolution A v) := by
  change basisSolveProg
    (unary n, coordinateRows (transposeBits (unary n).length (matrixBits A)), vectorBits v) = _
  rw [length_unary, coordinateRows_matrixBits, basisSolveProg_encoding]
  rfl

/-- The inverse is assembled column by column, solving for each standard basis vector. -/
def inverseMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2)) :
    Matrix (Fin n) (Fin n) (ZMod 2) :=
  fun i j => matrixSolution A (Pi.single j 1) i

noncomputable def inverseColumnsProg : PolyTimeFun (Unary × List BitStr) (List BitStr) :=
  let solve : PolyTimeFun (BitStr × (Unary × List BitStr)) BitStr :=
    matrixSolveProg.comp ((fst.comp snd).pair ((snd.comp snd).pair fst))
  (mapWith solve).comp ((identityBitsProg.comp fst).pair (PolyTimeFun.id _))

theorem inverseColumnsProg_encoding {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (ZMod 2)) :
    inverseColumnsProg (unary n, matrixBits A) = matrixBits (inverseMatrix A).transpose := by
  change (identityBits (unary n).length).map
    (fun v => matrixSolveProg (unary n, matrixBits A, v)) = _
  rw [length_unary, identityBits_eq_matrixBits]
  simp only [matrixBits, List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  have hj : (1 : Matrix (Fin n) (Fin n) (ZMod 2)) j = Pi.single j 1 := by
    funext i
    simp [Pi.single_apply, Matrix.one_apply, eq_comm]
  change matrixSolveProg (unary n, matrixBits A, vectorBits ((1 : Matrix (Fin n) (Fin n) (ZMod 2)) j)) = _
  rw [hj, matrixSolveProg_encoding]
  rfl

/-- One globally polynomial-time ambient program for binary matrix inversion.
The dimension is explicit and unary; correctness requires a nonsingular matrix. -/
noncomputable def inverseMatrixProg : PolyTimeFun (Unary × List BitStr) (List BitStr) :=
  transposeBitsProg.comp (fst.pair inverseColumnsProg)

end MIPRE.LowDegree.BinaryLinear


