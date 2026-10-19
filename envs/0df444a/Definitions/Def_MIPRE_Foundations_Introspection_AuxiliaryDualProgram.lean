-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryDualProgram
-- name    : MIPRE_Foundations_Introspection_AuxiliaryDualProgram
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:49:09.617751+00:00
-- url     : https://prove2.me/theorems/1ca594da-30e6-462d-8b00-df75f78e8211
-- title:
--   Definitions of AuxiliaryDualProgram: Executable canonical dual of a binary linear map The rows of a matrix span the dot-product orthogonal complement of its…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.AuxiliaryDualProgram` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Executable canonical dual of a binary linear map. The rows of a matrix span the dot-product orthogonal complement of its kernel. Canonical elimination of those rows therefore computes the exact `CL.lperp`, including for singular matrices and in dimension zero.
--
--   **Definitions** (1): `MIPRE.Introspection.AuxiliaryDual.rowSpaceCheck` (Membership in the supplied row span, tested by exact canonical reduction.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.AuxiliaryDualProgram` (`MIPRE/Foundations/Introspection/AuxiliaryDualProgram.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 33 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/AuxiliaryDualProgram.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AuxiliaryDualProgram.lean (definition bundle: declarations the uploaded statements rest on);
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
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryKernel
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryCanonicalProgram

/-! # Executable canonical dual of a binary linear map

The rows of a matrix span the dot-product orthogonal complement of its
kernel. Canonical elimination of those rows therefore computes the exact
`CL.lperp`, including for singular matrices and in dimension zero.
-/

noncomputable section
namespace MIPRE.Introspection.AuxiliaryDual

open Cost Cost.PolyTimeFun LowDegree.BinaryLinear
set_option backward.isDefEq.respectTransparency false

variable {F : Type*} [Field F] {m n : ℕ}

/-- Membership in the supplied row span, tested by exact canonical reduction.
The zero vector has the input vector's width, so malformed widths do not become
an implicit promise about the program's termination. -/
def rowSpaceCheck : PolyTimeFun (List BitStr × BitStr) Bool :=
  SAT.ArrayProg.eqBits.comp (AuxiliaryCanonical.canonicalProg.pair
    ((map (const false)).comp snd))

end MIPRE.Introspection.AuxiliaryDual
end


