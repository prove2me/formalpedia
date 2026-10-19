-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOrbitDescent
-- name    : MIPRE_Foundations_LowDegree_BinaryOrbitDescent
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:26:00.781819+00:00
-- url     : https://prove2.me/theorems/31513cf5-63f4-4051-95cc-3cd19788e20d
-- title:
--   Definitions of BinaryOrbitDescent: Descending a closed orbit product to binary coefficient bits
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.BinaryOrbitDescent` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Descending a closed orbit product to binary coefficient bits
--
--   **Definitions** (4): `MIPRE.LowDegree.BinaryQuotient.descendBits` (Select the constant coordinate of each quotient coefficient.); `MIPRE.LowDegree.BinaryQuotient.descendBitsProg` (Coefficient descent has a fixed linear-time list program.); `MIPRE.LowDegree.BinaryQuotient.orbitPolynomialBits` (Print binary coefficients of the supplied Frobenius orbit.); `MIPRE.LowDegree.BinaryQuotient.orbitPolynomialBitsProg` (A uniform polynomial-time program for a binary orbit polynomial.).
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `descendBitsProg_apply`, `orbitPolynomialBitsProg_apply`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.BinaryOrbitDescent` (`MIPRE/Foundations/LowDegree/BinaryOrbitDescent.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 33 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryOrbitDescent.lean; blueprint lem:binary-orbit-polynomial

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryOrbitDescent.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.CharP.Algebra
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
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.AdjoinRoot
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryConstants
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotient
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryKernel
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientFrobenius
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientOrbit
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOrbitPolynomial

/-! # Descending a closed orbit product to binary coefficient bits -/

noncomputable section

namespace MIPRE.LowDegree.BinaryQuotient

open Cost Cost.PolyTimeFun BinaryPolynomial Polynomial

variable {R : Type*} [CommRing R]

/-- Select the constant coordinate of each quotient coefficient. -/
def descendBits (cs : List BitStr) : BitStr := cs.map (fun c => c.headD false)

/-- Coefficient descent has a fixed linear-time list program. -/
def descendBitsProg : PolyTimeFun (List BitStr) BitStr := map (headD false)

@[simp] theorem descendBitsProg_apply (cs : List BitStr) :
    descendBitsProg cs = descendBits cs := rfl

variable (f : Polynomial (ZMod 2)) (hf : f.Monic)

/-- Print binary coefficients of the supplied Frobenius orbit. -/
def orbitPolynomialBits (u : Unary) (p a : BitStr) : BitStr :=
  descendBits (orbitProductBits u p a)

/-- A uniform polynomial-time program for a binary orbit polynomial. -/
def orbitPolynomialBitsProg : PolyTimeFun (Unary × BitStr × BitStr) BitStr :=
  descendBitsProg.comp orbitProductBitsProg

@[simp] theorem orbitPolynomialBitsProg_apply (u : Unary) (p a : BitStr) :
    orbitPolynomialBitsProg (u, p, a) = orbitPolynomialBits u p a := by
  change descendBits (orbitProductBitsProg (u, p, a)) = _
  rw [orbitProductBitsProg_apply]
  rfl

end MIPRE.LowDegree.BinaryQuotient

end


