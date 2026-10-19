-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientFrobenius
-- name    : MIPRE_Foundations_LowDegree_BinaryQuotientFrobenius
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:22:48.412828+00:00
-- url     : https://prove2.me/theorems/9a0dcbfa-fc48-4497-9302-3abfb3ad4dfa
-- title:
--   Definitions of BinaryQuotientFrobenius: Computing Frobenius matrices in arbitrary monic binary quotients
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.BinaryQuotientFrobenius` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Computing Frobenius matrices in arbitrary monic binary quotients
--
--   **Definitions** (8): `MIPRE.LowDegree.BinaryQuotient.fixedGenerator` (Abstract interpretation of the computed kernel generators in the quotient.); `MIPRE.LowDegree.BinaryQuotient.fixedGeneratorsProg` (Print a bounded family spanning the quotient's complete Frobenius fixed space.); `MIPRE.LowDegree.BinaryQuotient.fixedMatrix` (The fixed-space equation for quotient Frobenius.); `MIPRE.LowDegree.BinaryQuotient.fixedMatrixProg` (Compute Frobenius plus identity on coefficient vectors.); `MIPRE.LowDegree.BinaryQuotient.frobeniusLinear` (Frobenius is binary linear even when the quotient is not a field.); `MIPRE.LowDegree.BinaryQuotient.frobeniusMatrix` (Frobenius in the specified monic power basis.); `MIPRE.LowDegree.BinaryQuotient.frobeniusMatrixProg` (Compute the squares of the power-basis vectors and transpose their columns.); `MIPRE.LowDegree.BinaryQuotient.squareProg` (Squaring modulo a supplied monic polynomial, without constructing a field.).
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `frobeniusLinear_apply`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.BinaryQuotientFrobenius` (`MIPRE/Foundations/LowDegree/BinaryQuotientFrobenius.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 28 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryQuotientFrobenius.lean; blueprint lem:binary-quotient-fixed-space

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryQuotientFrobenius.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryKernel

/-! # Computing Frobenius matrices in arbitrary monic binary quotients -/

noncomputable section

namespace MIPRE.LowDegree.BinaryQuotient

open Cost BinaryPolynomial BinaryLinear

variable (f : Polynomial (ZMod 2)) (hf : f.Monic)

/-- Frobenius is binary linear even when the quotient is not a field. -/
def frobeniusLinear : AdjoinRoot f →ₗ[ZMod 2] AdjoinRoot f :=
  (FiniteField.frobeniusAlgHom (ZMod 2) (AdjoinRoot f)).toLinearMap

/-- In a binary algebra the Frobenius map is squaring. -/
@[simp] theorem frobeniusLinear_apply (x : AdjoinRoot f) :
    frobeniusLinear f x = x ^ 2 := by
  simp [frobeniusLinear, FiniteField.frobeniusAlgHom]

/-- Frobenius in the specified monic power basis. -/
def frobeniusMatrix : Matrix (Fin f.natDegree) (Fin f.natDegree) (ZMod 2) :=
  LinearMap.toMatrix (AdjoinRoot.powerBasisAux' hf) (AdjoinRoot.powerBasisAux' hf)
    (frobeniusLinear f)

/-- Squaring modulo a supplied monic polynomial, without constructing a field. -/
def squareProg : PolyTimeFun (BitStr × BitStr) BitStr :=
  mulReduceProg.comp (PolyTimeFun.fst.pair (PolyTimeFun.snd.pair PolyTimeFun.snd))

/-- Compute the squares of the power-basis vectors and transpose their columns. -/
def frobeniusMatrixProg : PolyTimeFun BitStr (List BitStr) :=
  let columns := (PolyTimeFun.mapWith
    (squareProg.comp (PolyTimeFun.snd.pair PolyTimeFun.fst))).comp
      ((identityBitsProg.comp PolyTimeFun.length).pair (PolyTimeFun.id _))
  transposeBitsProg.comp (PolyTimeFun.length.pair columns)

/-- The fixed-space equation for quotient Frobenius. -/
def fixedMatrix : Matrix (Fin f.natDegree) (Fin f.natDegree) (ZMod 2) :=
  frobeniusMatrix f hf + 1

/-- Compute Frobenius plus identity on coefficient vectors. -/
def fixedMatrixProg : PolyTimeFun BitStr (List BitStr) :=
  addMatrixBitsProg.comp
    (frobeniusMatrixProg.pair (identityBitsProg.comp PolyTimeFun.length))

/-- Print a bounded family spanning the quotient's complete Frobenius fixed space. -/
def fixedGeneratorsProg : PolyTimeFun BitStr (List BitStr) :=
  kernelGeneratorsProg.comp (PolyTimeFun.length.pair fixedMatrixProg)

/-- Abstract interpretation of the computed kernel generators in the quotient. -/
def fixedGenerator (j : Fin f.natDegree) : AdjoinRoot f :=
  (coordinateEquiv f hf).symm (kernelMap (fixedMatrix f hf) (Pi.single j 1))

end MIPRE.LowDegree.BinaryQuotient

end


