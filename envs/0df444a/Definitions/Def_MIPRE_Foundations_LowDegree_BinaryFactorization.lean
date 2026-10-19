-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_BinaryFactorization
-- name    : MIPRE_Foundations_LowDegree_BinaryFactorization
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:46:37.392263+00:00
-- url     : https://prove2.me/theorems/f6c05b11-68a8-4476-bda3-dbb8033faf8c
-- title:
--   Definitions of BinaryFactorization: Deterministic squarefree factorization over the binary field Frobenius fixed-space separation computes primitive…
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.BinaryFactorization` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Deterministic squarefree factorization over the binary field. Frobenius fixed-space separation computes primitive idempotents of the monic quotient. The factor supported by an idempotent represented by `E` is `gcd(f, E - 1)`. All executing operations are uniform ambient programs; the finite-ring arguments justify correctness without enumerating the quotient.
--
--   **Definitions** (3): `MIPRE.LowDegree.BinaryQuotient.factorBits` (The factor list extracted from the computed primitive components.); `MIPRE.LowDegree.BinaryQuotient.factorBitsProg` (A fixed deterministic polynomial-time squarefree binary factorization program.); `_private.MIPRE.Foundations.LowDegree.BinaryFactorization.0.MIPRE.LowDegree.BinaryQuotient.componentFactorBitsProg`.
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `factorBitsProg_apply`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.BinaryFactorization` (`MIPRE/Foundations/LowDegree/BinaryFactorization.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 42 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryFactorization.lean; blueprint lem:binary-squarefree-factorization

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryFactorization.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Squarefree.Basic
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
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Polynomial.Content
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNormalize
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDivision
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponentsProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientFrobenius
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientFactors
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGCD

/-!
# Deterministic squarefree factorization over the binary field

Frobenius fixed-space separation computes primitive idempotents of the monic
quotient. The factor supported by an idempotent represented by `E` is
`gcd(f, E - 1)`. All executing operations are uniform ambient programs; the
finite-ring arguments justify correctness without enumerating the quotient.
-/

noncomputable section

namespace MIPRE.LowDegree.BinaryQuotient

open Cost Cost.PolyTimeFun Polynomial BinaryPolynomial

/-- The factor list extracted from the computed primitive components. -/
def factorBits (p : BitStr) : List BitStr :=
  (quotientComponentsProg p).map (fun e => gcdBits (p ++ [true]) (xorBits e (oneBits p)))

def componentFactorBitsProg : PolyTimeFun (BitStr × BitStr) BitStr :=
  gcdBitsProg.comp ((append.comp (snd.pair (const [true]))).pair
    (xorBitsProg.comp (fst.pair (oneBitsProg.comp snd))))

/-- A fixed deterministic polynomial-time squarefree binary factorization program.
Its input consists of the lower coefficients of the monic polynomial. -/
def factorBitsProg : PolyTimeFun BitStr (List BitStr) :=
  (mapWith componentFactorBitsProg).comp (quotientComponentsProg.pair (PolyTimeFun.id _))

@[simp] theorem factorBitsProg_apply (p : BitStr) : factorBitsProg p = factorBits p := rfl

variable (f : Polynomial (ZMod 2)) (hf : f.Monic)

end MIPRE.LowDegree.BinaryQuotient

end


