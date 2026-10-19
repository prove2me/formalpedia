-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOddPrimeProgram
-- name    : MIPRE_Foundations_LowDegree_BinaryOddPrimeProgram
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:57:31.65079+00:00
-- url     : https://prove2.me/theorems/de72a79e-c11e-4bb3-b400-6a290d286e2b
-- title:
--   Definitions of BinaryOddPrimeProgram: The explicit odd-prime-power construction program
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.BinaryOddPrimeProgram` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # The explicit odd-prime-power construction program
--
--   **Definitions** (5): `MIPRE.LowDegree.BinaryPolynomial.oddExtensionBits` (The full binary modulus for Shoup's flat auxiliary extension.); `MIPRE.LowDegree.BinaryPolynomial.oddExtensionLowerBits` (The lower coefficients used by quotient arithmetic.); `MIPRE.LowDegree.BinaryPolynomial.oddPrimePowerBits` (Print the descended orbit polynomial of the trace generator.); `MIPRE.LowDegree.BinaryPolynomial.oddPrimePowerBitsProg` (One total polynomial-time program takes unary prime and requested prime-power degree.); `MIPRE.LowDegree.BinaryPolynomial.oddTraceBits` (The trace generator in the explicitly represented flat extension.).
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `oddPrimePowerBitsProg_apply`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.BinaryOddPrimeProgram` (`MIPRE/Foundations/LowDegree/BinaryOddPrimeProgram.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 56 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryOddPrimeProgram.lean; blueprint lem:binary-odd-prime-power-irreducible

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryOddPrimeProgram.lean (definition bundle: declarations the uploaded statements rest on);
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
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryFactorization
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCyclotomicSeed
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySubstitution
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNonresidueLoop
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNonresidueCorrectness
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientOrbit
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryTraceBits
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOrbitPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOrbitDescent
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientTranslation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCoprimeDegree
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComposedSumPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComposedSumProg

/-! # The explicit odd-prime-power construction program -/

noncomputable section

namespace MIPRE.LowDegree.BinaryPolynomial

open Cost Cost.PolyTimeFun Polynomial BinaryQuotient

/-- The full binary modulus for Shoup's flat auxiliary extension. -/
def oddExtensionBits (q r : Unary) : BitStr :=
  substitutePowerBits (nonresidueLiftBitsProg q) r.tail

/-- The lower coefficients used by quotient arithmetic. -/
def oddExtensionLowerBits (q r : Unary) : BitStr := (oddExtensionBits q r).dropLast

/-- The trace generator in the explicitly represented flat extension. -/
def oddTraceBits (q r : Unary) : BitStr :=
  let p := oddExtensionLowerBits q r
  traceBits (unary (nonresidueLiftBitsProg q).tail.length) r p (BinaryQuotient.rootBits p)

/-- Print the descended orbit polynomial of the trace generator. -/
def oddPrimePowerBits (q r : Unary) : BitStr :=
  normalizeBits (orbitPolynomialBits r (oddExtensionLowerBits q r) (oddTraceBits q r))

/-- One total polynomial-time program takes unary prime and requested prime-power degree. -/
def oddPrimePowerBitsProg : PolyTimeFun (Unary × Unary) BitStr :=
  let aux := nonresidueLiftBitsProg.comp fst
  let r := snd
  let p := dropLastBitsProg.comp (substitutePowerBitsProg.comp
    (aux.pair (PolyTimeFun.tail.comp r)))
  let m := length.comp (PolyTimeFun.tail.comp aux)
  let gamma := traceBitsProg.comp (m.pair (r.pair (p.pair (BinaryQuotient.rootBitsProg.comp p))))
  normalizeBitsProg.comp (orbitPolynomialBitsProg.comp (r.pair (p.pair gamma)))

@[simp] theorem oddPrimePowerBitsProg_apply (q r : Unary) :
    oddPrimePowerBitsProg (q, r) = oddPrimePowerBits q r := by
  simp only [oddPrimePowerBitsProg, comp_apply, pair_apply, fst_apply, snd_apply,
    dropLastBitsProg_apply, substitutePowerBitsProg_apply, tail_apply, length_apply,
    traceBitsProg_apply, BinaryQuotient.rootBitsProg_apply, orbitPolynomialBitsProg_apply, normalizeBitsProg_apply]
  rfl

end MIPRE.LowDegree.BinaryPolynomial

end


