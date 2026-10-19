-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCyclotomicSeed
-- name    : MIPRE_Foundations_LowDegree_BinaryCyclotomicSeed
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:47:47.208696+00:00
-- url     : https://prove2.me/theorems/9777c799-485f-403b-b691-cc01d50c443d
-- title:
--   Definitions of BinaryCyclotomicSeed: The deterministic cyclotomic seed for odd prime-power construction For an odd prime `q`, factor `1+X+...+X^(q-1)` and…
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.BinaryCyclotomicSeed` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The deterministic cyclotomic seed for odd prime-power construction. For an odd prime `q`, factor `1+X+...+X^(q-1)` and choose the first factor in the specified factorization order. This gives a concrete irreducible polynomial of degree equal to the order of two modulo `q`; it does not enumerate fields.
--
--   **Definitions** (4): `MIPRE.LowDegree.BinaryPolynomial.cyclotomicLowerBits` (Lower coefficients of the prime cyclotomic polynomial; the leading one is implicit.); `MIPRE.LowDegree.BinaryPolynomial.cyclotomicLowerBitsProg` (Uniform unary printing of the binary prime-cyclotomic coefficient vector.); `MIPRE.LowDegree.BinaryPolynomial.cyclotomicSeedBits` (Choose the first factor in the fixed deterministic factorization order.); `MIPRE.LowDegree.BinaryPolynomial.cyclotomicSeedBitsProg` (One fixed ambient program producing the auxiliary irreducible seed.).
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `cyclotomicLowerBitsProg_apply`, `cyclotomicSeedBitsProg_apply`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.BinaryCyclotomicSeed` (`MIPRE/Foundations/LowDegree/BinaryCyclotomicSeed.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 43 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryCyclotomicSeed.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryCyclotomicSeed.lean (definition bundle: declarations the uploaded statements rest on);
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

/-!
# The deterministic cyclotomic seed for odd prime-power construction

For an odd prime `q`, factor `1+X+...+X^(q-1)` and choose the first factor in the
specified factorization order. This gives a concrete irreducible polynomial of
degree equal to the order of two modulo `q`; it does not enumerate fields.
-/

noncomputable section

namespace MIPRE.LowDegree.BinaryPolynomial

open Cost Cost.PolyTimeFun Polynomial

/-- Lower coefficients of the prime cyclotomic polynomial; the leading one is implicit. -/
def cyclotomicLowerBits (u : Unary) : BitStr := List.replicate (u.length - 1) true

/-- Uniform unary printing of the binary prime-cyclotomic coefficient vector. -/
def cyclotomicLowerBitsProg : PolyTimeFun Unary BitStr :=
  congr (replicate.comp (PolyTimeFun.tail.pair (const true))) cyclotomicLowerBits (by
    intro u
    simp [cyclotomicLowerBits])

@[simp] theorem cyclotomicLowerBitsProg_apply (u : Unary) :
    cyclotomicLowerBitsProg u = cyclotomicLowerBits u := rfl

/-- Choose the first factor in the fixed deterministic factorization order. -/
def cyclotomicSeedBits (u : Unary) : BitStr :=
  (BinaryQuotient.factorBitsProg (cyclotomicLowerBits u)).headD []

/-- One fixed ambient program producing the auxiliary irreducible seed. -/
def cyclotomicSeedBitsProg : PolyTimeFun Unary BitStr :=
  (PolyTimeFun.headD []).comp (BinaryQuotient.factorBitsProg.comp cyclotomicLowerBitsProg)

@[simp] theorem cyclotomicSeedBitsProg_apply (u : Unary) :
    cyclotomicSeedBitsProg u = cyclotomicSeedBits u := rfl

end MIPRE.LowDegree.BinaryPolynomial

end


