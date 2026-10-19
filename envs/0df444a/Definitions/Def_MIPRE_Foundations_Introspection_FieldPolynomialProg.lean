-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_FieldPolynomialProg
-- name    : MIPRE_Foundations_Introspection_FieldPolynomialProg
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T05:31:56.143397+00:00
-- url     : https://prove2.me/theorems/bf9e27a3-c5fd-4f61-98c0-7fda6bfce11f
-- title:
--   Definitions of FieldPolynomialProg: Uniform evaluation of field coefficient vectors Coefficients are listed in increasing degree order
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.FieldPolynomialProg` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Uniform evaluation of field coefficient vectors. Coefficients are listed in increasing degree order. The program constructs the field modulus once, then uses Horner's rule. Its ambient polynomial bound also holds on malformed inputs: every step preserves the modulus and evaluation point, and the accumulator's bit length can only decrease. This file does not parse answers or claim correctness of the Pauli decider. It supplies the arithmetic operation needed by its two line tests.
--
--   **Definitions** (5): `MIPRE.Introspection.FieldPolynomialProgram.evalCoeffs` (Evaluation of a coefficient list in increasing degree order.); `MIPRE.Introspection.FieldPolynomialProgram.hornerFoldProg` (Horner evaluation with an explicit modulus, point and initial accumulator.); `MIPRE.Introspection.FieldPolynomialProgram.shoupHornerProg` (One ambient program, uniform in both field width and coefficient count.); `_private.MIPRE.Foundations.Introspection.FieldPolynomialProg.0.MIPRE.Introspection.FieldPolynomialProgram.hornerStep`; `_private.MIPRE.Foundations.Introspection.FieldPolynomialProg.0.MIPRE.Introspection.FieldPolynomialProgram.hornerStepProg`.
--
--   **Embedded lemmas** (6): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `evalCoeffs_cons`, `evalCoeffs_nil`, `fold_hornerStep`, `fold_hornerStep_acc`, `hornerStep_bounded`, `hornerStep_width`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.FieldPolynomialProg` (`MIPRE/Foundations/Introspection/FieldPolynomialProg.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 89 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/FieldPolynomialProg.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/FieldPolynomialProg.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Rotate
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_SAT_Succinct
import Definitions.Def_MIPRE_Foundations_SAT_Decoupled
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_SAT_Pcp
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryConstants
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPower
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOddPrimeProgram
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPrimePowerTrace
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreier
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreierProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreierTower
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreierLoop
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryDegreeArithmetic
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryPrimality
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryPrimePower
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDegreeFactors
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDegreeDecomposition
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPrimePowerDispatch
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryIrreducibleAssembly
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryIrreducibleConstructor
import Definitions.Def_MIPRE_Foundations_LowDegree_Shoup
import Definitions.Def_MIPRE_Foundations_LowDegree_ShoupCoefficients
import Definitions.Def_MIPRE_Foundations_SAT_QuotientField
import Definitions.Def_MIPRE_Foundations_SAT_FieldTrace
import Definitions.Def_MIPRE_Foundations_SAT_FieldCoordinates
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryFold
import Definitions.Def_MIPRE_Foundations_SAT_NormalElementProg
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_length_mulReduce_le

/-! # Uniform evaluation of field coefficient vectors

Coefficients are listed in increasing degree order. The program constructs the
field modulus once, then uses Horner's rule. Its ambient polynomial bound also
holds on malformed inputs: every step preserves the modulus and evaluation
point, and the accumulator's bit length can only decrease.

This file does not parse answers or claim correctness of the Pauli decider.
It supplies the arithmetic operation needed by its two line tests.
-/

noncomputable section
namespace MIPRE.Introspection.FieldPolynomialProgram
open Cost Cost.PolyTimeFun Polynomial LowDegree.BinaryPolynomial SAT

/-- Evaluation of a coefficient list in increasing degree order. -/
def evalCoeffs {R : Type*} [Semiring R] (x : R) (coeffs : List R) : R :=
  coeffs.foldr (fun c a => a * x + c) 0

@[simp] theorem evalCoeffs_nil {R : Type*} [Semiring R] (x : R) :
    evalCoeffs x [] = 0 := rfl

@[simp] theorem evalCoeffs_cons {R : Type*} [Semiring R] (x c : R) (coeffs : List R) :
    evalCoeffs x (c :: coeffs) = evalCoeffs x coeffs * x + c := rfl

def hornerStep (s : BitStr × BitStr × BitStr) (c : BitStr) :
    BitStr × BitStr × BitStr :=
  (s.1, s.2.1, xorBits (mulReduce s.1 s.2.2 s.2.1) c)

theorem hornerStep_width (s : BitStr × BitStr × BitStr) (c : BitStr) :
    (hornerStep s c).2.2.length ≤ s.2.2.length := by
  change (xorBits (mulReduce s.1 s.2.2 s.2.1) c).length ≤ _
  rw [length_xorBits]
  exact (min_le_left _ _).trans (length_mulReduce_le _ _ _)

theorem fold_hornerStep (l : List BitStr) (s : BitStr × BitStr × BitStr) :
    (l.foldl hornerStep s).1 = s.1 ∧
    (l.foldl hornerStep s).2.1 = s.2.1 ∧
    (l.foldl hornerStep s).2.2.length ≤ s.2.2.length := by
  induction l generalizing s with
  | nil => exact ⟨rfl, rfl, le_rfl⟩
  | cons c l ih =>
    obtain ⟨hp, hx, ha⟩ := ih (hornerStep s c)
    exact ⟨hp, hx, ha.trans (hornerStep_width s c)⟩

theorem fold_hornerStep_acc (l : List BitStr) (p x a : BitStr) :
    (l.foldl hornerStep (p, x, a)).2.2 =
      l.foldl (fun a c => xorBits (mulReduce p a x) c) a := by
  induction l generalizing a with
  | nil => rfl
  | cons c l ih => exact ih _

def hornerStepProg :
    PolyTimeFun ((BitStr × BitStr × BitStr) × BitStr) (BitStr × BitStr × BitStr) :=
  let p := fst.comp fst
  let x := fst.comp (snd.comp fst)
  let a := snd.comp (snd.comp fst)
  p.pair (x.pair (xorBitsProg.comp
    ((mulReduceProg.comp (p.pair (a.pair x))).pair snd)))

theorem hornerStep_bounded : FoldBounded hornerStepProg (5 * X + 5) := by
  intro l s pre post _
  change esize (pre.foldl hornerStep s) ≤ _
  obtain ⟨hp, hx, ha⟩ := fold_hornerStep pre s
  have hi := length_le_esize_list s.2.2
  have ho := esize_bitStr_le (pre.foldl hornerStep s).2.2
  have hs : esize s = esize s.1 + (esize s.2.1 + esize s.2.2 + 1) + 1 := rfl
  change esize (pre.foldl hornerStep s).1 +
    (esize (pre.foldl hornerStep s).2.1 + esize (pre.foldl hornerStep s).2.2 + 1) + 1 ≤ _
  rw [hp, hx]
  simp only [esize_prod, hs, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_ofNat, Polynomial.eval_X]
  omega

/-- Horner evaluation with an explicit modulus, point and initial accumulator.
The initial accumulator is useful for the correctness induction; ordinary
polynomial evaluation initializes it to the field's zero vector. -/
def hornerFoldProg :
    PolyTimeFun (List BitStr × (BitStr × BitStr × BitStr)) BitStr :=
  congr (((snd.comp snd).comp
      (foldl hornerStepProg (5 * X + 5) hornerStep_bounded)).comp
      ((PolyTimeFun.reverse.comp fst).pair snd))
    (fun z => z.1.foldr (fun c a => xorBits (mulReduce z.2.1 a z.2.2.1) c) z.2.2.2)
    (by
      rintro ⟨l, p, x, a⟩
      change (l.reverse.foldl hornerStep (p, x, a)).2.2 = _
      rw [fold_hornerStep_acc]
      exact List.foldr_eq_foldl_reverse.symm)

/-- One ambient program, uniform in both field width and coefficient count. -/
def shoupHornerProg : PolyTimeFun (Unary × BitStr × List BitStr) BitStr :=
  hornerFoldProg.comp ((snd.comp snd).pair
    ((shoupLowerCoeffs.comp fst).pair
      ((fst.comp snd).pair (shoupZeroProg.comp fst))))

end MIPRE.Introspection.FieldPolynomialProgram
end


