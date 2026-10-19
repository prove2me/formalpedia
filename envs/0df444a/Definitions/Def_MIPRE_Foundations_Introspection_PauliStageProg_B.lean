-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_PauliStageProg_B
-- name    : MIPRE_Foundations_Introspection_PauliStageProg_B
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T06:22:08.320708+00:00
-- url     : https://prove2.me/theorems/077a10b4-a54e-481b-a706-c6cf1a6b3cfb
-- title:
--   Definitions of PauliStageProg (addendum): Uniform programs for all three Pauli sampling stages The field width, selector width and point dimension are inputs, as…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.PauliStageProg` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Uniform programs for all three Pauli sampling stages. The field width, selector width and point dimension are inputs, as are the type tag, prefix and vector. The five computational branches cover point, axis line, diagonal line, Pauli and the remaining Pauli-test types. In particular, neither a finite table of field elements nor a dimension-dependent program is used.
--
--   This bundle **adds** the declarations below to the already published bundle `MIPRE_Foundations_Introspection_PauliStageProg` of the same module, which the new statements of this upload need and the earlier bundle left out.
--
--   **Definitions** (30): `MIPRE.Introspection.PauliStageProgram.Input`; `MIPRE.Introspection.PauliStageProgram.Parameters`; `MIPRE.Introspection.PauliStageProgram.Tag` (Kind and basis: `0` point, `1` axis, `2` diagonal, `3` Pauli, `4` full.); `MIPRE.Introspection.PauliStageProgram.allThree`; `MIPRE.Introspection.PauliStageProgram.assemble` (Assemble three disjoint output registers without performing field arithmetic.); `MIPRE.Introspection.PauliStageProgram.basis`; `MIPRE.Introspection.PauliStageProgram.dimension`; `MIPRE.Introspection.PauliStageProgram.direction`; `MIPRE.Introspection.PauliStageProgram.fieldWidth`; `MIPRE.Introspection.PauliStageProgram.finalPoint`; `MIPRE.Introspection.PauliStageProgram.firstTwo`; `MIPRE.Introspection.PauliStageProgram.fullFields`; `MIPRE.Introspection.PauliStageProgram.isKind`; `MIPRE.Introspection.PauliStageProgram.kind`; `MIPRE.Introspection.PauliStageProgram.linear` (A single program selects the requested stage; out-of-range stages return zero.); `MIPRE.Introspection.PauliStageProgram.marginal` (Uniform evaluation of each legal marginal, including both prefix-dependent stages.); `MIPRE.Introspection.PauliStageProgram.pack`; `MIPRE.Introspection.PauliStageProgram.pointFields`; `MIPRE.Introspection.PauliStageProgram.prefixData`; `MIPRE.Introspection.PauliStageProgram.seed`; `MIPRE.Introspection.PauliStageProgram.selectedPoint`; `MIPRE.Introspection.PauliStageProgram.selectorWidth`; `MIPRE.Introspection.PauliStageProgram.stageOne`; and 2 more.
--
--   **Embedded lemmas** (6): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `linear_one`, `linear_three`, `linear_two`, `marginal_one`, `marginal_three`, `marginal_two`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.PauliStageProg` (`MIPRE/Foundations/Introspection/PauliStageProg.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 117 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/PauliStageProg.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/PauliStageProg.lean (delta bundle: declarations the new statements need that the published bundle Def_MIPRE_Foundations_Introspection_PauliStageProg does not carry);
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryTrace
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasis
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixInverse
import Definitions.Def_MIPRE_Foundations_LowDegree_SelfDualize
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySquareRoot
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCirculant
import Definitions.Def_MIPRE_Foundations_Cost_Iterates
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCirculantProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCirculantProg_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryKernel
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGroupAlgebra
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGroupAlgebra_B
import Definitions.Def_MIPRE_Foundations_LowDegree_FiniteReducedComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_IdempotentSplit
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponents_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponentsProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponentsProg_B
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
import Definitions.Def_MIPRE_Foundations_SAT_FieldTrace_B
import Definitions.Def_MIPRE_Foundations_SAT_FieldCoordinates
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Introspection_SeedSelectorProg
import Definitions.Def_MIPRE_Foundations_SAT_TraceGram
import Definitions.Def_MIPRE_Foundations_LowDegree_SelfDual
import Definitions.Def_MIPRE_Foundations_LowDegree_NormalBasis
import Definitions.Def_MIPRE_Foundations_SAT_NormalGram
import Definitions.Def_MIPRE_Foundations_SAT_FrobeniusAction
import Definitions.Def_MIPRE_Foundations_SAT_NormalElement
import Definitions.Def_MIPRE_Foundations_SAT_FrobeniusMatrix
import Definitions.Def_MIPRE_Foundations_SAT_FrobeniusActionProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryFold
import Definitions.Def_MIPRE_Foundations_SAT_NormalElementProg
import Definitions.Def_MIPRE_Foundations_SAT_NormalElementProg_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryInverse
import Definitions.Def_MIPRE_Foundations_Introspection_LineRepresentativeProg
import Definitions.Def_MIPRE_Foundations_Cost_BinaryCompare
import Definitions.Def_MIPRE_Foundations_Introspection_SeededLineProg
import Definitions.Def_MIPRE_Foundations_Introspection_PauliStageProg

/-! # Uniform programs for all three Pauli sampling stages

The field width, selector width and point dimension are inputs, as are the
type tag, prefix and vector. The five computational branches cover point,
axis line, diagonal line, Pauli and the remaining Pauli-test types. In
particular, neither a finite table of field elements nor a dimension-dependent
program is used.
-/

noncomputable section
namespace MIPRE.Introspection.PauliStageProgram
open Cost Cost.PolyTimeFun SAT SeededLineProgram LineProgram

abbrev Parameters := Unary × Unary × Unary
/-- Kind and basis: `0` point, `1` axis, `2` diagonal, `3` Pauli, `4` full. -/
abbrev Tag := ℕ × Bool
abbrev Input := Parameters × Tag × Fields × Fields

def fieldWidth : PolyTimeFun Input Unary := fst.comp fst
def selectorWidth : PolyTimeFun Input Unary := fst.comp (snd.comp fst)
def dimension : PolyTimeFun Input Unary := snd.comp (snd.comp fst)
def kind : PolyTimeFun Input ℕ := fst.comp (fst.comp snd)
def basis : PolyTimeFun Input Bool := snd.comp (fst.comp snd)
def prefixData : PolyTimeFun Input Fields := fst.comp (snd.comp snd)
def vector : PolyTimeFun Input Fields := snd.comp (snd.comp snd)

def seed : PolyTimeFun Fields BitStr := fst.comp (snd.comp snd)
def direction : PolyTimeFun Fields (List BitStr) := fst.comp (snd.comp (snd.comp snd))

def zeroField : PolyTimeFun Input BitStr := shoupZeroProg.comp fieldWidth
def zeroPoint : PolyTimeFun Input (List BitStr) := ap₂ replicate dimension zeroField
def pack {A : Type*} [SizedEncoding A]
    (x z : PolyTimeFun A (List BitStr)) (s : PolyTimeFun A BitStr)
    (v : PolyTimeFun A (List BitStr)) (rx rz : PolyTimeFun A BitStr) :
    PolyTimeFun A Fields := x.pair (z.pair (s.pair (v.pair (rx.pair rz))))
def zeros : PolyTimeFun Input Fields :=
  pack zeroPoint zeroPoint zeroField zeroPoint zeroField zeroField
def isKind (t : ℕ) : PolyTimeFun Input Bool := ap₂ ArrayProg.eqNat kind (const t)

def stageOne : PolyTimeFun Input Fields :=
  let s := ite (isKind 1) (seed.comp vector)
    (ite (isKind 2) (seed.comp vector) zeroField)
  pack zeroPoint zeroPoint s zeroPoint zeroField zeroField

def stageTwo : PolyTimeFun Input Fields :=
  let v := ite (isKind 2)
    (selectedDirectionProg.comp
      ((fieldWidth.pair (selectorWidth.pair (seed.comp prefixData))).pair (direction.comp vector)))
    zeroPoint
  pack zeroPoint zeroPoint zeroField v zeroField zeroField

def selectedPoint : PolyTimeFun Input (List BitStr) :=
  ite basis (pointZ.comp vector) (pointX.comp vector)

def finalPoint : PolyTimeFun Input (List BitStr) :=
  ite (isKind 1)
    (axisRepresentativeProg.comp
      ((fieldWidth.pair (selectorWidth.pair (seed.comp prefixData))).pair selectedPoint))
    (ite (isKind 2)
      (lineRepresentativeProg.comp
        (fieldWidth.pair (selectedPoint.pair (direction.comp prefixData)))) selectedPoint)

def pointFields : PolyTimeFun Input Fields :=
  pack (ite basis zeroPoint finalPoint) (ite basis finalPoint zeroPoint)
    zeroField zeroPoint zeroField zeroField

def fullFields : PolyTimeFun Input Fields :=
  pack (pointX.comp vector) (pointZ.comp vector) zeroField zeroPoint
    (scalarX.comp vector) (scalarZ.comp vector)

def stageThree : PolyTimeFun Input Fields :=
  ite (isKind 0) pointFields
    (ite (isKind 1) pointFields
      (ite (isKind 2) pointFields (ite (isKind 3) zeros fullFields)))

/-- A single program selects the requested stage; out-of-range stages return zero. -/
def linear : PolyTimeFun (ℕ × Input) Fields :=
  ite (ap₂ ArrayProg.eqNat fst (const 1)) (stageOne.comp snd)
    (ite (ap₂ ArrayProg.eqNat fst (const 2)) (stageTwo.comp snd)
      (ite (ap₂ ArrayProg.eqNat fst (const 3)) (stageThree.comp snd) (zeros.comp snd)))

@[simp] theorem linear_one (x : Input) : linear (1, x) = stageOne x := rfl
@[simp] theorem linear_two (x : Input) : linear (2, x) = stageTwo x := rfl
@[simp] theorem linear_three (x : Input) : linear (3, x) = stageThree x := rfl

/-- Assemble three disjoint output registers without performing field arithmetic. -/
def assemble : PolyTimeFun (Fields × Fields × Fields) Fields :=
  pack (pointX.comp (snd.comp snd)) (pointZ.comp (snd.comp snd)) (seed.comp fst)
    (direction.comp (fst.comp snd)) (scalarX.comp (snd.comp snd))
    (scalarZ.comp (snd.comp snd))

def withPrefix : PolyTimeFun (Input × Fields) Input :=
  (fst.comp fst).pair ((fst.comp (snd.comp fst)).pair
    (snd.pair (vector.comp fst)))

def firstTwo : PolyTimeFun Input Fields :=
  let a := stageOne
  let b := stageTwo.comp (withPrefix.comp ((PolyTimeFun.id _).pair a))
  assemble.comp (a.pair (b.pair zeros))

def allThree : PolyTimeFun Input Fields :=
  let c := stageThree.comp (withPrefix.comp ((PolyTimeFun.id _).pair firstTwo))
  assemble.comp (firstTwo.pair (firstTwo.pair c))

/-- Uniform evaluation of each legal marginal, including both prefix-dependent stages. -/
def marginal : PolyTimeFun (ℕ × Input) Fields :=
  ite (ap₂ ArrayProg.eqNat fst (const 1)) (stageOne.comp snd)
    (ite (ap₂ ArrayProg.eqNat fst (const 2)) (firstTwo.comp snd)
      (ite (ap₂ ArrayProg.eqNat fst (const 3)) (allThree.comp snd) (zeros.comp snd)))

@[simp] theorem marginal_one (x : Input) : marginal (1, x) = stageOne x := rfl
@[simp] theorem marginal_two (x : Input) : marginal (2, x) = firstTwo x := rfl
@[simp] theorem marginal_three (x : Input) : marginal (3, x) = allThree x := rfl

end MIPRE.Introspection.PauliStageProgram
end


