-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_FieldLineCheckProg
-- name    : MIPRE_Foundations_Introspection_FieldLineCheckProg
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T05:33:24.640803+00:00
-- url     : https://prove2.me/theorems/9ce3e03e-2e69-471b-823e-50d73e27b6c8
-- title:
--   Definitions of FieldLineCheckProg: Executable line-versus-point arithmetic The program finds the first nonzero direction coordinate, checks membership in…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.FieldLineCheckProg` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Executable line-versus-point arithmetic. The program finds the first nonzero direction coordinate, checks membership in the affine line, and evaluates the supplied polynomial at that parameter. The zero direction denotes a singleton line and has parameter zero.
--
--   **Definitions** (7): `MIPRE.Introspection.FieldLineCheck.affineProg`; `MIPRE.Introspection.FieldLineCheck.lineCheckProg` (The geometric line input, polynomial coefficients, and claimed point value.); `MIPRE.Introspection.FieldLineCheck.memberProg`; `MIPRE.Introspection.FieldLineCheck.parameter` (The canonical scalar parameter, including singleton lines.); `MIPRE.Introspection.FieldLineCheck.parameterProg` (Width, origin, direction, and point.); `MIPRE.Introspection.FieldLineCheck.subtractProg`; `_private.MIPRE.Foundations.Introspection.FieldLineCheckProg.0.MIPRE.Introspection.FieldLineCheck.affineEntryProg`.
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `firstPair_zero`, `vecBits_injective`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.FieldLineCheckProg` (`MIPRE/Foundations/Introspection/FieldLineCheckProg.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 96 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/FieldLineCheckProg.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/FieldLineCheckProg.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryFold
import Definitions.Def_MIPRE_Foundations_SAT_NormalElementProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryInverse
import Definitions.Def_MIPRE_Foundations_Introspection_LineRepresentativeProg
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgFinite
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgParse
import Definitions.Def_MIPRE_Foundations_Introspection_FieldPolynomialProg
import Theorems.Thm_MIPRE_Cost_encode_injective

/-! # Executable line-versus-point arithmetic

The program finds the first nonzero direction coordinate, checks membership
in the affine line, and evaluates the supplied polynomial at that parameter.
The zero direction denotes a singleton line and has parameter zero.
-/

noncomputable section
namespace MIPRE.Introspection.FieldLineCheck
open Cost Cost.PolyTimeFun SAT LowDegree.BinaryPolynomial LineProgram FieldPolynomialProgram CL.Detyping.Program

theorem firstPair_zero {F : Type*} [Zero F] [DecidableEq F]
    (l : List (F × F)) (h : ∀ p ∈ l, p.2 = 0) : firstPair l = (0, 0) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ha := h a (by simp)
    have hl : ∀ p ∈ l, p.2 = 0 := fun p hp => h p (by simp [hp])
    simpa [firstPair, ha] using ih hl

/-- The canonical scalar parameter, including singleton lines. -/
def parameter {F : Type*} [Field F] [DecidableEq F] {m : ℕ}
    (origin direction point : Fin m → F) : F :=
  coefficient (List.ofFn fun i => (point i - origin i, direction i))

def subtractProg : PolyTimeFun (List BitStr × List BitStr) (List BitStr) :=
  (map xorBitsProg).comp zip

/-- Width, origin, direction, and point. -/
def parameterProg : PolyTimeFun (Unary × List BitStr × List BitStr × List BitStr) BitStr :=
  let origin := fst.comp snd
  let direction := fst.comp (snd.comp snd)
  let point := snd.comp (snd.comp snd)
  let differences := subtractProg.comp (point.pair origin)
  coefficientBitsProg.comp (fst.pair (zip.comp (differences.pair direction)))

def affineEntryProg : PolyTimeFun ((BitStr × BitStr) × Unary × BitStr) BitStr :=
  xorBitsProg.comp ((fst.comp fst).pair
    (shoupMulProg.comp ((fst.comp snd).pair ((snd.comp snd).pair (snd.comp fst)))))

def affineProg : PolyTimeFun (Unary × BitStr × List BitStr × List BitStr) (List BitStr) :=
  (mapWith affineEntryProg).comp
    ((zip.comp (snd.comp snd)).pair (fst.pair (fst.comp snd)))

theorem vecBits_injective {k m : ℕ} (E : BinField k) :
    Function.Injective (E.vecBits : (Fin m → E.carrier) → List BitStr) := by
  intro x y h
  simp only [BinField.vecBits, List.map_ofFn] at h
  have he := List.ofFn_injective h
  funext i
  have hi := congrArg (fun f => E.ofBits (f i)) he
  simpa only [Function.comp_apply, E.ofBits_toBits] using hi

def memberProg : PolyTimeFun (Unary × List BitStr × List BitStr × List BitStr) Bool :=
  let expected := affineProg.comp
    (fst.pair (parameterProg.pair ((fst.comp snd).pair (fst.comp (snd.comp snd)))))
  treeEq.comp ((encoded.comp (snd.comp (snd.comp snd))).pair (encoded.comp expected))

/-- The geometric line input, polynomial coefficients, and claimed point value. -/
def lineCheckProg : PolyTimeFun
    ((Unary × List BitStr × List BitStr × List BitStr) × List BitStr × BitStr) Bool :=
  let evaluated := shoupHornerProg.comp
    ((fst.comp fst).pair ((parameterProg.comp fst).pair (fst.comp snd)))
  ite (memberProg.comp fst)
    (ArrayProg.eqBits.comp (evaluated.pair (snd.comp snd))) (const false)

end MIPRE.Introspection.FieldLineCheck
end


