-- Prove2me | Definitions.Def_MIPRE_Background_QLD_PauliBooleanPrograms
-- name    : MIPRE_Background_QLD_PauliBooleanPrograms
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T06:52:02.040563+00:00
-- url     : https://prove2.me/theorems/5cbefd0b-8972-4130-852a-60e5afd99b5b
-- title:
--   Definitions of PauliBooleanPrograms: The uniform Boolean Pauli decision program Both answers undergo the exact type-directed parser
-- statement:
--   The definitions of the module `MIPRE.Background.QLD.PauliBooleanPrograms` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The uniform Boolean Pauli decision program. Both answers undergo the exact type-directed parser. A faithful finite type route chooses consistency or one of the seven arithmetic rules. The finite Magic Square metadata contains only type indices; field arithmetic, answer tables and polynomial coefficients are processed by uniform programs.
--
--   **Definitions** (50): `MIPRE.QLD.PauliBooleanProgram.Input`; `MIPRE.QLD.PauliBooleanProgram.Payload`; `MIPRE.QLD.PauliBooleanProgram.axis`; `MIPRE.QLD.PauliBooleanProgram.axisCheck`; `MIPRE.QLD.PauliBooleanProgram.basis`; `MIPRE.QLD.PauliBooleanProgram.bitAt`; `MIPRE.QLD.PauliBooleanProgram.boolAnd`; `MIPRE.QLD.PauliBooleanProgram.boolEq`; `MIPRE.QLD.PauliBooleanProgram.boolNot`; `MIPRE.QLD.PauliBooleanProgram.boolOr`; `MIPRE.QLD.PauliBooleanProgram.checks`; `MIPRE.QLD.PauliBooleanProgram.consistency`; `MIPRE.QLD.PauliBooleanProgram.diagonalCheck`; `MIPRE.QLD.PauliBooleanProgram.dim`; `MIPRE.QLD.PauliBooleanProgram.endpointTypes`; `MIPRE.QLD.PauliBooleanProgram.endpoints`; `MIPRE.QLD.PauliBooleanProgram.gamma` (All commutation and Magic Square rules use the omega tuple at the right, distinguished endpoint after the orientation normalization.); `MIPRE.QLD.PauliBooleanProgram.left`; `MIPRE.QLD.PauliBooleanProgram.leftBit`; `MIPRE.QLD.PauliBooleanProgram.leftBits`; `MIPRE.QLD.PauliBooleanProgram.leftFields`; `MIPRE.QLD.PauliBooleanProgram.leftParity`; `MIPRE.QLD.PauliBooleanProgram.leftParser`; `MIPRE.QLD.PauliBooleanProgram.leftRows`; `MIPRE.QLD.PauliBooleanProgram.leftValue`; `MIPRE.QLD.PauliBooleanProgram.magicCheck`; `MIPRE.QLD.PauliBooleanProgram.magicInfo`; `MIPRE.QLD.PauliBooleanProgram.magicMetadata`; `MIPRE.QLD.PauliBooleanProgram.magicProbeCheck`; `MIPRE.QLD.PauliBooleanProgram.magicTypes`; `MIPRE.QLD.PauliBooleanProgram.oriented`; `MIPRE.QLD.PauliBooleanProgram.origin`; and 18 more.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.QLD.PauliBooleanPrograms` (`MIPRE/Background/QLD/PauliBooleanPrograms.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 184 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/QLD/PauliBooleanPrograms.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/PauliBooleanPrograms.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Rotate
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
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
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_CL_Downsize
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
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgFinite
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgParse
import Definitions.Def_MIPRE_Foundations_SAT_BasisTransport
import Definitions.Def_MIPRE_Foundations_SAT_EffectiveSelfDual
import Definitions.Def_MIPRE_Foundations_SAT_EffectiveNormalBasis
import Definitions.Def_MIPRE_Foundations_Introspection_BasisProg
import Definitions.Def_MIPRE_Foundations_Introspection_BinaryBlockProg
import Definitions.Def_MIPRE_Foundations_Introspection_BinaryBlockProg_B
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Geometry
import Definitions.Def_MIPRE_Foundations_CL_DetypingQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCall
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgRoute
import Definitions.Def_MIPRE_Foundations_Introspection_FieldPolynomialProg
import Definitions.Def_MIPRE_Foundations_Introspection_FieldLineCheckProg
import Definitions.Def_MIPRE_Foundations_Introspection_PauliStageProg
import Definitions.Def_MIPRE_Foundations_Introspection_PauliStageProg_B
import Definitions.Def_MIPRE_Foundations_Introspection_FieldQuestionProg
import Definitions.Def_MIPRE_Foundations_Cost_SizeProgram
import Definitions.Def_MIPRE_Foundations_SAT_PcpFormat
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderRoute
import Definitions.Def_MIPRE_Foundations_Introspection_ParserBits
import Definitions.Def_MIPRE_Foundations_Introspection_ParserAnswers
import Definitions.Def_MIPRE_Foundations_Introspection_DynamicParserSlice
import Definitions.Def_MIPRE_LCS_Basic
import Definitions.Def_MIPRE_LCS_Common
import Definitions.Def_MIPRE_LCS_Measurement
import Definitions.Def_MIPRE_LCS_Observable
import Definitions.Def_MIPRE_LCS_Strategy_ObservableToProjector
import Definitions.Def_MIPRE_LCS_NonlocalGame
import Definitions.Def_MIPRE_LCS_Pauli
import Definitions.Def_MIPRE_LCS_MagicSquare_Strategy
import Definitions.Def_MIPRE_LCS_MagicSquare_Game
import Definitions.Def_MIPRE_Background_QLD_Game
import Definitions.Def_MIPRE_Background_QLD_CLPresentation
import Definitions.Def_MIPRE_Background_QLD_CLBinary
import Definitions.Def_MIPRE_Background_QLD_CLExplicitSeed
import Definitions.Def_MIPRE_Background_QLD_PauliStagePrograms
import Definitions.Def_MIPRE_Background_QLD_TypeEncoding
import Definitions.Def_MIPRE_Foundations_Introspection_FieldAnswerParserProg
import Definitions.Def_MIPRE_Background_QLD_PauliAnswerPrograms
import Definitions.Def_MIPRE_Foundations_Introspection_FieldIndicatorProg
import Definitions.Def_MIPRE_Foundations_Introspection_FieldTableProg
import Definitions.Def_MIPRE_Background_QLD_PauliAnswerCoding
import Definitions.Def_MIPRE_Background_QLD_PauliBranchPrograms
import Definitions.Def_MIPRE_Foundations_Introspection_FieldGammaProg
import Definitions.Def_MIPRE_Background_QLD_PauliArithmeticPrograms

/-! # The uniform Boolean Pauli decision program

Both answers undergo the exact type-directed parser. A faithful finite type
route chooses consistency or one of the seven arithmetic rules. The finite
Magic Square metadata contains only type indices; field arithmetic, answer
tables and polynomial coefficients are processed by uniform programs.
-/

noncomputable section
namespace MIPRE.QLD.PauliBooleanProgram
open Cost Cost.PolyTimeFun SAT LowDegree LowDegree.BinaryLinear Introspection.PauliStageProgram Introspection.FieldLineCheck Introspection.FieldGammaProgram PauliArithmeticProgram
open LCS.MagicSquare

abbrev Payload := Ty × Fields × BitStr
abbrev Input := Parameters × Payload × Payload

def params : PolyTimeFun Input Parameters := fst
def width : PolyTimeFun Input Unary := fst.comp params
def dim : PolyTimeFun Input Unary := snd.comp (snd.comp params)
def endpoints : PolyTimeFun Input (Payload × Payload) := snd
def endpointTypes : PolyTimeFun Input (Ty × Ty) :=
  (fst.comp (fst.comp endpoints)).pair (fst.comp (snd.comp endpoints))
def route : PolyTimeFun Input PauliBranchProgram.Route :=
  PauliBranchProgram.routeProg.comp endpointTypes
def basis : PolyTimeFun Input ℕ := fst.comp (snd.comp (snd.comp route))
def oriented : PolyTimeFun Input (Payload × Payload) :=
  PauliBranchProgram.orientProg.comp ((fst.comp (snd.comp route)).pair endpoints)
def left : PolyTimeFun Input Payload := fst.comp oriented
def right : PolyTimeFun Input Payload := snd.comp oriented
def leftFields : PolyTimeFun Input Fields := fst.comp (snd.comp left)
def rightFields : PolyTimeFun Input Fields := fst.comp (snd.comp right)
def leftBits : PolyTimeFun Input BitStr := snd.comp (snd.comp left)
def rightBits : PolyTimeFun Input BitStr := snd.comp (snd.comp right)
def leftParser : PolyTimeFun Input (Bool × List BitStr) :=
  PauliAnswerProgram.parser.comp ((fst.comp left).pair
    (dim.pair (width.pair ((const (unary 1)).pair leftBits))))
def rightParser : PolyTimeFun Input (Bool × List BitStr) :=
  PauliAnswerProgram.parser.comp ((fst.comp right).pair
    (dim.pair (width.pair ((const (unary 1)).pair rightBits))))
def leftRows : PolyTimeFun Input (List BitStr) := snd.comp leftParser
def rightRows : PolyTimeFun Input (List BitStr) := snd.comp rightParser
def leftValue : PolyTimeFun Input BitStr := (nthD [] 0).comp leftRows

def bitAt : PolyTimeFun (ℕ × List BitStr) Bool :=
  (nthD false 0).comp (ArrayProg.getD [])

def boolEq : PolyTimeFun (Bool × Bool) Bool := finiteFunction (fun p => p.1 == p.2)
def boolAnd : PolyTimeFun (Bool × Bool) Bool := finiteFunction (fun p => p.1 && p.2)
def boolOr : PolyTimeFun (Bool × Bool) Bool := finiteFunction (fun p => p.1 || p.2)
def boolNot : PolyTimeFun Bool Bool := finiteFunction (! ·)

def point : PolyTimeFun Input (List BitStr) :=
  Introspection.FieldQuestionProgram.selectedPoint.comp (basis.pair leftFields)
def origin : PolyTimeFun Input (List BitStr) :=
  Introspection.FieldQuestionProgram.selectedPoint.comp (basis.pair rightFields)
def scalar : PolyTimeFun Input BitStr :=
  Introspection.FieldQuestionProgram.selectedScalar.comp (basis.pair rightFields)
def axis : PolyTimeFun Input (List BitStr) :=
  Introspection.FieldQuestionProgram.axisDirectionProg.comp
    (params.pair (seed.comp rightFields))

def consistency : PolyTimeFun Input Bool := ap₂ ArrayProg.eqBits leftBits rightBits
def axisCheck : PolyTimeFun Input Bool :=
  lineCheckProg.comp ((width.pair (origin.pair (axis.pair point))).pair
    (rightRows.pair leftValue))
def diagonalCheck : PolyTimeFun Input Bool :=
  lineCheckProg.comp ((width.pair (origin.pair ((direction.comp rightFields).pair point))).pair
    (rightRows.pair leftValue))
def tableCheck : PolyTimeFun Input Bool :=
  fullAnswerCheckProg.comp ((width.pair (point.pair rightRows)).pair leftValue)

/-- All commutation and Magic Square rules use the omega tuple at the right,
distinguished endpoint after the orientation normalization. -/
def gamma : PolyTimeFun Input Bool :=
  gammaProg.comp (width.pair
    ((zip.comp ((pointX.comp rightFields).pair (pointZ.comp rightFields))).pair
      ((scalarX.comp rightFields).pair (scalarZ.comp rightFields))))
def probe : PolyTimeFun Input Bool :=
  probeProg.comp (width.pair (leftValue.pair scalar))
def leftBit : PolyTimeFun Input Bool := bitAt.comp ((const 0).pair leftRows)
def rightBit : PolyTimeFun Input Bool := bitAt.comp ((const 0).pair rightRows)

def pairCheck : PolyTimeFun Input Bool :=
  ap₂ boolOr gamma (ap₂ boolEq leftBit (bitAt.comp (basis.pair rightRows)))
def probeCheck : PolyTimeFun Input Bool := ap₂ boolOr gamma (ap₂ boolEq probe rightBit)

def magicInfo : Ty × Ty → Bool × Bool × ℕ
  | (.con i, .var j) => (decide (j ∈ layout.V i), bit (game.b i), (cellIdx i j).val)
  | _ => (false, false, 0)

def magicTypes : PolyTimeFun Input (Ty × Ty) := (fst.comp left).pair (fst.comp right)
def magicMetadata : PolyTimeFun Input (Bool × Bool × ℕ) :=
  (finiteFunction magicInfo).comp magicTypes
def parityProg : PolyTimeFun (Bool × Bool × Bool) Bool :=
  finiteFunction (fun p => bit ((ofBool p.1 : ZMod 2) + ofBool p.2.1 + ofBool p.2.2))
def leftParity : PolyTimeFun Input Bool :=
  parityProg.comp ((bitAt.comp ((const 0).pair leftRows)).pair
    ((bitAt.comp ((const 1).pair leftRows)).pair (bitAt.comp ((const 2).pair leftRows))))
def magicCheck : PolyTimeFun Input Bool :=
  ap₂ boolOr (boolNot.comp gamma)
    (ap₂ boolAnd (fst.comp magicMetadata)
      (ap₂ boolAnd (ap₂ boolEq leftParity (fst.comp (snd.comp magicMetadata)))
        (ap₂ boolEq (bitAt.comp ((snd.comp (snd.comp magicMetadata)).pair leftRows)) rightBit)))

def probeEligible : Ty × Ty → Bool
  | (.point .X, .var j) => decide (j = v 0)
  | (.point .Z, .var j) => decide (j = v 4)
  | _ => false

def magicProbeCheck : PolyTimeFun Input Bool :=
  ap₂ boolOr (boolNot.comp gamma)
    (ap₂ boolAnd ((finiteFunction probeEligible).comp magicTypes) (ap₂ boolEq probe rightBit))

def checks : PolyTimeFun Input (List Bool) :=
  cons consistency (cons axisCheck (cons diagonalCheck (cons tableCheck
    (cons pairCheck (cons probeCheck (cons magicCheck (cons magicProbeCheck (const []))))))))

def program : PolyTimeFun Input Bool :=
  PauliBranchProgram.formatGuard.comp ((fst.comp leftParser).pair
    ((fst.comp rightParser).pair (PauliBranchProgram.selectProg.comp (route.pair checks))))

end MIPRE.QLD.PauliBooleanProgram
end


