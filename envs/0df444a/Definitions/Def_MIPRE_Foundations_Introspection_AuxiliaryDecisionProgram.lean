-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryDecisionProgram
-- name    : MIPRE_Foundations_Introspection_AuxiliaryDecisionProgram
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T03:18:39.435644+00:00
-- url     : https://prove2.me/theorems/5bb9a40d-65e3-4041-85d7-9b5e380494c1
-- title:
--   Definitions of AuxiliaryDecisionProgram: The uniform auxiliary decision kernel The finite type labels choose programs, including the fixed-depth hiding scans
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.AuxiliaryDecisionProgram` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The uniform auxiliary decision kernel. The finite type labels choose programs, including the fixed-depth hiding scans. Source descriptions, the shared unary clock, dimensions and answer bytes remain runtime data. Pauli arithmetic and conversion are supplied by their separately verified uniform programs.
--
--   **Definitions** (33): `MIPRE.Introspection.AuxiliaryDecision.Bounds`; `MIPRE.Introspection.AuxiliaryDecision.Endpoint`; `MIPRE.Introspection.AuxiliaryDecision.Input`; `MIPRE.Introspection.AuxiliaryDecision.Parameters`; `MIPRE.Introspection.AuxiliaryDecision.bounds`; `MIPRE.Introspection.AuxiliaryDecision.branch`; `MIPRE.Introspection.AuxiliaryDecision.check` (Both orientations and exact same-type byte consistency are checked.); `MIPRE.Introspection.AuxiliaryDecision.context`; `MIPRE.Introspection.AuxiliaryDecision.contextWith` (Replace the player's role while retaining the common clock and source.); `MIPRE.Introspection.AuxiliaryDecision.directed` (The complete directed auxiliary program, including the source game call.); `MIPRE.Introspection.AuxiliaryDecision.format`; `MIPRE.Introspection.AuxiliaryDecision.formatBranch`; `MIPRE.Introspection.AuxiliaryDecision.formatKind` (Pauli format validation is delegated to its field-aware parser.); `MIPRE.Introspection.AuxiliaryDecision.guardFields`; `MIPRE.Introspection.AuxiliaryDecision.left`; `MIPRE.Introspection.AuxiliaryDecision.leftBits`; `MIPRE.Introspection.AuxiliaryDecision.leftTriple`; `MIPRE.Introspection.AuxiliaryDecision.leftType`; `MIPRE.Introspection.AuxiliaryDecision.metadata`; `MIPRE.Introspection.AuxiliaryDecision.nextBranch`; `MIPRE.Introspection.AuxiliaryDecision.originalBound`; `MIPRE.Introspection.AuxiliaryDecision.pauliParameters`; `MIPRE.Introspection.AuxiliaryDecision.right`; `MIPRE.Introspection.AuxiliaryDecision.rightBits`; and 9 more.
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `swap_apply`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.AuxiliaryDecisionProgram` (`MIPRE/Foundations/Introspection/AuxiliaryDecisionProgram.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 185 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/AuxiliaryDecisionProgram.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AuxiliaryDecisionProgram.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Computability.Primrec.List
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_Expanded
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Definitions.Def_MIPRE_Foundations_Linearity
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_Pasting
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_CL_TypedSampler
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
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Cost_BinaryCompare
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgFinite
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgParse
import Definitions.Def_MIPRE_Foundations_CL_DetypingQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCall
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgRoute
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Cost_FiniteEncoding
import Definitions.Def_MIPRE_Foundations_Cost_FiniteChoice
import Definitions.Def_MIPRE_Foundations_Halting_Lists_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Halting_Arith_B
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Pipeline_Budget
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgSampler
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCost
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderRoute
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderProg
import Definitions.Def_MIPRE_Foundations_CL_DetypingClock
import Definitions.Def_MIPRE_Foundations_Pipeline_Introspection
import Definitions.Def_MIPRE_Foundations_Halting_PolyBounded
import Definitions.Def_MIPRE_Foundations_Introspection_ClockArithmetic
import Definitions.Def_MIPRE_Foundations_Introspection_ParserBits
import Definitions.Def_MIPRE_Foundations_Introspection_ParserAnswers
import Definitions.Def_MIPRE_Foundations_Introspection_DynamicParserSlice
import Definitions.Def_MIPRE_Foundations_Introspection_DynamicParser
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompilerParams
import Definitions.Def_MIPRE_Foundations_Introspection_Clock
import Definitions.Def_MIPRE_Foundations_Introspection_ClockCost
import Definitions.Def_MIPRE_Foundations_Introspection_ClockSimulation
import Definitions.Def_MIPRE_Foundations_Introspection_ClockCompiler
import Definitions.Def_MIPRE_Foundations_Introspection_ClockSimulationCost
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompilerParamsCost
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompilerGuard
import Definitions.Def_MIPRE_Foundations_Introspection_ParserGuard
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompiler
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompilerCost
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Foundations_Introspection_Types
import Definitions.Def_MIPRE_Foundations_Introspection_SamplingPrefix
import Definitions.Def_MIPRE_Foundations_Introspection_TwirlDistance
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement
import Definitions.Def_MIPRE_Foundations_Introspection_CommutatorParseval
import Definitions.Def_MIPRE_Foundations_Introspection_BlockTwirl
import Definitions.Def_MIPRE_Foundations_Introspection_BlockPOVM
import Definitions.Def_MIPRE_Foundations_Introspection_EPR
import Definitions.Def_MIPRE_Foundations_Introspection_BlockRetention
import Definitions.Def_MIPRE_Foundations_Introspection_PauliMixing
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterTransport
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterEPR
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterMixing
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterCoordinates
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryChecks
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPredicate
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryReadProgram
import Definitions.Def_MIPRE_Foundations_Introspection_ClockedQueryProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliarySamplingProgram
import Definitions.Def_MIPRE_Foundations_Introspection_Readout
import Definitions.Def_MIPRE_Foundations_Introspection_FinalExtraction
import Definitions.Def_MIPRE_Foundations_Introspection_TypeGraph
import Definitions.Def_MIPRE_Foundations_Introspection_HonestCore
import Definitions.Def_MIPRE_Foundations_Introspection_SourcePadding
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryRegisterBits
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliarySamplingCorrect
import Definitions.Def_MIPRE_Foundations_Introspection_ClockedSourceChecks
import Definitions.Def_MIPRE_Foundations_Introspection_ConditionalNormalizer
import Definitions.Def_MIPRE_Foundations_Introspection_HonestFirstHide
import Definitions.Def_MIPRE_Foundations_Introspection_HonestAdaptive
import Definitions.Def_MIPRE_Foundations_Introspection_HonestRead
import Definitions.Def_MIPRE_Foundations_Introspection_HonestXCoordinates
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHidingStep
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHiding
import Definitions.Def_MIPRE_Foundations_Introspection_HonestLabelSupport
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPresentation
import Definitions.Def_MIPRE_Foundations_Introspection_TypedEstimates
import Definitions.Def_MIPRE_Foundations_Introspection_HidingRigidity
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHidingChecks
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHidingAcceptance
import Definitions.Def_MIPRE_Foundations_Introspection_HidingMaps
import Definitions.Def_MIPRE_Foundations_Introspection_ConditionalNormalizerIdeal
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixFactor
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPrefixChain
import Definitions.Def_MIPRE_Foundations_Introspection_ReadChainMaps
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveResidual
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryPrefixSolve
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryMaskProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryCanonicalProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryDualProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryDualKernel
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryQuotientProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryDualDecode
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryQuotientChecks
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryHidingCoreProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliarySourceQueries
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryScanStage
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryScanProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryScanCorrect
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryRegisterProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryHidingNextProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryHidingBoundaryProgram
import Definitions.Def_MIPRE_Foundations_Introspection_SourcePaddingQueries
import Definitions.Def_MIPRE_Foundations_Introspection_SourcePaddingQueryProg
import Theorems.Thm_MIPRE_Cost_encode_injective

/-! # The uniform auxiliary decision kernel

The finite type labels choose programs, including the fixed-depth hiding
scans. Source descriptions, the shared unary clock, dimensions and answer
bytes remain runtime data. Pauli arithmetic and conversion are supplied by
their separately verified uniform programs.
-/

noncomputable section
namespace MIPRE.Introspection.AuxiliaryDecision
open Cost Cost.PolyTimeFun AuxiliaryProgram CL.Detyping.Program
variable {P : Type*} [Fintype P] [DecidableEq P] [SizedEncoding P] {ℓ : ℕ}

abbrev Endpoint (P : Type*) (ℓ : ℕ) := QuestionType P ℓ × BitStr
abbrev Parameters := Unary × Unary × Unary
abbrev Bounds := (ℕ × ℕ × ℕ × Prog) × Parameters
abbrev Input (P : Type*) (ℓ : ℕ) :=
  (AuxiliarySource.Context × Bounds) × Endpoint P ℓ × Endpoint P ℓ

def context : PolyTimeFun (Input P ℓ) AuxiliarySource.Context := fst.comp fst
def bounds : PolyTimeFun (Input P ℓ) (ℕ × ℕ × ℕ × Prog) := fst.comp (snd.comp fst)
def pauliParameters : PolyTimeFun (Input P ℓ) Parameters := snd.comp (snd.comp fst)
def width : PolyTimeFun (Input P ℓ) ℕ := fst.comp bounds
def originalBound : PolyTimeFun (Input P ℓ) ℕ := fst.comp (snd.comp bounds)
def sourceDim : PolyTimeFun (Input P ℓ) ℕ := fst.comp (snd.comp (snd.comp bounds))
def sourceDecider : PolyTimeFun (Input P ℓ) Prog := snd.comp (snd.comp (snd.comp bounds))
def left : PolyTimeFun (Input P ℓ) (Endpoint P ℓ) := fst.comp snd
def right : PolyTimeFun (Input P ℓ) (Endpoint P ℓ) := snd.comp snd
def leftType : PolyTimeFun (Input P ℓ) (QuestionType P ℓ) := fst.comp left
def rightType : PolyTimeFun (Input P ℓ) (QuestionType P ℓ) := fst.comp right
def leftBits : PolyTimeFun (Input P ℓ) BitStr := snd.comp left
def rightBits : PolyTimeFun (Input P ℓ) BitStr := snd.comp right
def swap : PolyTimeFun (Input P ℓ) (Input P ℓ) := fst.pair (right.pair left)

omit [Fintype P] [DecidableEq P] in
@[simp] theorem swap_apply (ctx : AuxiliarySource.Context) (b : Bounds)
    (a d : Endpoint P ℓ) : swap ((ctx,b),a,d) = ((ctx,b),d,a) := rfl

def rightPair : PolyTimeFun (Input P ℓ) (BitStr × BitStr) :=
  DynamicParser.pairParts.comp (rightBits.pair width)
def leftTriple : PolyTimeFun (Input P ℓ) (BitStr × BitStr × BitStr) :=
  DynamicParser.tripleParts.comp (leftBits.pair width)
def rightTriple : PolyTimeFun (Input P ℓ) (BitStr × BitStr × BitStr) :=
  DynamicParser.tripleParts.comp (rightBits.pair width)

/-- Pauli format validation is delegated to its field-aware parser. -/
def formatKind : QuestionType P ℓ → Fin 4
  | .inl _ => 0
  | .inr (.introspect, _) | .inr (.sample, _) => 1
  | .inr (.read, _) => 2
  | .inr (.hide _, _) => 3

def formatBranch (tag : Fin 4) : PolyTimeFun (Input P ℓ) Bool :=
  match tag.val with
  | 0 => const true
  | 1 => DynamicParser.pairCheck.comp (leftBits.pair (width.pair originalBound))
  | 2 => (DynamicParser.tripleCheck false).comp (leftBits.pair (width.pair originalBound))
  | _ => (DynamicParser.tripleCheck true).comp (leftBits.pair (width.pair width))

def format : PolyTimeFun (Input P ℓ) Bool :=
  choose ((finiteFunction formatKind).comp leftType) formatBranch (const false)

/-- Replace the player's role while retaining the common clock and source. -/
def contextWith (role : PolyTimeFun (Input P ℓ) Bool) :
    PolyTimeFun (Input P ℓ) AuxiliarySource.Context :=
  (AuxiliarySource.budget.comp context).pair ((AuxiliarySource.source.comp context).pair
    ((AuxiliarySource.index.comp context).pair (role.pair
      ((AuxiliarySource.level.comp context).pair (AuxiliarySource.inputPrefix.comp context)))))

def guardFields : PolyTimeFun (Input P ℓ) SourceCompiler.GuardInput :=
  (AuxiliarySource.index.comp context).pair (width.pair (originalBound.pair
    (sourceDim.pair (leftBits.pair rightBits))))

/-- Each directed auxiliary edge has one rule, a role and an optional hiding level. -/
def route (X Z : P) : QuestionType P ℓ × QuestionType P ℓ → Fin 8 × Bool × Option (Fin ℓ)
  | (.inl p, .inr (.sample, w)) => if p = Z then (0,w,none) else (7,w,none)
  | (.inr (.introspect,w), .inr (.sample,v)) => if w = v then (1,w,none) else (7,w,none)
  | (.inr (.introspect,w), .inr (.read,v)) => if w = v then (2,w,none) else (7,w,none)
  | (.inr (.hide k,w), .inr (.read,v)) =>
      if w = v ∧ k.val + 1 = ℓ then (3,w,none) else (7,w,none)
  | (.inr (.hide k,w), .inr (.hide j,v)) =>
      if w = v ∧ k.val + 1 = j.val then (4,w,some k) else (7,w,none)
  | (.inl p, .inr (.hide k,w)) => if p = X ∧ k.val = 0 then (5,w,none) else (7,w,none)
  | (.inr (.introspect,false), .inr (.introspect,true)) => (6,false,none)
  | _ => (7,false,none)

def metadata (X Z : P) : PolyTimeFun (Input P ℓ) (Fin 8 × Bool × Option (Fin ℓ)) :=
  (finiteFunction (route X Z)).comp (leftType.pair rightType)

def sourceContext (X Z : P) : PolyTimeFun (Input P ℓ) AuxiliarySource.Context :=
  contextWith (fst.comp (snd.comp (metadata X Z)))

def nextBranch (U : ClockedUniversalMachine) (X Z : P) (k : Option (Fin ℓ)) :
    PolyTimeFun (Input P ℓ) Bool :=
  match k with
  | none => const true
  | some k => (AuxiliaryHiding.check (SourcePadding.Program.factorFromContext U)
      (SourcePadding.Program.matrixFromContext U) k.val).comp
        ((sourceContext X Z).pair (leftTriple.pair rightTriple))

def branch (U : ClockedUniversalMachine) (X Z : P)
    (project : PolyTimeFun (Input P ℓ) BitStr) (tag : Fin 8) : PolyTimeFun (Input P ℓ) Bool :=
  match tag.val with
  | 0 => equal project (fst.comp rightPair)
  | 1 => (ClockedSourceChecks.sampling U).comp
      ((AuxiliarySource.budget.comp context).pair ((AuxiliarySource.source.comp context).pair
        ((const ℓ).pair ((fst.comp (snd.comp (metadata X Z))).pair guardFields))))
  | 2 => readingCheck.comp guardFields
  | 3 => (AuxiliaryBoundary.last (SourcePadding.Program.factorFromContext U)
      (SourcePadding.Program.matrixFromContext U) ℓ).comp
        ((sourceContext X Z).pair (leftTriple.pair
          ((fst.comp rightTriple).pair (fst.comp (snd.comp rightTriple)))))
  | 4 => choose (snd.comp (snd.comp (metadata X Z))) (nextBranch U X Z) (const true)
  | 5 => (AuxiliaryBoundary.first (SourcePadding.Program.factorFromContext U)
      (SourcePadding.Program.matrixFromContext U)).comp
        ((sourceContext X Z).pair (project.pair rightTriple))
  | 6 => (ClockedSourceChecks.cross U).comp
      ((AuxiliarySource.budget.comp context).pair (sourceDecider.pair guardFields))
  | _ => const true

/-- The complete directed auxiliary program, including the source game call. -/
def directed (U : ClockedUniversalMachine) (X Z : P)
    (project : PolyTimeFun (Input P ℓ) BitStr) : PolyTimeFun (Input P ℓ) Bool :=
  choose (fst.comp (metadata X Z)) (branch U X Z project) (const true)

/-- Both orientations and exact same-type byte consistency are checked.
The Pauli predicate and its format checks are conjoined by the caller. -/
def check (U : ClockedUniversalMachine) (X Z : P)
    (project : PolyTimeFun (Input P ℓ) BitStr) : PolyTimeFun (Input P ℓ) Bool :=
  andCheck format (andCheck (format.comp swap)
    (andCheck (ite (equal leftType rightType) (equal leftBits rightBits) (const true))
      (andCheck (directed U X Z project) ((directed U X Z project).comp swap))))

end MIPRE.Introspection.AuxiliaryDecision
end


