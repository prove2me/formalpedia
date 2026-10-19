-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_SourcePaddingQueryProg
-- name    : MIPRE_Foundations_Introspection_SourcePaddingQueryProg
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T03:09:06.57559+00:00
-- url     : https://prove2.me/theorems/384ccac1-4acd-43d6-8c9e-c309c01452d0
-- title:
--   Definitions of SourcePaddingQueryProg: Uniform programs for queries to a padded source Source width is input data
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.SourcePaddingQueryProg` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Uniform programs for queries to a padded source. Source width is input data. The full register width is read from the prefix. Source queries receive only the original prefix and vector coordinates; their answers are extended to the full register. The first factor consumes the unused suffix and all later factors leave it empty.
--
--   **Definitions** (12): `MIPRE.Introspection.SourcePadding.Program.QContext`; `MIPRE.Introspection.SourcePadding.Program.adapt` (Cap the dimension by the actual full prefix length before creating unary data.); `MIPRE.Introspection.SourcePadding.Program.dimension` (Read the source dimension with the already supplied source clock.); `MIPRE.Introspection.SourcePadding.Program.factor`; `MIPRE.Introspection.SourcePadding.Program.factorFromContext` (The original scan context is sufficient: width is queried at runtime.); `MIPRE.Introspection.SourcePadding.Program.fullWidth`; `MIPRE.Introspection.SourcePadding.Program.linear`; `MIPRE.Introspection.SourcePadding.Program.matrix`; `MIPRE.Introspection.SourcePadding.Program.matrixFromContext`; `MIPRE.Introspection.SourcePadding.Program.sourceContext`; `MIPRE.Introspection.SourcePadding.Program.sourceWidth`; `MIPRE.Introspection.SourcePadding.Program.suffixWidth`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.SourcePaddingQueryProg` (`MIPRE/Foundations/Introspection/SourcePaddingQueryProg.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 137 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/SourcePaddingQueryProg.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/SourcePaddingQueryProg.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_Introspection_Clock
import Definitions.Def_MIPRE_Foundations_Introspection_ClockCost
import Definitions.Def_MIPRE_Foundations_Introspection_ClockSimulation
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompilerGuard
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
import Definitions.Def_MIPRE_Foundations_Introspection_Readout
import Definitions.Def_MIPRE_Foundations_Introspection_FinalExtraction
import Definitions.Def_MIPRE_Foundations_Introspection_TypeGraph
import Definitions.Def_MIPRE_Foundations_Introspection_HonestCore
import Definitions.Def_MIPRE_Foundations_Introspection_SourcePadding
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryRegisterBits
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliarySourceQueries
import Definitions.Def_MIPRE_Foundations_Introspection_SourcePaddingQueries
import Theorems.Thm_MIPRE_CL_Detyping_Program_readNat_encode
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_transposeBits_matrixBits

/-! # Uniform programs for queries to a padded source

Source width is input data. The full register width is read from the prefix.
Source queries receive only the original prefix and vector coordinates;
their answers are extended to the full register. The first factor consumes
the unused suffix and all later factors leave it empty.
-/

noncomputable section
namespace MIPRE.Introspection.SourcePadding.Program
open Cost Cost.PolyTimeFun CL.Detyping.Program LowDegree.BinaryLinear AuxiliaryProgram

abbrev QContext := Unary × AuxiliarySource.Context

def sourceWidth : PolyTimeFun QContext Unary := fst
def fullWidth : PolyTimeFun QContext Unary := length.comp (AuxiliarySource.inputPrefix.comp snd)
def suffixWidth : PolyTimeFun QContext Unary := drop.comp (fullWidth.pair sourceWidth)

def sourceContext : PolyTimeFun QContext AuxiliarySource.Context :=
  (AuxiliarySource.budget.comp snd).pair ((AuxiliarySource.source.comp snd).pair
    ((AuxiliarySource.index.comp snd).pair ((AuxiliarySource.player.comp snd).pair
      ((AuxiliarySource.level.comp snd).pair
        (take.comp ((AuxiliarySource.inputPrefix.comp snd).pair sourceWidth))))))

def linear (U : ClockedUniversalMachine) : PolyTimeFun (BitStr × QContext) BitStr :=
  let input := take.comp (fst.pair (sourceWidth.comp snd))
  let output := (AuxiliarySource.linear U).comp (input.pair (sourceContext.comp snd))
  append.comp (output.pair (replicate.comp ((suffixWidth.comp snd).pair (const false))))

def factor (U : ClockedUniversalMachine) : PolyTimeFun QContext BitStr :=
  let first := SAT.ArrayProg.eqNat.comp ((AuxiliarySource.level.comp snd).pair (const 1))
  append.comp (((AuxiliarySource.factor U).comp sourceContext).pair
    (replicate.comp (suffixWidth.pair first)))

def matrix (U : ClockedUniversalMachine) : PolyTimeFun QContext (List BitStr) :=
  let columns := (mapWith (linear U)).comp
    ((identityBitsProg.comp fullWidth).pair (PolyTimeFun.id _))
  transposeBitsProg.comp (fullWidth.pair columns)

/-- Read the source dimension with the already supplied source clock. -/
def dimension (U : ClockedUniversalMachine) : PolyTimeFun AuxiliarySource.Context ℕ :=
  let query := encoded.comp
    (AuxiliarySource.index.pair (const CL.Sampler.Query.dimension))
  readNat.comp (treeTail.comp ((ClockedQuery.run U).comp
    (AuxiliarySource.budget.pair (AuxiliarySource.source.pair query))))

/-- Cap the dimension by the actual full prefix length before creating unary
data. Consequently arbitrary dimension-query results cannot cause large allocation. -/
def adapt (U : ClockedUniversalMachine) : PolyTimeFun AuxiliarySource.Context QContext :=
  (DynamicParser.boundedOffset.comp (AuxiliarySource.inputPrefix.pair (dimension U))).pair
    (PolyTimeFun.id _)

/-- The original scan context is sufficient: width is queried at runtime. -/
def factorFromContext (U : ClockedUniversalMachine) : PolyTimeFun AuxiliarySource.Context BitStr :=
  (factor U).comp (adapt U)

def matrixFromContext (U : ClockedUniversalMachine) :
    PolyTimeFun AuxiliarySource.Context (List BitStr) := (matrix U).comp (adapt U)

end MIPRE.Introspection.SourcePadding.Program
end


