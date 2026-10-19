-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_DecisionPreparation
-- name    : MIPRE_Foundations_Introspection_DecisionPreparation
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T03:08:57.043725+00:00
-- url     : https://prove2.me/theorems/d0859f78-ceeb-4ca2-b884-6b05767588cc
-- title:
--   Definitions of DecisionPreparation: Preparing shared resources for the introspection decision kernel The uniform program receives `cons (encode ((S,D),λ))…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.DecisionPreparation` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Preparing shared resources for the introspection decision kernel. The uniform program receives `cons (encode ((S,D),λ)) raw`. It generates the single unary clock, exponential source index, canonical unary Pauli parameters and binary register bounds. The raw decision input and source metadata are retained verbatim. A fixed polynomial-time kernel then consumes these resources.
--
--   **Definitions** (29): `MIPRE.Introspection.DecisionPreparation.KernelInput`; `MIPRE.Introspection.DecisionPreparation.Metadata`; `MIPRE.Introspection.DecisionPreparation.Resources`; `MIPRE.Introspection.DecisionPreparation.appendRoute` (Append a subroutine result while retaining its entire input as context.); `MIPRE.Introspection.DecisionPreparation.appendStage`; `MIPRE.Introspection.DecisionPreparation.boundsResult`; `MIPRE.Introspection.DecisionPreparation.boundsStage`; `MIPRE.Introspection.DecisionPreparation.clockResult`; `MIPRE.Introspection.DecisionPreparation.clockStage`; `MIPRE.Introspection.DecisionPreparation.compiler` (The compiler specializes only the binary source metadata.); `MIPRE.Introspection.DecisionPreparation.finish`; `MIPRE.Introspection.DecisionPreparation.indexResult`; `MIPRE.Introspection.DecisionPreparation.indexStage`; `MIPRE.Introspection.DecisionPreparation.inputIndex`; `MIPRE.Introspection.DecisionPreparation.inputLambda`; `MIPRE.Introspection.DecisionPreparation.inputMetadata`; `MIPRE.Introspection.DecisionPreparation.inputRaw`; `MIPRE.Introspection.DecisionPreparation.kernelInput` (The same prepared layout with canonically supplied source programs typed.); `MIPRE.Introspection.DecisionPreparation.kernelProg`; `MIPRE.Introspection.DecisionPreparation.origin`; `MIPRE.Introspection.DecisionPreparation.parameterInput`; `MIPRE.Introspection.DecisionPreparation.pauliResult`; `MIPRE.Introspection.DecisionPreparation.pauliStage`; and 6 more.
--
--   **Embedded lemmas** (3): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `compiler_apply`, `inputIndex_canonical`, `inputLambda_canonical`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.DecisionPreparation` (`MIPRE/Foundations/Introspection/DecisionPreparation.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 82 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/DecisionPreparation.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/DecisionPreparation.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Computability.Primrec.List
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
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
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
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
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
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
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompilerParams
import Definitions.Def_MIPRE_Foundations_Introspection_PauliSamplerParams
import Definitions.Def_MIPRE_Foundations_Introspection_Clock
import Definitions.Def_MIPRE_Foundations_Introspection_ClockCost
import Definitions.Def_MIPRE_Foundations_Introspection_ClockSimulation
import Definitions.Def_MIPRE_Foundations_Introspection_ClockCompiler
import Definitions.Def_MIPRE_Foundations_Introspection_ClockSimulationCost
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompilerParamsCost
import Definitions.Def_MIPRE_Foundations_Introspection_PauliSamplerParamsCost
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompilerGuard
import Definitions.Def_MIPRE_Foundations_Introspection_ParserGuard
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompiler
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompilerCost
import Theorems.Thm_MIPRE_CL_Detyping_Program_readNat_encode
import Theorems.Thm_MIPRE_Cost_Prog_routeOneCall_closed
import Theorems.Thm_MIPRE_Cost_Prog_routeOneCall_indirect
import Theorems.Thm_MIPRE_Cost_hardcode_time
import Theorems.Thm_MIPRE_Cost_hardcode_wellScoped

/-! # Preparing shared resources for the introspection decision kernel

The uniform program receives `cons (encode ((S,D),λ)) raw`. It generates the
single unary clock, exponential source index, canonical unary Pauli parameters
and binary register bounds. The raw decision input and source metadata are
retained verbatim. A fixed polynomial-time kernel then consumes these resources.
-/

noncomputable section
namespace MIPRE.Introspection.DecisionPreparation
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program SourceCompiler

abbrev Metadata := (Prog × Prog) × ℕ
abbrev Resources := Data × Data × Unary × ℕ × PauliSamplerParameters.Parameters × ℕ × ℕ
abbrev KernelInput := Data × Metadata × Unary × ℕ × PauliSamplerParameters.Parameters × ℕ × ℕ

def inputMetadata : PolyTimeFun Data Data := treeHead
def inputRaw : PolyTimeFun Data Data := treeTail
def inputLambda : PolyTimeFun Data ℕ := readNat.comp (treeTail.comp inputMetadata)
def inputIndex : PolyTimeFun Data ℕ := ClockSimulation.indexReader.comp inputRaw
def parameterInput : PolyTimeFun Data Data := encoded.comp (inputLambda.pair inputIndex)

/-- The output format, before any kernel-specific conversion. -/
def resources (c : ℕ) (z : Data) : Resources :=
  (inputRaw z, inputMetadata z, unary (ansBound 5 (inputLambda z) (inputIndex z)),
    2 ^ inputIndex z, PauliSamplerParameters.parameters c (inputLambda z) (inputIndex z),
    registerBits c (inputLambda z) (inputIndex z), originalBound (inputLambda z) (inputIndex z))

/-- The same prepared layout with canonically supplied source programs typed. -/
def kernelInput (c : ℕ) (M : Metadata) (x : Data) : KernelInput :=
  let n := ClockSimulation.indexReader x
  (x, M, unary (ansBound 5 M.2 n), 2 ^ n, PauliSamplerParameters.parameters c M.2 n,
    registerBits c M.2 n, originalBound M.2 n)

@[simp] theorem inputLambda_canonical (S D : Prog) (lam : ℕ) (x : Data) :
    inputLambda (.cons (encode ((S,D),lam)) x) = lam := by
  simp [inputLambda, inputMetadata, encode_prod, readNat_encode]

@[simp] theorem inputIndex_canonical (M : Data) (x : Data) :
    inputIndex (.cons M x) = ClockSimulation.indexReader x := rfl

/-- Append a subroutine result while retaining its entire input as context. -/
def appendRoute (arg : PolyTimeFun Data Data) : PolyTimeFun Data (Bool × Data) :=
  (const true).pair (ap₂ treePair arg (PolyTimeFun.id Data))

def appendStage (arg : PolyTimeFun Data Data) (p : Prog) : Prog :=
  routeOneCall (appendRoute arg) p treePair

def clockStage : Prog := appendStage parameterInput (ClockArithmetic.uniformProg 5)
def indexStage : Prog := appendStage (inputRaw.comp treeHead) ClockSimulation.reindexProg
def pauliStage (c : ℕ) : Prog :=
  appendStage (parameterInput.comp (treeHead.comp treeHead)) (PauliSamplerParameters.prog c)
def boundsStage (c : ℕ) : Prog :=
  appendStage (parameterInput.comp (treeHead.comp (treeHead.comp treeHead))) (boundsProg c)

def origin : PolyTimeFun Data Data := treeHead.comp (treeHead.comp (treeHead.comp treeHead))
def preparedClock : PolyTimeFun Data Data := treeTail.comp (treeHead.comp (treeHead.comp treeHead))
def preparedIndex : PolyTimeFun Data Data := treeHead.comp (treeTail.comp (treeHead.comp treeHead))
def preparedParameters : PolyTimeFun Data Data := treeTail.comp treeHead

def finish : PolyTimeFun Data Data :=
  ap₂ treePair (inputRaw.comp origin) (ap₂ treePair (inputMetadata.comp origin)
    (ap₂ treePair preparedClock (ap₂ treePair preparedIndex
      (ap₂ treePair preparedParameters treeTail))))

/-- Sequence closed programs, retaining the ambient input discipline. -/
def sequence (p q : Prog) : Prog := .let_ p q

/-- The budget appears once in the program; all later stages only retain it. -/
def prog (c : ℕ) : Prog := sequence clockStage (sequence indexStage
  (sequence (pauliStage c) (sequence (boundsStage c) finish.code)))

def clockResult (z : Data) : Data := .cons z (.ofNat (ansBound 5 (inputLambda z) (inputIndex z)))
def indexResult (z : Data) : Data := .cons (clockResult z) (ClockSimulation.reindexed (inputRaw z))
def pauliResult (c : ℕ) (z : Data) : Data :=
  .cons (indexResult z) (encode (PauliSamplerParameters.parameters c (inputLambda z) (inputIndex z)))
def boundsResult (c : ℕ) (z : Data) : Data :=
  .cons (pauliResult c z) (encode (registerBits c (inputLambda z) (inputIndex z),
    originalBound (inputLambda z) (inputIndex z)))

def kernelProg (c : ℕ) (kernel : PolyTimeFun KernelInput Bool) : Prog :=
  sequence (prog c) kernel.code

/-- The compiler specializes only the binary source metadata. -/
def compiler (c : ℕ) (kernel : PolyTimeFun KernelInput Bool) : PolyTimeFun Metadata Prog :=
  (smn Metadata).comp ((const (kernelProg c kernel)).pair (PolyTimeFun.id Metadata))

@[simp] theorem compiler_apply (c : ℕ) (kernel : PolyTimeFun KernelInput Bool) (M : Metadata) :
    compiler c kernel M = hardcode (kernelProg c kernel) (encode M) := rfl

end MIPRE.Introspection.DecisionPreparation


