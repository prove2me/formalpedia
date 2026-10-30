-- Prove2me | Definitions.Def_OAIQ081S081
-- name    : OAIQ081S081
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:06:12.854513+00:00
-- url     : https://prove2.me/theorems/38ee9767-4ea4-4d25-861d-6b7442f332ea
-- title:
--   Definitions bundle OAIQ081S081 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 140 declarations of OpenAI's Lean: 130 definitions, 5 inductive types or structures and 5 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityPrimitives.Count.binaryProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityPrimitives.Count.countTest`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityPrimitives.Count.toBinary`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEnvironment.reset`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEnvironment.reset16`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.replaceInner`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.initial`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.HeadGate.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafOuterNative.prefixTrial`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSemantics.indexed`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction.coreBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction.prepareBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamBudgets.reconstructionCoefficient`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamBudgets.scalarEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamSpaceBudgets.envelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamSpaceBudgets.recoveryEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.RingNodeSetup.initNodes`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.RingNodeSetup.readNode`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.RingNodeSetup.storeOf`, `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixAnchorGuardProgram.accepted`, `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixAnchorGuardProgram.compared`, `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixAnchorGuardProgram.copied`, `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixAnchorGuardProgram.cost`, `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixAnchorGuardProgram.popped`, `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixAnchorGuardProgram.valid`, `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixAnchorReadProgram.cleared`, `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixAnchorReadProgram.copied`, `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixAnchorReadProgram.fourReadResult`, `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixAnchorReadProgram.moved`, `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixAnchorReadProgram.readOneResult`, `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixAnchorReadProgram.readResult`, `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixAnchorReadProgram.transferred`, `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryProgram.copied`, `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryProgram.counted`, `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryProgram.project`, `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.clearColorsCost`, `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.cleared`, `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.colorsCleared`, `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.install` and 95 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityPrimitives`, `SubexponentialSAT_SqrtLogSpace_FactorEnvironment`, `SubexponentialSAT_SqrtLogSpace_FactorTableProgram`, `SubexponentialSAT_SqrtLogSpace_HashGreedyCode`, `SubexponentialSAT_SqrtLogSpace_HashTrialStage`, `SubexponentialSAT_SqrtLogSpace_HeadEvaluationProgram`, `SubexponentialSAT_SqrtLogSpace_NativeLeafSemantics`, `SubexponentialSAT_SqrtLogSpace_QueryReconstruction`, `SubexponentialSAT_SqrtLogSpace_QueryStreamBudgets`, `SubexponentialSAT_SqrtLogSpace_QueryStreamSpaceBudgets`, `SubexponentialSAT_SqrtLogSpace_RingNodeSetup`, `SubexponentialSAT_SqrtLogSpace_StreamResources`, `SubexponentialSAT_SubexpCRTAtZero`, `SubexponentialSAT_SubexpConvolutionIteration`, `SubexponentialSAT_SubexpConvolutionOuter`, `SubexponentialSAT_SubexpConvolutionRows`, `SubexponentialSAT_SubexpDenseOperandIO`, `SubexponentialSAT_SubexpEmptyClauseProgram`, `SubexponentialSAT_SubexpEvaluationProgram`, `SubexponentialSAT_SubexpIncidenceSlotProgram`, `SubexponentialSAT_SubexpNodeScanControl`, `SubexponentialSAT_SubexpNormalizationPrefixProgram`, `SubexponentialSAT_SubexpNormalizationProgram`, `SubexponentialSAT_SubexpProjectedExecution`, `SubexponentialSAT_SubexpRowInterpolation`, `SubexponentialSAT_SubexpTautologyFilterProgram`, `SubexponentialSAT_SubexpTautologyProgram`, `SubexponentialSAT_Subexp_MatrixAnchorGuardProgram`, `SubexponentialSAT_Subexp_MatrixAnchorReadProgram`, `SubexponentialSAT_Subexp_MatrixAnchorTypes`, `SubexponentialSAT_Subexp_MatrixEntryFrames`, `SubexponentialSAT_Subexp_MatrixEntryPrepare`, `SubexponentialSAT_Subexp_MatrixExtendedEntryProgram`, `SubexponentialSAT_Subexp_MatrixInputAccess`, `SubexponentialSAT_Subexp_MatrixInputProgram`, `SubexponentialSAT_Subexp_MatrixInputTypes`, `SubexponentialSAT_Subexp_MatrixPositionCountProgram`, `SubexponentialSAT_Subexp_MatrixPositionProgram`, `SubexponentialSAT_Subexp_MatrixProgram`, `SubexponentialSAT_Subexp_MatrixScanProgram`, `SubexponentialSAT_Subexp_MatrixScanSemantics`, `SubexponentialSAT_Subexp_MatrixScanStepProgram`, `SubexponentialSAT_Subexp_MatrixVectorProgram`, `SubexponentialSAT_Subexp_MismatchPlanProgram`, `SubexponentialSAT_Subexp_TensorSpectrum`, `SubexponentialSAT_Subexp_UniversalRowFactorLoop`, `SubexponentialSAT_Subexp_UniversalRowGather`, `SubexponentialSAT_Subexp_UniversalRowLoop`, `SubexponentialSAT_Subexp_UniversalRowMismatchProgram`, `SubexponentialSAT_Subexp_UniversalRowMismatchTypes`, `SubexponentialSAT_Subexp_UniversalRowTermProgram`, `SubexponentialSAT_TruncatedInverse`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S045`, `OAIQ081S046`, `OAIQ081S047`, `OAIQ081S048`, `OAIQ081S049`, `OAIQ081S050`, `OAIQ081S051`, `OAIQ081S054`, `OAIQ081S055`, `OAIQ081S056`, `OAIQ081S058`, `OAIQ081S059`, `OAIQ081S060`, `OAIQ081S063`, `OAIQ081S064` and `OAIQ081S065` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ081S099`; the statements `OAI.Algorithms.SubexponentialSAT.ExecCoreChildProgram.program_runsIn`, `OAI.Algorithms.SubexponentialSAT.ExecPetalChildProgram.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.PairSpec.pairSpec`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Scan.scanStage_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.scalar_value_eq_target`, `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.command_run`, `OAI.Algorithms.SubexponentialSAT.SubexpNodeScanControl.command_run`, `OAI.Algorithms.SubexponentialSAT.SubexpNormalizationProgram.absorb_eval`, `OAI.Algorithms.SubexponentialSAT.SubexpNormalizationProgram.removeSupersetsCall_eval`, `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixAnchorReadProgram.readFour_typed`, `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixInputTypes.program_runsIn` and `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixScanStepProgram.command_eval`; the proofs of `OAI.Algorithms.SubexponentialSAT.ExecCoreChildProgram.program_runsIn`, `OAI.Algorithms.SubexponentialSAT.ExecPetalChildProgram.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.rejection_scan_runs_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsSpace.program_stack_bound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram.resultB_length_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.localCommand_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed.mul_spec`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.PairSpec.pairSpec`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.scan_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator.centered_rationalDefect_rank_relative`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Scan.scanStage_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped.row_meaning`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.sourceCode_decode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.scalar_value_eq_target`, `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.command_run`, `OAI.Algorithms.SubexponentialSAT.SubexpDenseLiteralPadding.program_runsIn`, `OAI.Algorithms.SubexponentialSAT.SubexpNodeScanControl.command_run`, `OAI.Algorithms.SubexponentialSAT.SubexpNormalizationCorrectness.normalizedBody_length_le`, `OAI.Algorithms.SubexponentialSAT.SubexpNormalizationProgram.absorb_eval`, `OAI.Algorithms.SubexponentialSAT.SubexpNormalizationProgram.removeSupersetsCall_eval`, `OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixServices.program_runsIn`, `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixAnchorReadProgram.readFour_typed`, `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixInputTypes.program_runsIn`, `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixScanStepProgram.command_eval`, `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixVectorProgram.matrix_trace` and `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowMismatchTypes.filter_eval`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S045
import Definitions.Def_OAIQ081S046
import Definitions.Def_OAIQ081S047
import Definitions.Def_OAIQ081S048
import Definitions.Def_OAIQ081S049
import Definitions.Def_OAIQ081S050
import Definitions.Def_OAIQ081S051
import Definitions.Def_OAIQ081S054
import Definitions.Def_OAIQ081S055
import Definitions.Def_OAIQ081S056
import Definitions.Def_OAIQ081S058
import Definitions.Def_OAIQ081S059
import Definitions.Def_OAIQ081S060
import Definitions.Def_OAIQ081S063
import Definitions.Def_OAIQ081S064
import Definitions.Def_OAIQ081S065

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityPrimitives
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete record-count and emission primitives extracted from supplied sources.
No sparsification schedule or formula evaluator is imported. Provenance is recorded
in verification/counting-draft/worker04/extraction.json. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityPrimitives

open BitProgram StructuredCalls BinaryArithmetic

namespace Count

open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityPrimitives.Tuple
  (copy clear )

def binaryProgram := ProgramLinking.liftProgram FrontendProgram.initializeProgram binaryReg binaryStack
def toBinary : Cmd 13 9 := .seq reset (.call binaryProgram)

def countTest (expected : Fin 2) : Cmd 13 9 :=
  .seq (.call countProgram) (.seq toBinary (.seq (numericEq expected) (clear 6)))

end Count

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityPrimitives
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_TruncatedInverse
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Explicit finite geometric inversion and local CRT factors

The inverses in this file are finite polynomial expressions. Scalar inverses are
input data with multiplication certificates; no Bézout coefficients are chosen.
-/

noncomputable section

namespace SubexponentialSAT.TruncatedInverse

open Polynomial
open scoped BigOperators

variable {A : Type*} [CommRing A]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Explicit Hermite reconstruction. Local corrections are truncated before
shifting back, so no final polynomial division is required. -/
def reconstruct (θ : ι → A) (D : ℕ) (a : ι → A) (J : ι → A[X]) : A[X] :=
  ∑ i, JetCRT.cofactor θ D i * (correction θ D a J i).comp (X - C (θ i))

end SubexponentialSAT.TruncatedInverse

end
end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorEnvironment
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The seven fixed persistent cache words are physically copied into the
native arithmetic environment. Cleanup clears those seven copies; both
commands frame all other stacks, including the query buffers. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEnvironment

open OAI BitProgram StructuredCalls
open SubexpSetupStorage SqrtLog.MomentsProgram

def reset16 : Cmd 16 896 := clearMany environmentPorts

def reset : Cmd 40 896 :=
  .call (ProgramLinking.liftProgram (compiled reset16 5 5) registerMap id)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEnvironment
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpRowInterpolation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Explicit mismatch interpolation for the multi-color layout

Section 3.3 of `subexponential-sat.txt`. All inverse data are supplied as
units. The polynomials are finite sums and products, not chosen witnesses.
Their scalar evaluation functions are executable from the supplied ring
operations and units; the semantic polynomial definitions use mathlib's
noncomputable polynomial representation.
-/

namespace SubexponentialSAT.SubexpRowInterpolation

open scoped BigOperators

variable {E I V C : Type*} [CommRing E] [DecidableEq I]

variable {node : I → E}

variable [DecidableEq V]

/-! ## Executable finite expression codes

The following constructors produce polynomial expression data using only
finite `List.ofFn` traversals. Their denotations are the proved polynomials
above. This supplies a concrete path representation in addition to the
executable scalar evaluator.
-/

section FiniteCode

variable {Q : ℕ} {node : Fin Q → E}

/-- Executable expression for a Lagrange basis with zero constant term. -/
def basisCode (u : NodeUnits node) (s : Finset (Fin Q)) (i : Fin Q) : PolynomialCode E :=
  .mul (.mul (.constant (u.nodeInverse i)) .indeterminate)
    (PolynomialCode.product (List.ofFn (fun j : Fin Q =>
      if j ∈ s.erase i then
        .mul (.constant (u.differenceInverse i j))
          (.add .indeterminate (.constant (-node j)))
      else .constant 1)))

/-- Executable constructor for the actual correction polynomial. -/
def correctionCode (u : NodeUnits node) (s : Finset (Fin Q)) (d : Fin Q → E) :
    PolynomialCode E :=
  PolynomialCode.sum (List.ofFn (fun i : Fin Q =>
    if i ∈ s then .mul (.constant (d i)) (basisCode u s i) else .constant 0))

variable [Fintype V] [DecidableEq C]

/-- A fully finite, executable expression constructor for the multi-color row. -/
def mismatchRowCode (v : V) (head : V → Fin Q → C) (σ : Fin Q → C) (R : ℕ)
    (u : NodeUnits node) (d : V → Fin Q → E) (y : V) : PolynomialCode E :=
  .add (.constant ((Pi.single v (1 : E) : V → E) y))
    (if y ∈ correctionColumns head σ R then
      correctionCode u (mismatchPositions head σ y) (d y)
    else .constant 0)

end FiniteCode

end SubexponentialSAT.SubexpRowInterpolation

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpConvolutionIteration
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Unary runtime-loop execution used by both convolution loops. The body
obligation contains actual executions; the loop invariant concerns physical
stacks and may include decoded coefficient arrays and their lengths. -/

namespace SubexponentialSAT.SubexpConvolutionControl

open BitProgram StructuredCalls

def unaryLoop (counter : Fin 256) (flag : Fin 16) (body : Code) : Code :=
  .while flag (.seq body (test counter flag))

def unaryRun (counter : Fin 256) (flag : Fin 16) (body : Code) : Code :=
  .seq (test counter flag) (unaryLoop counter flag body)

end SubexponentialSAT.SubexpConvolutionControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNodeScanControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed traversal of flat node cells, skipping one unary-indexed node.
The included-node service is an actual command with an actual execution
contract. This file accounts for all reads, guards, index pops, and cleanup.
-/

namespace SubexponentialSAT.SubexpNodeScanControl

open BitProgram StructuredCalls SubexpConvolutionControl

noncomputable def ready {A C : Type*} (base : Store)
    (encode : C → List Bool) (encodeA : A → List Bool)
    (cs : List C) (x : Cursor A) (current negative : List Bool) : Store :=
  work base (words encode encodeA cs x current negative)

variable {A C : Type*}

def IncludeSpec (includeNode : Code) (base : Store)
    (encode : C → List Bool) (encodeA : A → List Bool)
    (negative : C → List Bool) (f : A → C → A) (K : ℕ) : Prop :=
  ∀ cs x c, ExecutesIn includeNode K
    (ready base encode encodeA cs x (encode c) [])
    (ready base encode encodeA cs {x with value := f x.value c} (encode c) (negative c))

end SubexponentialSAT.SubexpNodeScanControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpConvolutionRows
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The triangular convolution controller charges actual fixed-width reads,
copies, and cell writes. The local pair contract is a contract for a fixed
finite command and is instantiated by the concrete quartic/jet service. -/

namespace SubexponentialSAT.SubexpConvolutionControl

open BitProgram StructuredCalls

variable {C : Type*}

/-- An actual pair-command contract. Only one local multiply-and-accumulate
operation is assumed here, at an in-bounds output cell, with explicit cost. -/
def PairSpec (pair : Code) (base : Store) (encode : C → List Bool)
    (add mul : C → C → C) (D pairCost : ℕ) : Prop :=
  ∀ (w : Buffers) (a b : C) (acc : List C), acc.length = D →
    (w 3).length < D → w 2 = encodeArray encode acc →
    w 9 = encode a → w 10 = encode b →
    ExecutesIn pair pairCost (buffers base w)
      (buffers base (Function.update (Function.update (Function.update w 9 []) 10 []) 2
        (encodeArray encode (TruncatedConvolution.addProduct add mul (w 3).length a b acc))))

structure InnerGood (base : Store) (encode : C → List Bool) (add mul : C → C → C)
    (a : C) (D : ℕ) (original : Buffers) (target suffix : List C) (total : ℕ)
    (r : RowData C) (fuel : ℕ) (stk : Store) : Prop where
  store_eq : stk = buffers base r.work
  pending_length : r.pending.length = fuel
  values_length : r.values.length = D
  accumulator : r.work 2 = encodeArray encode r.values
  right_tail : r.work 6 = encodeArray encode (r.pending ++ suffix)
  count_length : (r.work 7).length = fuel
  coefficient : r.work 8 = encode a
  operand_left : r.work 9 = []
  operand_right : r.work 10 = []
  index_bound : (r.work 3).length + fuel ≤ D
  index_tokens : List.replicate fuel false ++ r.work 3 =
    List.replicate total false ++ original 3
  target_eq : TruncatedConvolution.row add mul a (r.work 3).length r.pending r.values = target
  frame_left : r.work 0 = original 0
  frame_right : r.work 1 = original 1
  frame_row_index : r.work 4 = original 4
  frame_row_count : r.work 5 = original 5

end SubexponentialSAT.SubexpConvolutionControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpConvolutionOuter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The outer triangular loop of the fixed convolution controller. Each row
copies the preserved right-hand array, consumes one left coefficient, and
executes only the still-relevant output positions. -/

namespace SubexponentialSAT.SubexpConvolutionControl

open BitProgram StructuredCalls

variable {C : Type*}


structure OuterGood (base : Store) (encode : C → List Bool) (add mul : C → C → C)
    (Q : List C) (D : ℕ) (original : Buffers) (target : List C) (total : ℕ)
    (r : RowData C) (fuel : ℕ) (stk : Store) : Prop where
  store_eq : stk = buffers base r.work
  pending_length : r.pending.length = fuel
  values_length : r.values.length = D
  left : r.work 0 = encodeArray encode r.pending
  right : r.work 1 = encodeArray encode Q
  accumulator : r.work 2 = encodeArray encode r.values
  row_count : (r.work 5).length = fuel
  index_empty : r.work 3 = []
  right_empty : r.work 6 = []
  count_empty : r.work 7 = []
  coefficient_empty : r.work 8 = []
  operand_left : r.work 9 = []
  operand_right : r.work 10 = []
  index_bound : (r.work 4).length + fuel ≤ D
  index_tokens : List.replicate fuel false ++ r.work 4 =
    List.replicate total false ++ original 4
  target_eq : TruncatedConvolution.rows add mul Q (r.work 4).length fuel r.pending r.values = target

end SubexponentialSAT.SubexpConvolutionControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_StreamResources
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Uniform storage rules for concrete streaming loops. A local runtime bound
is used only for one invocation whose entire initial storage is uniformly
bounded; neither bound depends on the number of loop iterations. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources

open BitProgram

/-- Structured evaluation has its actual measured length, independent of the
derivation used to establish its concrete execution. -/
theorem eval_steps_eq {r s : ℕ} {command : StructuredCalls.Cmd r s}
    (inputStack outputStack : Fin s) {n m : ℕ} {a b c : StructuredCalls.State r s}
    (hb : StructuredCalls.Eval command n a b)
    (hc : StructuredCalls.Eval command m a c) : n = m := by
  have h := halted_trace_steps_eq
    (StructuredCalls.compiled_halt_trace hb inputStack outputStack)
    (StructuredCalls.compiled_halt_trace hc inputStack outputStack)
    (by rfl) (by rfl)
  exact Nat.add_right_cancel h

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpEvaluationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Concrete evaluation-result extraction

The extractor removes the singleton operand-list framing, parses the result
payload into a reversed scratch stack, and transfers it to physical stack 15.
It clears the operand/depth/scratch stacks and preserves every other stack.
-/

namespace SubexponentialSAT.SubexpEvaluationProgram

open BitProgram
open SubexpPostfixControl

open SubexpPostfixGlobal

@[simp] theorem snapshot_depth (bits : List Bool) (context : Fin 124 → List Bool) :
    snapshot bits context 28 = [true] := physicalCfg_depth _ _ _ _ _ _ _ _
@[simp] theorem snapshot_scratch (bits : List Bool) (context : Fin 124 → List Bool) :
    snapshot bits context 29 = [] := physicalCfg_scratch _ _ _ _ _ _ _ _
@[simp] theorem snapshot_output (bits : List Bool) (context : Fin 124 → List Bool) :
    snapshot bits context 15 = context 11 := rfl

/-! ## Entry from arbitrary caller registers -/

@[simp] theorem registers_false : registers false false false = fun _ => false := by
  first | done | (funext i; fin_cases i <;> rfl)

end SubexponentialSAT.SubexpEvaluationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpDenseOperandIO
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed finite framing operations at the physical postfix operand port.
These routines preserve the code/depth stacks and all surrounding data. -/

namespace SubexponentialSAT.SubexpDenseOperandIO

open BitProgram StructuredCalls SubexpScanPrimitives

def afterWrite (d : Data) (bits : List Bool) : Data :=
  ⟨Function.update (Function.update d.regs 0 true) 1 false,
    Function.update (Function.update d.stacks 27
      (true :: (Encoding.frame bits ++ d.stacks 27))) 29 []⟩

end SubexponentialSAT.SubexpDenseOperandIO

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpProjectedExecution
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Projected postfix execution

The compiled source contains the original raw literals. Each complete push
calls the finite projection table; the resulting value is therefore
`(e.map project).eval`. The induction tracks the entire remaining source and
operand list, and charges actual service trace bounds at every node.
-/

namespace SubexponentialSAT.SubexpProjectedInterpreter

open BitProgram
open SubexpPostfixControl (serializeCode serializeInstr operandDepth)
open SubexpPostfixInterpreter (cfg )

variable {r s a b c : ℕ}

/-- A unary load is implemented by actual instructions on the top framed
operand. The rest of the operand stack and arithmetic context are preserved. -/
abbrev LoadImplements {R : Type*} {l : ℕ} (encode : R → List Bool)
    (project : R → R) (service : Program (3 + r) (4 + s) l) (bound : R → ℕ)
    (context : Fin s → List Bool) : Prop :=
  ∀ (x : R) (xs : List R) (code depth : List Bool) (op : Bool),
    RunsIn service (bound x)
      (cfg (some service.entry) true false op code depth
        (Encoding.encodeList encode (x :: xs)) context)
      (cfg none false false false code depth
        (Encoding.encodeList encode (project x :: xs)) context)

/-- Binary services are required only on values produced by projection and
previous arithmetic. Raw literal keys need not satisfy this predicate. -/
abbrev ImplementsOn {R : Type*} {l : ℕ} (valid : R → Prop) (encode : R → List Bool)
    (operation : R → R → R) (isMul : Bool)
    (service : Program (3 + r) (4 + s) l) (bound : R → R → ℕ)
    (context : Fin s → List Bool) : Prop :=
  ∀ (x y : R), valid x → valid y → ∀ (xs : List R) (code depth : List Bool),
    RunsIn service (bound x y)
      (cfg (some service.entry) true true isMul code depth
        (Encoding.encodeList encode (y :: x :: xs)) context)
      (cfg none false false false code depth
        (Encoding.encodeList encode (operation x y :: xs)) context)

end SubexponentialSAT.SubexpProjectedInterpreter

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_TensorSpectrum
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Tensor eigenbases for the multicolor register swap

The finite change of basis is constructed from invertible local kernels. This
module then specializes it to the actual register swap and transports it to the
joint fiber of universal types; multiplicities count those actual basis labels.
-/

namespace SubexponentialSAT.Subexp.TensorSpectrum

open scoped BigOperators

section ProductKernel

variable (K : Type*) [Field K]
variable {β ι : Type*} [Fintype β] [DecidableEq β] [Fintype ι] [DecidableEq ι]

/-- A genuine basis of the full function space on assignments of local states. -/
noncomputable def productBasis (A B : β → β → K)
    (hAB : ∀ x y, (∑ z, A x z * B z y) = if x = y then 1 else 0)
    (hBA : ∀ x y, (∑ z, B x z * A z y) = if x = y then 1 else 0) :
    Module.Basis (ι → β) K ((ι → β) → K) :=
  Module.Basis.ofEquivFun (productCoordinateEquiv K A B hAB hBA)

end ProductKernel

end SubexponentialSAT.Subexp.TensorSpectrum

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowGather
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Reading actual scalar and difference-row data for universal rows

All tables are packed runtime arrays. The selected index is unary data on
stack 16. The three fixed reads preserve their source tables and index and
produce the correction scalar, inverse node, and complete difference row.
-/

namespace SubexponentialSAT.Subexp.UniversalRowGather

open BitProgram StructuredCalls StackRoutines

def result (field : Field) (a : Data) (word : Word) : Data :=
  ⟨readRegs a.regs 0 1 none, Function.update a.stacks (outputPort field) word⟩

def termResult (a : Data) (value inverse differenceRow : Word) : Data :=
  ⟨readRegs a.regs 0 1 none,
    Function.update (Function.update (Function.update a.stacks 19 value) 20 inverse) 0 differenceRow⟩

end SubexponentialSAT.Subexp.UniversalRowGather

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowFactorLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual diagonal exclusion and factor-record production for a row. -/

namespace SubexponentialSAT.Subexp.UniversalRowFactorLoop

open BitProgram StructuredCalls StackRoutines
open UniversalRowGather (Data Word)

abbrev afterEquality (a : Data) (answer : Bool) : Data :=
  ⟨fun j => if j.val < 5 then false else a.regs j,
    Function.update (Function.update (Function.update a.stacks 1 []) 12 [])
      11 (answer :: a.stacks 11)⟩

abbrev compared (a : Data) : Data :=
  ⟨Function.update
      (Function.update (fun j => if j.val < 5 then false else a.regs j) 1 true)
      4 (decide (a.stacks 9 = a.stacks 16)), a.stacks⟩

structure Ready (differences negatives : List Word) (width outer : Word) (a : Data) : Prop where
  differences : a.stacks 0 = differences.flatten
  negatives : a.stacks 26 = negatives.flatten
  width : a.stacks 29 = width
  outer : a.stacks 16 = outer
  empty : ∀ j : Fin 32, j ∈ [1, 2, 4, 5, 6, 7, 11, 12, 15, 22, 23] → a.stacks j = []

abbrev resetState (a : Data) : Data :=
  ⟨Function.update (Function.update (Function.update a.regs 5 false) 6 true) 7 false,
    a.stacks⟩

def invariant (differences negatives : List Word) (width outer : Word)
    (frame : Fin 32 → Word) (a : Data) : Prop :=
  Ready differences negatives width outer a ∧ ∀ j, j ≠ 21 → a.stacks j = frame j

end SubexponentialSAT.Subexp.UniversalRowFactorLoop

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowTermProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One actual correction-term iteration, from packed tables to a row record. -/

namespace SubexponentialSAT.Subexp.UniversalRowTermProgram

open BitProgram StructuredCalls StackRoutines
open UniversalRowGather (Data Word)
open UniversalRowFactorLoop (indexWord)

structure Ready (values inverses negatives rows : List Word) (width rowWidth : Word)
    (positions : List ℕ) (i : ℕ) (a : Data) : Prop where
  values : a.stacks 24 = values.flatten
  inverses : a.stacks 25 = inverses.flatten
  negatives : a.stacks 26 = negatives.flatten
  rows : a.stacks 27 = rows.flatten
  indices : a.stacks 28 = indices positions
  width : a.stacks 29 = width
  rowWidth : a.stacks 30 = rowWidth
  index : a.stacks 16 = indexWord i
  empty : ∀ j : Fin 32,
    j ∈ [0, 1, 2, 4, 5, 6, 7, 8, 9, 11, 12, 15, 19, 20, 21, 22, 23] → a.stacks j = []

end SubexponentialSAT.Subexp.UniversalRowTermProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual outer loop assembling correction terms in selected-index order. -/

namespace SubexponentialSAT.Subexp.UniversalRowLoop

open BitProgram StructuredCalls
open UniversalRowGather (Data Word)
open UniversalRowFactorLoop (indexWord)

def ready (t : Tables) (width rowWidth : Word) (positions : List ℕ) (a : Data) : Prop :=
  UniversalRowTermProgram.Ready t.values t.inverses t.negatives t.rows width rowWidth positions 0 a

def invariant (t : Tables) (width rowWidth : Word) (positions : List ℕ)
    (frame : Fin 32 → Word) (a : Data) : Prop :=
  ready t width rowWidth positions a ∧ ∀ j, j ≠ 31 → a.stacks j = frame j

end SubexponentialSAT.Subexp.UniversalRowLoop

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixInputAccess
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-port array access used to prepare the matrix-entry comparison. -/

namespace SubexponentialSAT.Subexp.MatrixInputAccess

open BitProgram StructuredCalls StackRoutines

abbrev readResult (a : Data) (row : List Bool) : Data :=
  ⟨readRegs a.regs 0 1 none,
    Function.update (Function.update a.stacks 2 []) 1 (row ++ a.stacks 1)⟩

abbrev replaceResult (a : Data) (rows : List Bool) : Data :=
  ⟨readRegs a.regs 0 1 none, Function.update (Function.update a.stacks 2 []) 0 rows⟩

abbrev copied (a : Data) (src dst : Fin 29) : Data :=
  ⟨readRegs a.regs 0 1 none, copyStacks src dst a.stacks⟩

abbrev cleared (a : Data) (src : Fin 29) : Data :=
  ⟨readRegs a.regs 0 1 none, clearStacks src a.stacks⟩

abbrev compared (a : Data) (answer : Bool) : Data :=
  ⟨fun j => if j = 7 then answer else if j.val < 5 then false else a.regs j,
    Function.update (Function.update a.stacks 0 []) 28 []⟩

end SubexponentialSAT.Subexp.MatrixInputAccess

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixPositionProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical comparison of the two color pairs at one matrix position.
The four color words occupy stacks 13--16. They are preserved. Actual copies,
the existing bit-equality table, and actual cleanup produce the comparison
bits; no semantic equality callback is assumed. -/

namespace SubexponentialSAT.Subexp.MatrixPositionProgram

open BitProgram StructuredCalls StackRoutines

abbrev compared (a : Data) (answer : Bool) : Data :=
  ⟨fun j => if j.val < 5 then false else a.regs j,
    Function.update (Function.update (Function.update a.stacks 1 []) 12 [])
      11 (answer :: a.stacks 11)⟩

abbrev copied (a : Data) (src dst : Fin 17) : Data :=
  ⟨readRegs a.regs 0 1 none, copyStacks src dst a.stacks⟩

def leftWord (a : Data) (swapped : Bool) : List Bool :=
  if swapped then a.stacks 14 ++ a.stacks 13 else a.stacks 13 ++ a.stacks 14

def volume (a : Data) : ℕ :=
  (a.stacks 13).length + (a.stacks 14).length + (a.stacks 15).length + (a.stacks 16).length

abbrev prepared (a : Data) (swapped : Bool) : Data :=
  ⟨readRegs a.regs 0 1 none,
    Function.update (Function.update a.stacks 1 (leftWord a swapped))
      12 (a.stacks 15 ++ a.stacks 16)⟩

def pairMatches (a : Data) (swapped : Bool) : Bool :=
  decide (leftWord a swapped = a.stacks 15 ++ a.stacks 16)

end SubexponentialSAT.Subexp.MatrixPositionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixPositionCountProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One physical active-position step for a normalized matrix entry.
Stack 2 counts unchanged nonfixed pairs, stack 3 counts swapped nonfixed
pairs, and register 7 records compatibility of all positions seen so far. -/

namespace SubexponentialSAT.Subexp.MatrixPositionCountProgram

open BitProgram StructuredCalls StackRoutines MatrixPositionProgram

def popped (a : Data) (out : Fin 8) : Data :=
  ⟨readRegs a.regs out 5 (a.stacks 11).head?, Function.update a.stacks 11 (a.stacks 11).tail⟩

def branched (a : Data) : Data :=
  if a.regs 6 then
    if a.regs 4 then a else TupleProgram.pushedState 2 0 true a
  else if a.regs 4 then TupleProgram.pushedState 3 0 true a
  else (StructuredProgram.Atom.set (7 : Fin 8) false).eval a

def resetState (a : Data) : Data :=
  ⟨Function.update (Function.update (Function.update (Function.update a.regs
    0 false) 4 false) 5 false) 6 false, a.stacks⟩

def classified (a : Data) : Data :=
  let same := pairMatches a false
  let swapped := pairMatches a true
  ⟨fun j => if j = 7 then a.regs 7 && (same || swapped) else false,
    Function.update (Function.update a.stacks 2
      (if same && !swapped then true :: a.stacks 2 else a.stacks 2)) 3
      (if swapped && !same then true :: a.stacks 3 else a.stacks 3)⟩

end SubexponentialSAT.Subexp.MatrixPositionCountProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixScanStepProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One physical scan iteration: read four equal-width color records,
classify their same/swapped relation, and clear the consumed color buffers. -/

namespace SubexponentialSAT.Subexp.MatrixScanStepProgram

open BitProgram StructuredCalls StackRoutines

def restrict (a : Data) : MatrixPositionProgram.Data :=
  ⟨a.regs, fun j => a.stacks (lowPorts j)⟩

def frame (base : Data) (a : MatrixPositionProgram.Data) : Data :=
  ⟨a.regs, fun j => if h : j.val < 17 then a.stacks ⟨j.val, h⟩ else base.stacks j⟩

def classified (a : Data) : Data :=
  frame a (MatrixPositionCountProgram.classified (restrict a))

def clearedOne (a : Data) (i : Fin 23) : Data :=
  ⟨readRegs a.regs 0 1 none, clearStacks i a.stacks⟩

def cleared (a : Data) : Data :=
  clearedOne (clearedOne (clearedOne (clearedOne a 13) 14) 15) 16

def output (a : Data) (words rests : Fin 4 → List Bool) : Data :=
  cleared (classified (MatrixColorReadProgram.fourPulled a words rests))

end SubexponentialSAT.Subexp.MatrixScanStepProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixScanProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The finite loop that scans the four color streams. Its loop count and
color width are runtime stacks. The result is specified by a finite fold of
the already proved physical scan step. -/

namespace SubexponentialSAT.Subexp.MatrixScanProgram

open BitProgram StructuredCalls StackRoutines

def popped (a : Data) : Data :=
  ⟨readRegs a.regs 4 6 (a.stacks 22).head?, Function.update a.stacks 22 (a.stacks 22).tail⟩

def result : List ColorRow → Data → Data
  | [], a => popped a
  | w :: ws, a => result ws (MatrixScanStepProgram.output (popped a) w (streams ws))

structure Ready (a : Data) (rows : List ColorRow) (width : ℕ) : Prop where
  zero0 : a.stacks 0 = []
  zero1 : a.stacks 1 = []
  zero4 : a.stacks 4 = []
  zero10 : a.stacks 10 = []
  zero11 : a.stacks 11 = []
  zero12 : a.stacks 12 = []
  targets : ∀ i, a.stacks (MatrixColorReadProgram.target i) = []
  sources : ∀ i, a.stacks (MatrixColorReadProgram.source i) = streams rows i
  width_length : (a.stacks 21).length = width
  count_length : (a.stacks 22).length = rows.length
  row_length : ∀ w ∈ rows, ∀ i, (w i).length = width

end SubexponentialSAT.Subexp.MatrixScanProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixScanSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Arithmetic meaning of the two physical unary counters and the
compatibility register, including the one-hot color encoding boundary. -/

namespace SubexponentialSAT.Subexp.MatrixScanProgram

open BitProgram StructuredCalls StackRoutines

def resultStacks (rows : List ColorRow) (a : Data) : Fin 23 → List Bool := fun j =>
  if j = 2 then List.replicate (unchangedCount rows) true ++ a.stacks 2
  else if j = 3 then List.replicate (transposedCount rows) true ++ a.stacks 3
  else if 13 ≤ j.val ∧ j.val ≤ 20 then []
  else if j = 22 then [] else a.stacks j

end SubexponentialSAT.Subexp.MatrixScanProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixEntryFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-port execution rules used to assemble the concrete entry program.
The call rule consumes a trace of the supplied actual subprogram. -/

namespace SubexponentialSAT.Subexp.MatrixEntryProgram

open BitProgram StructuredCalls StackRoutines

def project {s : ℕ} (hs : s ≤ 37) (a : Data) : State 8 s :=
  ⟨fun j => a.regs (lowRegisters j), fun j => a.stacks (j.castLE hs)⟩

def copied (a : Data) (src dst : Fin 37) : Data :=
  ⟨readRegs a.regs 0 1 none, copyStacks src dst a.stacks⟩

end SubexponentialSAT.Subexp.MatrixEntryProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixEntryPrepare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual preparation of the coefficient workspace from the two scan counts.
The first count is positive: its first token is the distinguished joint
coordinate. All remaining operations are concrete copies, transfers and pushes. -/

namespace SubexponentialSAT.Subexp.MatrixEntryProgram

open BitProgram StructuredCalls StackRoutines

def counted (base : Data) (regs : Fin 9 → Bool) (A B : ℕ) : Data :=
  ⟨regs, fun j =>
    if j = 2 then List.replicate A true
    else if j = 3 then List.replicate B true
    else if j = 22 then []
    else if j = 33 then base.stacks 22
    else if j = 34 ∨ j = 35 ∨ j = 36 then []
    else base.stacks j⟩

end SubexponentialSAT.Subexp.MatrixEntryProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixInputProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Extract head/slot rows and compare the untouched spectator rows. All row
widths and selected-row indices are data; the instruction table is fixed. -/

namespace SubexponentialSAT.Subexp.MatrixInputProgram

open BitProgram StructuredCalls StackRoutines MatrixInputAccess


def WorkReady (a : Data) : Prop :=
  a.stacks 1 = [] ∧ a.stacks 2 = [] ∧ a.stacks 4 = [] ∧ a.stacks 5 = [] ∧
  a.stacks 6 = [] ∧ a.stacks 7 = [] ∧ a.stacks 8 = []

def extracted (a : Data) (second : Bool) (head slot : List Bool) : Data :=
  ⟨readRegs a.regs 0 1 none,
    Function.update (Function.update (Function.update a.stacks 0 (a.stacks (sourcePort second)))
      (headPort second) head) (slotPort second) slot⟩

def normalized (a : Data) (before after : List (List Bool)) : Data :=
  ⟨readRegs a.regs 0 1 none,
    Function.update a.stacks 0 (normalizedBits (a.stacks 17) before after)⟩

def inputState (left right index width colors positions : List Bool)
    (regs : Fin 8 → Bool) : Data :=
  ⟨regs, fun j => if j = 21 then colors else if j = 22 then positions
    else if j = 23 then left else if j = 24 then right else if j = 25 then index
    else if j = 26 then width else []⟩

def outputState (left right index width colors positions : List Bool)
    (headU slotU headY slotY : List Bool) (answer : Bool) (regs : Fin 8 → Bool) : Data :=
  ⟨fun j => if j = 7 then answer else if j.val < 5 then false else regs j,
    fun j => if j = 17 then headU else if j = 18 then slotU else if j = 19 then headY
      else if j = 20 then slotY else (inputState left right index width colors positions regs).stacks j⟩

end SubexponentialSAT.Subexp.MatrixInputProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixInputTypes
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.allCompatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The concrete extractor on canonical one-hot type encodings. -/

namespace SubexponentialSAT.Subexp.MatrixInputTypes

open BitProgram StructuredCalls MulticolorTypes ReadPlan MatrixInputProgram

variable {r Q Δ : ℕ}

def input (i : Fin Δ) (u y : UniversalType r Q Δ) (regs : Fin 8 → Bool) :
    MatrixInputAccess.Data :=
  inputState (CollisionProgram.encodeType u) (CollisionProgram.encodeType y)
    (List.replicate (i.val + 1) true) (List.replicate (Q * r) true)
    (List.replicate r true) (List.replicate Q true) regs

def output (i : Fin Δ) (u y : UniversalType r Q Δ) (regs : Fin 8 → Bool) :
    MatrixInputAccess.Data :=
  outputState (CollisionProgram.encodeType u) (CollisionProgram.encodeType y)
    (List.replicate (i.val + 1) true) (List.replicate (Q * r) true)
    (List.replicate r true) (List.replicate Q true)
    (encodeWord u.head) (encodeWord (u.slot i))
    (encodeWord y.head) (encodeWord (y.slot i))
    (decide (∀ j, j ≠ i → ∀ l, u.slot j l = y.slot j l)) regs

end SubexponentialSAT.Subexp.MatrixInputTypes

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixAnchorGuardProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Three physical byte comparisons for the selected joint coordinate. -/

namespace SubexponentialSAT.Subexp.MatrixAnchorGuardProgram

open BitProgram StructuredCalls StackRoutines

def compared (a : Data) (answer : Bool) : Data :=
  ⟨fun j => if j.val < 5 then false else a.regs j,
    Function.update (Function.update (Function.update a.stacks 1 []) 12 [])
      11 (answer :: a.stacks 11)⟩

def copied (a : Data) (src dst : Fin 42) : Data :=
  ⟨readRegs a.regs 0 1 none, copyStacks src dst a.stacks⟩

def popped (a : Data) : Data :=
  ⟨readRegs a.regs 3 4 (a.stacks 11).head?, Function.update a.stacks 11 (a.stacks 11).tail⟩
def accepted (a : Data) (expected : Bool) : Data :=
  ⟨Function.update a.regs 9 (a.regs 9 && (a.regs 3 == expected)), a.stacks⟩

def valid (a : Data) : Bool :=
  decide (a.stacks 38 = a.stacks 40 ∧ a.stacks 39 ≠ a.stacks 40 ∧ a.stacks 41 ≠ a.stacks 40)

def cost (a : Data) : ℕ :=
  18 * ((a.stacks 38).length + (a.stacks 39).length + (a.stacks 41).length) +
    27 * (a.stacks 40).length + 106

end SubexponentialSAT.Subexp.MatrixAnchorGuardProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixAnchorReadProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Read the selected color from each of four preserved word streams. The
position is a unary runtime cursor on stack37; color width is on stack21. -/

namespace SubexponentialSAT.Subexp.MatrixAnchorReadProgram

open BitProgram StructuredCalls StackRoutines

def readResult (a : Data) (row : List Bool) : Data :=
  ⟨readRegs a.regs 0 1 none,
    Function.update (Function.update a.stacks 2 []) 1 (row ++ a.stacks 1)⟩

def copied (a : Data) (src dst : Fin 42) : Data :=
  ⟨readRegs a.regs 0 1 none, copyStacks src dst a.stacks⟩
def transferred (a : Data) (src dst : Fin 42) : Data :=
  ⟨readRegs a.regs 0 1 none, transferStacks src dst a.stacks⟩
def moved (a : Data) (src dst : Fin 42) : Data := transferred (transferred a src 8) 8 dst
def cleared (a : Data) (src : Fin 42) : Data :=
  ⟨readRegs a.regs 0 1 none, clearStacks src a.stacks⟩

def readOneResult (a : Data) (i : Fin 4) (row : List Bool) : Data :=
  ⟨readRegs a.regs 0 1 none, Function.update a.stacks (target i) row⟩

end SubexponentialSAT.Subexp.MatrixAnchorReadProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixAnchorTypes
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Canonical one-hot color reads for the explicit joint-membership guard. -/

namespace SubexponentialSAT.Subexp.MatrixAnchorReadProgram

open BitProgram StructuredCalls StackRoutines MulticolorTypes

variable {r Q Δ : ℕ}

def fourReadResult (a : Data) (words : Fin 4 → List Bool) : Data :=
  readOneResult (readOneResult (readOneResult (readOneResult a 0 (words 0)) 1 (words 1))
    2 (words 2)) 3 (words 3)

end SubexponentialSAT.Subexp.MatrixAnchorReadProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixExtendedEntryProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed control for the zero-extended joint entry on arbitrary universal
types. The unary position cursor is preserved on37. -/

namespace SubexponentialSAT.Subexp.MatrixExtendedEntryProgram

open BitProgram StructuredCalls StackRoutines MatrixWordEncoding MulticolorTypes

variable {r Q Δ : ℕ}

def project {k s : ℕ} (hk : k ≤ 10) (hs : s ≤ 42) (a : Data) : State k s :=
  ⟨fun j => a.regs (j.castLE hk), fun j => a.stacks (j.castLE hs)⟩

def install {k s : ℕ} (a : Data) (b : State k s) : Data :=
  ⟨fun j => if h : j.val < k then b.regs ⟨j.val, h⟩ else a.regs j,
    fun j => if h : j.val < s then b.stacks ⟨j.val, h⟩ else a.stacks j⟩

def cleared (a : Data) (src : Fin 42) : Data :=
  ⟨readRegs a.regs 0 1 none, clearStacks src a.stacks⟩

open BitProgram StructuredCalls StackRoutines

def colorsCleared (a : Data) : Data :=
  cleared (cleared (cleared (cleared (cleared (cleared (cleared (cleared a 17) 18) 19) 20)
    38) 39) 40) 41

def clearColorsCost (a : Data) : ℕ :=
  2 * ((a.stacks 17).length + (a.stacks 18).length + (a.stacks 19).length +
    (a.stacks 20).length + (a.stacks 38).length + (a.stacks 39).length +
    (a.stacks 40).length + (a.stacks 41).length) + 24

open BitProgram StructuredCalls StackRoutines MatrixWordEncoding MulticolorTypes


end SubexponentialSAT.Subexp.MatrixExtendedEntryProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MismatchPlanProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical mismatch-position selection

The input consists of two packed arrays, a runtime row width, and a framed
list of numeric positions. Each callback reads the two rows with the actual
persistent array reader, compares their bytes, and emits exactly the unequal
positions. The arrays and their order are preserved.
-/

namespace SubexponentialSAT.Subexp.MismatchPlanProgram

open BitProgram StructuredCalls StackRoutines

abbrev state (regs : Regs) (left right width source payload acc output : Word) : Data :=
  ⟨regs, ![left, [], [], width, [], [], [], [], source, payload,
    right, [], [], acc, output, []]⟩

abbrev afterLookup (right : Bool) (row : Word) (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none,
    Function.update (Function.update a.stacks 2 []) (rowPort right) row⟩

def afterCopy (a : Data) : Data := ⟨readRegs a.regs 0 1 none, copyStacks 9 2 a.stacks⟩

abbrev afterEquality (a : Data) (answer : Bool) : Data :=
  ⟨fun j => if j.val < 5 then false else a.regs j,
    Function.update (Function.update (Function.update a.stacks 1 []) 12 [])
      11 (answer :: a.stacks 11)⟩

def invariant (left right : List Word) (width : Word) (a : Data) : Prop :=
  ∃ regs source payload acc,
    a = state regs left.flatten right.flatten width source payload acc []

end SubexponentialSAT.Subexp.MismatchPlanProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowMismatchProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Generate all positions on tape, then retain the mismatches.  The output
is in descending position order, as required by the prepend-based row loops. -/

namespace SubexponentialSAT.Subexp.UniversalRowMismatchProgram

open BitProgram StructuredCalls StackRoutines
open MismatchPlanProgram (indexRecords mismatch)

def state (regs : Regs) (left right width count index fuel source output : Word) : Data :=
  ⟨regs, ![left, [], [], width, [], index, fuel, [], source, [],
    right, [], [], [], output, [], count]⟩

end SubexponentialSAT.Subexp.UniversalRowMismatchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowMismatchTypes
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.allCompatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Read the two relevant words from the complete types, generate their
mismatch positions, and restore the temporary extracted words. -/

namespace SubexponentialSAT.Subexp.UniversalRowMismatchTypes

open BitProgram StructuredCalls StackRoutines MulticolorTypes

variable {r Q Δ : ℕ}

def InputReady (i : Fin Δ) (u y : UniversalType r Q Δ) (a : Data) : Prop :=
  ∀ j : Fin 29, a.stacks (inputStacks j) =
    (MatrixInputTypes.input i u y (a.regs ∘ inputRegs)).stacks j

def extractedStacks (a : Data) (i : Fin Δ) (u y : UniversalType r Q Δ) : Fin 49 → Word :=
  Function.update (Function.update (Function.update (Function.update a.stacks
    17 (ReadPlan.encodeWord u.head)) 18 (ReadPlan.encodeWord (u.slot i)))
    19 (ReadPlan.encodeWord y.head)) 20 (ReadPlan.encodeWord (y.slot i))

def cleared (a : Data) (port : Fin 49) : Data :=
  ⟨readRegs a.regs 0 1 none, clearStacks port a.stacks⟩

end SubexponentialSAT.Subexp.UniversalRowMismatchTypes

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTableProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual selected-factor table runs over ambient variable IDs. Each low
payload is specialized immediately before its framed table entry is retained.
The source scratch embedding excludes persistent layout masters. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives
open SubexpPolynomialConstructor PerturbationAssembly OAI.Algorithms.SubexponentialSAT.SubexpLiftRing

attribute [local simp] Fin.coe_ofNat_eq_mod

noncomputable def replaceInner (s : OuterStore) (u : Store) : OuterStore := Function.extend innerPort u s

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedyCode
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual supplied-code row payloads initialize_ the streamed selector. Raw
slot bounds retain repeated indices and zero coefficients, as the physical
assembler does; they do not substitute semantic support for retained data. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode

open SqrtLog
open scoped BigOperators
open HashGreedyCNF

noncomputable section

abbrev initial {m B : ℕ} (shifts : SparseCode.SuppliedShifts m B)
    (Q : SparseCode.SuppliedLocal m B) : List (List Bool) :=
  LeafScopeResourceBounds.initialPayloads (HashCandidates.digitWidth m)
    (CodeRowsProgram.serializedRows m shifts Q)

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashTrialStage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Exact finite staging extracted from `SqrtLog.LeafOuterNativeStage` for the
space-aware hash pipeline. Semantic query provenance remains in the original
module, while these declarations live in the stronger development's namespace. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafOuterNative
open OAI BitProgram StructuredCalls SqrtLog.LeafOuterProgram
open Subexp

def prefixTrial : Cmd 40 896 :=
  .seq (route (768,702))
    (.seq (TupleProgram.pushConst 701 0 false)
      (.seq (TupleProgram.escape trialPorts) (TupleProgram.pushConst 701 0 true)))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafOuterNative
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadEvaluationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete correction-mask checking for a head rescan. This local routine
preserves its input masters and charges every stack at every source prefix. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.HeadGate
open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram
open OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport

def budget (W bits : List Bool) (rows : List (List (List Bool))) (wanted : List Bool) : ℕ :=
  AttainedSignatureProgram.cost W bits rows+20*(signatureValue W bits rows).length+
    9*wanted.length+29*bits.length+52

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.HeadGate
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpTautologyProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual encoded-clause tautology testing

The outer iterator reads unary literal records. For each literal, a concrete
program builds its opposite's query, copies the preserved clause, and runs the
proved encoded membership program. All data-dependent repetition is in those
finite programs and the record iterator.
-/

namespace SubexponentialSAT.SubexpTautologyProgram

open BitProgram StructuredCalls

abbrev callback : Cmd 10 8 :=
  .seq negateQuery (.seq copyClause (.seq ExecCNFSubset.memberCall
    (.seq (RecordPrograms.atom (.copy 9 4))
      (.seq (ExecCNFSubset.clear 1) (.seq (ExecCNFSubset.clear 3)
        (.seq (ExecCNFSubset.clear 4) (ExecCNFSubset.clear 7)))))))

def UnaryPayload (bits : List Bool) : Prop := ∃ c, bits = Encoding.encodeNat c

abbrev finish : Cmd 10 8 :=
  .seq (ExecCNFSubset.clear 0) (RecordPrograms.atom (.push 1 9))

abbrev tautology : Cmd 10 8 :=
  .seq initializeCmd (.seq (RecordPrograms.iterate ports callback) finish)

def program := compiled tautology 0 1

end SubexponentialSAT.SubexpTautologyProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpTautologyFilterProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual tautological-clause filtering

The outer record loop runs the checked clause-tautology machine on each clause,
emits exactly the clauses that it rejects as tautologies, and restores their
original list order. The Boolean predicates below specify this concrete code;
they are not instructions available to the machine.
-/

namespace SubexponentialSAT.SubexpTautologyFilterProgram

open BitProgram StructuredCalls

def keepClause (bits : List Bool) : Bool :=
  match decodeClause bits with
  | none => false
  | some C => !(ExecCNF.tautology SubexpFrontend.negateCode C)

def coreProgram := ProgramLinking.liftProgram
  SubexpTautologyProgram.program coreRegister coreStack

abbrev coreCall : Cmd 13 11 := .call coreProgram

end SubexponentialSAT.SubexpTautologyFilterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNormalizationPrefixProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!+# Actual literal cleanup followed by tautology removal

This is a fixed program on the original declared variable universe. Its two
stages use the same input/output port and restore empty work stacks. The exact
list order and the length bound are retained for subsequent clause absorption.
-/

namespace SubexponentialSAT.SubexpNormalizationPrefixProgram

open BitProgram StructuredCalls

def preprocess (F : List (List ℕ)) : List (List ℕ) :=
  ExecCNF.removeTautologies SubexpFrontend.negateCode (ExecCNF.cleanLiterals F)

end SubexponentialSAT.SubexpNormalizationPrefixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNormalizationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!+# Fixed-control encoded CNF normalization

The common boundary uses stack 13 for the formula and empty work stacks.
Literal cleanup and tautology removal are lifted into that boundary here;
clause deduplication and strict-subset deletion use the same boundary.
-/

namespace SubexponentialSAT.SubexpNormalizationProgram

open BitProgram StructuredCalls

def bitFields (F : List (List ℕ)) : ExecClauseRelationScan.Formula :=
  F.map (List.map Encoding.encodeNat)

def Ready (d : Data) : Prop := ∀ i : Fin 16, i ≠ 13 → d.stacks i = []

end SubexponentialSAT.SubexpNormalizationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpEmptyClauseProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A preserving empty-clause test on the actual encoded leaf

The fixed program searches for the one-bit encoding of an empty clause.
The leaf on stack 9 and every other caller word are preserved.  Only the
five empty membership work ports and one empty copy port are used.
-/

namespace SubexponentialSAT.SubexpEmptyClauseProgram

open BitProgram StructuredCalls

def Ready (d : Data) : Prop :=
  (∀ i : Fin 10, i.val < 5 → d.stacks i = []) ∧ d.stacks 8 = []

def copied (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks 0 (d.stacks 9)⟩

def queryLoaded (d : Data) : Data :=
  ⟨Function.update d.regs 0 false, Function.update d.stacks 2 (false :: d.stacks 2)⟩

def cleared (i : Fin 10) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks i []⟩

def resetResult (d : Data) : Data :=
  ⟨fun i => if i = 0 then d.regs 4 else if i.val < 7 then false else d.regs i,
    d.stacks⟩

end SubexponentialSAT.SubexpEmptyClauseProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeLeafSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The leaf's serialized raw clauses and the selector's indexed clauses
have exactly the same ambient models. Repeated clauses or literals are not
assigned extra model multiplicity. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSemantics

open SqrtLog DisjointReuse
open scoped BigOperators

/-- Index the actual list of clauses without renaming any ambient variable. -/
def indexed {n : ℕ} (F : RawCNF n) (i : Fin F.length) : SAT.Clause (Fin n) :=
  ExecCNF.clauseSet (F.get i)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSemantics
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpCRTAtZero
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Direct evaluation of the explicit Hermite reconstruction at zero. The
algorithm needs only local corrections and scalar Horner evaluations; no
global shifted polynomial or final polynomial division is required. -/

namespace SubexponentialSAT.SubexpCRTAtZero

open Polynomial
open scoped BigOperators

noncomputable section

variable {A I : Type*} [CommRing A] [Fintype I] [DecidableEq I]

def value (θ : I → A) (D : ℕ) (a : I → A) (J : I → A[X]) : A :=
  ∑ i, (JetCRT.cofactor θ D i).eval 0 *
    (TruncatedInverse.correction θ D a J i).eval (-θ i)

end

end SubexponentialSAT.SubexpCRTAtZero

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryReconstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual streamed-jet handoff, scratch preparation, and canonical count
reconstruction. Readiness is derived from the produced ring masters. The target
and jets are mathematical properties of the actual query output; no evaluator
or readiness service is accepted by the produced-input theorem. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction

open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing OAI.Algorithms.SubexponentialSAT.SqrtLog
open DensePolynomialProgram LeafProgram
open LeafParametersProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

def prepareBudget (B : ℕ) : ℕ :=
  2*B+6+3*Count.Prepare.ports.length+2*Count.Prepare.ports.length*B

def coreBudget (B S : ℕ) : ℕ := prepareBudget B+ReconstructionNative.budget S

def budget (B S : ℕ) : ℕ := 8*B+10+coreBudget B S

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpIncidenceSlotProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical local-slot query

The three preserved inputs are the encoded scope family and unary factor and
vertex indices. A real mask pass selects the preceding factors, and the checked
incidence scan counts them. No slot map or selected prefix is supplied as input.
-/

namespace SubexponentialSAT.SubexpIncidenceSlotProgram

open BitProgram StructuredCalls

abbrev Data := StructuredProgram.State 10 13

abbrev data (regs : Fin 10 → Bool)
    (source index vertex answer sourceCopy mask query pre tmp aux count codes payload : List Bool) :
    Data := ⟨regs, fun i => if i = 0 then source else if i = 1 then index else
    if i = 2 then vertex else if i = 3 then answer else if i = 4 then sourceCopy else
    if i = 5 then mask else if i = 6 then query else if i = 7 then pre else
    if i = 8 then tmp else if i = 9 then aux else if i = 10 then count else
    if i = 11 then codes else payload⟩

def idle (regs : Fin 10 → Bool) (scopes : List (List ℕ)) (e v : ℕ) (answer : List Bool) : Data :=
  data regs (scopeBits scopes) (unary e) (unary v) answer [] [] [] [] [] [] [] [] []

abbrev seeded (regs : Fin 10 → Bool) (scopes : List (List ℕ)) (e v : ℕ) : Data :=
  data regs (scopeBits scopes) (unary e) (unary v) []
    (scopeBits scopes) (unary e) [] [] [] [] [] [] []

def selected (regs : Fin 10 → Bool) (scopes : List (List ℕ)) (e v : ℕ) : Data :=
  data regs (scopeBits scopes) (unary e) (unary v) []
    [] [] [] (scopeBits (scopes.take e)) [] [] [] [] []

def ready (regs : Fin 10 → Bool) (scopes : List (List ℕ)) (e v : ℕ) : Data :=
  data regs (scopeBits scopes) (unary e) (unary v) []
    [] [] ((Encoding.encodeNat v).reverse) (scopeBits (scopes.take e)) [] [] [] [] []

def scanned (regs : Fin 10 → Bool) (scopes : List (List ℕ)) (e v : ℕ) : Data :=
  data regs (scopeBits scopes) (unary e) (unary v) (unary (degree scopes e v))
    [] [] ((Encoding.encodeNat v).reverse) [] [] []
    (unary (scopes.take e).length) (indices scopes e v) []

def copied (src dst : Fin 13) (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none, StackRoutines.copyStacks src dst a.stacks⟩

def pushed (dst : Fin 13) (bit : Bool) (a : Data) : Data :=
  ⟨Function.update a.regs 0 bit, Function.update a.stacks dst (bit :: a.stacks dst)⟩

end SubexponentialSAT.SubexpIncidenceSlotProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_RingNodeSetup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Paid traversal of the actual framed node table. The remaining cursor and
unary index are physical stacks, and the decoded node is transferred to the
original factor port. No list of semantic nodes is manufactured by the machine. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.RingNodeSetup

open OAI BitProgram StructuredCalls StackRoutines
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram

/-- Project every named field without changing any other caller stack. -/
def storeOf (a : Data) : Store where
  frame := a.stacks
  source := a.stacks 301
  payload := a.stacks 302
  nodesRev := a.stacks 303
  jetsRev := a.stacks 304
  temporary := a.stacks 305
  index := a.stacks 307
  node := a.stacks 78
  jet := a.stacks 102
  shape := a.stacks 104
  nodesOut := a.stacks 256
  jetsOut := a.stacks 265

/-- Initial cursor setup includes clearing stale parser buffers and index. -/
def initNodes : Code :=
  .seq (clear 301) (.seq (clear 302) (.seq (clear 305)
    (.seq (clear 307) (.seq (clear 78) (copy 300 301)))))

/-- Consume one outer list tag, read its frame, and put the whole node at78. -/
def readNode : Code := .seq pop (.seq reader (transfer 302 78))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.RingNodeSetup
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed encoded modular dot products

Vectors are streams of framed, fixed-width little-endian scalar words. The
loop reads the two streams itself and calls the measured multiply-add routine.
Its finite control is independent of the modulus, width, and vector length.
-/

namespace SubexponentialSAT.Subexp.MatrixProgram

open BitProgram StructuredCalls BinaryArithmetic
open MatrixProgramSupport MatrixScalarProgram

def ready (regs : Fin 8 → Bool) (modulus acc : List Bool) (xs : List (List Bool))
    (right saved output zero input : List Bool) : MatrixScalarProgram.Data :=
  state (readRegs regs 0 1 (words xs).head?) [] [] modulus acc (words xs)
    right saved output zero input

end SubexponentialSAT.Subexp.MatrixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixVectorProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed row controller for encoded matrix-vector multiplication. -/

namespace SubexponentialSAT.Subexp.MatrixVectorProgram

open BitProgram StructuredCalls BinaryArithmetic
open MatrixProgramSupport MatrixScalarProgram MatrixProgram

abbrev readyMatrix (regs : Fin 8 → Bool) (modulus : List Bool) (xs : List (List Bool))
    (right output zero : List Bool) (m : ℕ) : MatrixScalarProgram.Data :=
  state (readRegs regs 0 1 (List.replicate m true).head?) [] [] modulus [] [] right
    (words xs) output zero (List.replicate m true).tail

end SubexponentialSAT.Subexp.MatrixVectorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryStreamBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed polynomial time envelopes for the actual conditioned stream. The
same original assembled resource pays the support/tuple work; all remaining
scalars and retained words enter only fixed polynomial coefficients. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamBudgets
open SqrtLog SubexpLiftRing SubexpQuarticRing
open CostAssembly.Polynomial QueryStreamCorrect

def reconstructionCoefficient : ℕ :=
  2400*(ReconstructionProgram.Native.costConstant+1)^4+
    5*LeafProgram.Count.Prepare.ports.length+39628

def scalarEnvelope (X : ℕ) : ℕ :=
  18*X+65*X+67+23*X+
    X*(20000*(X+1)^4+300*(X+1)+X+10+finishEnvelope X+1)+32+
    reconstructionCoefficient*(2*X+1)^96


open SqrtLog SqrtLog.Statement



open Filter SqrtLog SqrtLog.Statement


open SqrtLog SqrtLog.Statement

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamBudgets
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryStreamSpaceBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed polynomial space for the actual complete conditioned query.
Retained words and local arithmetic work are counted independently of the
number of support pairs, attained signatures, head assignments or nodes. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamSpaceBudgets
open OAI SqrtLog SubexpLiftRing
open CostAssembly.Polynomial

/-- The actual reconstruction bound includes all arithmetic temporaries and
whole count-word readback. Its exponent is fixed before the query. -/
def recoveryEnvelope (F X : ℕ) : ℕ :=
  (2400*(ReconstructionProgram.Native.costConstant+1)^4+
    5*LeafProgram.Count.Prepare.ports.length+39628)*(F+X+1)^96

/-- A sum dominates the actual nested prefix maxima; it never multiplies
space by the number of executed candidates or callbacks. -/
def envelope (F P X : ℕ) : ℕ :=
  F+(67*F+37)+(919*F+31)+P+
    (896*F+(20000*(F+1)^4+300*(F+1))+finishEnvelope F X+1)+
    (896*F+recoveryEnvelope F X)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamSpaceBudgets
end


