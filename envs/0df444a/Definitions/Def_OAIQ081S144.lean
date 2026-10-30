-- Prove2me | Definitions.Def_OAIQ081S144
-- name    : OAIQ081S144
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:49:42.518926+00:00
-- url     : https://prove2.me/theorems/c8742ac4-d556-4115-b470-e321172d80bd
-- title:
--   Definitions bundle OAIQ081S144 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 67 declarations of OpenAI's Lean: 61 definitions, 1 inductive type or structure and 5 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.compareTypes`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.delta`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.emit`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.literal`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.lookup`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.mismatches`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.one`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.stageTypes`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.zero`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.fiberLoop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceForOwner`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRowWith`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRowsWith`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native.ValidWord`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram.address`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram.choose`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram.copy`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram.emit`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram.lookup`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram.loop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram.setup`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram.test`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram.visit`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Address.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Address.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.factors`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.headCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.headResult`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.heads`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.initializeAddress`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.prepareHead`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.prepareHeadCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.preparedHead`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local.mergeStep`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.prepareHash`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.start` and 22 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_LayoutProgramSourceBank`, `SubexponentialSAT_SqrtLog_LayoutSourceRowsProgram`, `SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramController`, `SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramRow`, `SubexponentialSAT_SqrtLog_LayoutSourceValuesProgram`, `SubexponentialSAT_SqrtLog_LeafHeadFactorsProgram`, `SubexponentialSAT_SqrtLog_LeafHeadFactorsProgramLoop`, `SubexponentialSAT_SqrtLog_LeafHeadFactorsProgramRun`, `SubexponentialSAT_SqrtLog_LeafHeadFactorsProgramTest`, `SubexponentialSAT_SqrtLog_LeafHeadFactorsProgramVisit`, `SubexponentialSAT_SqrtLog_LeafHeadSetupProgramAddress`, `SubexponentialSAT_SqrtLog_LeafHeadSetupProgramBoot`, `SubexponentialSAT_SqrtLog_LeafHeadSetupProgramPrepare`, `SubexponentialSAT_SqrtLog_LeafHeadSetupProgramSelection`, `SubexponentialSAT_SqrtLog_LeafHighContextProgramBase`, `SubexponentialSAT_SqrtLog_LeafOuterProgramCode`, `SubexponentialSAT_SqrtLog_LeafOuterProgramPrepareCode`, `SubexponentialSAT_SqrtLog_LeafParametersProgramBankPred`, `SubexponentialSAT_SqrtLog_LeafParametersProgramNative`, `SubexponentialSAT_SqrtLog_LeafProgramAssignmentSemanticsCore`, `SubexponentialSAT_SqrtLog_LeafProgramExpansion`, `SubexponentialSAT_SqrtLog_LeafProgramIndicator`, `SubexponentialSAT_SqrtLog_LeafProgramNativeSemantics`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendCore`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramNative`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputNative`, `SubexponentialSAT_SqrtLog_ReconstructionProgramCofactorOuter`, `SubexponentialSAT_SqrtLog_ReconstructionProgramHorner`, `SubexponentialSAT_SqrtLog_ReconstructionProgramMiddle`, `SubexponentialSAT_SqrtLog_ReconstructionProgramNative`, `SubexponentialSAT_SqrtLog_ReconstructionProgramScalar`, `SubexponentialSAT_SqrtLog_ReconstructionProgramScalarSteps`, `SubexponentialSAT_SubexpKernelControl`, `SubexponentialSAT_Subexp_BasisTransposePlanProgram`, `SubexponentialSAT_Subexp_PackingLeftoverStage`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S116`, `OAIQ081S117`, `OAIQ081S118`, `OAIQ081S119`, `OAIQ081S120`, `OAIQ081S122`, `OAIQ081S123`, `OAIQ081S124`, `OAIQ081S125`, `OAIQ081S126` and `OAIQ081S127` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S156`, `OAIQ081S157`, `OAIQ081S158`, `OAIQ081S159`, `OAIQ081S160`, `OAIQ081S162` and `OAIQ081S165`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup.start_trace_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost.clause_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost.literal_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost.negative_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost.product_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost.row_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceForOwner_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRowWith_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRows_absent`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRows_absent_model`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRows_present_from_rows`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRows_relSpec`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram.test_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds.prepareHead_bound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.factors_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.heads_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.prepareHead_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local.merge_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.prepareHash_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics.clause_denote_scoped`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.CofactorOuter.command_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Horner.command_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle.command_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle.iteration_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Scalar.accumulate_run` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Scalar.negative_run`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup.start_trace_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost.clause_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost.literal_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost.negative_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost.product_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost.row_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Expansion.forward_original_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceForOwner_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRowWith_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRows_absent`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRows_absent_model`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRows_present_from_rows`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRows_relSpec`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram.test_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds.prepareHead_bound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.factors_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.heads_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.prepareHead_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local.merge_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.prepareHash_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics.clause_denote_scoped`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.CofactorOuter.command_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Horner.command_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle.command_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle.iteration_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Scalar.accumulate_run` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Scalar.negative_run`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S116
import Definitions.Def_OAIQ081S117
import Definitions.Def_OAIQ081S118
import Definitions.Def_OAIQ081S119
import Definitions.Def_OAIQ081S120
import Definitions.Def_OAIQ081S122
import Definitions.Def_OAIQ081S123
import Definitions.Def_OAIQ081S124
import Definitions.Def_OAIQ081S125
import Definitions.Def_OAIQ081S126
import Definitions.Def_OAIQ081S127

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpKernelControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed controller constructing the separated postfix source

The input contains literal payloads and the three nested lists of blocks,
color groups, and terms.  The controller only parses frames, copies bits,
and emits postfix tags.  It has no arithmetic callback and never builds a
Cartesian product of the inner lists.  Three unary stacks hold the pending
right-fold operators, so the emitted source has exactly the association of
`SubexpAlgorithm.momentExpression`.
-/

namespace SubexponentialSAT.SubexpKernelControl

open BitProgram StructuredCalls

/-! ## Fixed source-constructor control -/

/-! ## Concrete machine states and elementary traces -/

def setCounter (i : Fin 3) (word : Word) (a : Accumulator) : Accumulator :=
  if i = 0 then { a with outer := word }
  else if i = 1 then { a with groups := word }
  else { a with terms := word }

/-! The following induction rule accounts for actual executions of the fixed
payload body. Its premises will be proved for `termBody`, `groupBody`, and
`blockBody`; the exported whole-controller statement has no callback argument. -/

/-! ## Forward-output service boundary -/

end SubexponentialSAT.SubexpKernelControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingLeftoverStage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual generation of ascending vertex indices and the leftover scan in
the fixed packing controller. -/

namespace SubexponentialSAT.Subexp.PackingProgram

open BitProgram StructuredCalls PackingProgramSupport

theorem leftovers_save_cost (input : Input) (n : ℕ)
    (records : PackingLeftovers.Records) (result : PackingLeftovers.Snapshot)
    (regs : Fin 16 → Bool) (b : Data)
    (hb : b.stacks = fun i =>
      if i = 6 then SelectorProgram.rawRecords records
      else if i = 10 then PackingLeftovers.unary result.rank
      else if i = 11 then PackingLeftovers.unary result.address
      else if i = 12 then result.storage
      else if i = 13 then result.metadata
      else if i = 14 then result.addresses
      else if i = 30 then List.replicate n true
      else (inputState input regs).stacks i) :
    PackingPlumbing.cost leftoversSave b =
      6 * result.rank + 6 * result.metadata.length + 6 * result.addresses.length +
      3 * result.storage.length + 2 * (SelectorProgram.rawRecords records).length +
      2 * result.address + 32 := by
  simp [PackingPlumbing.cost, PackingPlumbing.Op.cost, leftoversSave,
    PackingPlumbing.move, PackingPlumbing.Op.next, hb, inputState,
    StackRoutines.transferStacks, StackRoutines.clearStacks, TupleProgram.pushedState]
  omega

end SubexponentialSAT.Subexp.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_BasisTransposePlanProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical transpose read-plan generation

Two unary countdowns visit columns and rows in decreasing order. Each visit
constructs the unary physical index by repeated copying and emits one actual
framed record. Prepending these visits produces the increasing transpose
read order directly. All counters are runtime stacks and the code is fixed.
-/

namespace SubexponentialSAT.Subexp.BasisTransposePlanProgram

open BitProgram StructuredCalls

def copy (src dst : Fin 7) : Code := .call (StackRoutines.copyProgram src dst 6 0 1)

def multiply : Code := UnaryForPrograms.forCmd (ports 5) (copy 0 4)

end SubexponentialSAT.Subexp.BasisTransposePlanProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBank
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual packed source dispatch. This program constructs each polynomial
source from computed metadata and raw scalar caches, not a supplied polynomial
table. The owner-fiber source sum is a separate outer traversal. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

def lookup : Code := .call (ProgramLinking.liftProgram LookupPair.program lookupRegs lookupPorts)
def compareTypes : Code := liftCommand TypeCompare.command 23 23 lowRegs lowPorts

def mismatches : Code := liftCommand UniversalRowMismatchTypes.command 23 45 lowRegs mismatchPorts

def stageTypes : Code := Staging.sequence 0 1 319 stageTypesOps

def delta : Code := .ite 7
  (Staging.action 0 1 319 (.copy 314 274))
  (Staging.action 0 1 319 (.copy 313 274))

def emit : Code := .call (ProgramLinking.liftProgram UniversalRowSourceProgram.program emitterRegs emitterPorts)
def literal (src : Fin 320) : Code :=
  liftCommand Literal.command 0 3 literalRegs (literalPorts src)
def zero : Code := literal 313
def one : Code := literal 314

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Complete finite controllers for source fiber sums and ambient source-row
serialization. Parameters are actual finite programs with paid contracts. -/

/-! A runtime owner-fiber fold of actual serialized polynomial sources. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls

attribute [local simp] Fin.coe_ofNat_eq_mod

def fiberLoop (source : Code) : Code := UnaryForPrograms.forCmd fiberPorts (fiberBody source)

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {Witness : Type*}

def sourceForOwner (source : Code) : Code := .seq findOwner (.seq zeroSource (fiberLoop source))

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

/-! Paid bank relocation and register reset for the native polynomial source
executor. The parameter is a finite BitProgram; the integration selects the
checked polynomial executor, never a polynomial-value instruction. -/

/-! The bytes produced by the runtime fold are the compiler output of the
same finite sum expression, including the empty-owner zero polynomial. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramRow
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One source row: actual owner scan, native per-incidence source generation,
postfix summation, and native polynomial evaluation. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def sourceRowWith (source : Code) : Code :=
  .seq (sourceForOwner source) (evaluateRow PolynomialExecutorProgram.flatProgram)

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramController
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed outer control, parameterized only by a finite native source command.
The concrete instantiation supplies the actual packed source dispatcher. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls

def sourceRowsWith (source : Code) : Code := .seq initializeSource
  (.seq LayoutSourcePlanLookup.Native.command
    (.seq (.ite 4 (rowsCommand (sourceRowWith source)) zeroRows) (clear 304)))

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceValuesProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! The scalar callback calls the actual integer numerator program, then the
actual binary-to-ring scaler. Its integer result is never supplied as input. -/


/-! Closed correction-table construction from type metadata and integer/ring
caches. No correction-scalar table is supplied to the program or theorem. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open MulticolorTypes IntegerRingLiftProgram
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram (WordPair pairValue pairLength)
open scoped BigOperators
attribute [local simp] Fin.coe_ofNat_eq_mod


namespace Native

def ValidWord {r Q d : ℕ} (A R t : ℕ) (ht : 0 < t) (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (invDenom : ModelCode t d)
    (u y : UniversalType r Q 1) (j : ℕ) (word : List Bool) : Prop :=
  ∃ hj : j < Q, ∃ out : ModelCode t d,
    word = RingProgram.flat out ∧
    (RingProgram.modelRing t ht hd a M cache).decode out =
      -((RingProgram.modelRing t ht hd a M cache).decode invDenom) *
        ((LayoutProgram.Numerator.value A R ⟨j,hj⟩ u y : ℤ) : a.O t)

end Native
end SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram


/-! Uniform polynomial accounting and per-index observation of generated
correction tables. All parameters describe actual bytes and runtime counts. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadFactorsProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Factor head selection uses the full original table and a paid ambient offset. -/
namespace SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

abbrev copy := Subexp.SupportSelectionProgram.copy

def lookup : Code := liftCommand SubexpHeadColorProgram.select 0 5 wordRegs wordPorts


end SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadFactorsProgramTest
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def address : Code := .seq (copy 31 40) (copy 39 40)

def test : Code := .seq address (.seq lookup (.seq clearAddress
  (.seq (copy 32 12) (HeadIdentifierProgram.readBit false))))

end SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadFactorsProgramVisit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def emit : Code := .seq (copy 39 34)
  (.seq (Subexp.TupleProgram.pushConst 34 0 false)
    (.seq (Subexp.SupportSelectionProgram.emit 0 (by decide))
      (Subexp.TupleProgram.pushConst 1 0 false)))

def choose : Code := .ite 4 emit (.base .skip)

def visit : Code := .seq test choose

end SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadFactorsProgramLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def loop : Code := UnaryForPrograms.forCmd loopPorts visit

end SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadFactorsProgramRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def setup : Code := .seq (copy 30 39) (Subexp.TupleProgram.pushConst 0 0 false)
def command : Code := .seq setup (.seq loop RegisterResetProgram.all)
def program := compiled command 30 0

end SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramAddress
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The node index and palette size are runtime inputs. This fixed program
initializes the head countdown and computes the first physical color address
by real unary multiplication. Subsequent heads increment that address. -/
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Address
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.BasisTransposePlanProgram

def command : _root_.OAI.Algorithms.SubexponentialSAT.Subexp.BasisTransposePlanProgram.Code := .seq (copy 2 5) (.seq multiply (copy 0 3))
def program := compiled command 2 4

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Address

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramBoot
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Per-node paid bootstrap: address multiplication, actual plan-record
counting, and construction of the integer interpolation coefficient cache. -/
noncomputable section

namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def initializeAddress : Code := stage Address.program addressRegs (by decide) addressInputs addressOutputs

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramSelection
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual original/factor ID selection from the common full word table.
The input masters are copied into an isolated lookup program, and its output
records are copied back before the entire lookup workspace is cleared. -/
noncomputable section

namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def heads : Code := stage HeadIdentifierProgram.FullTable.program id (by decide) headInputs headOutputs

def headResult (a : Data) (n : ℕ) (rows : List (List Bool)) (low : List Bool) (W z : ℕ) : Data :=
  returned id (by decide) headInputs headOutputs a
    (HeadIdentifierProgram.FullTable.result n rows low W z)
def headCost (a : Data) (n : ℕ) (rows : List (List Bool)) (low : List Bool) (W z : ℕ) :=
  stageCost id (by decide) headInputs headOutputs a
    (HeadIdentifierProgram.FullTable.result n rows low W z)
    (HeadIdentifierProgram.FullTable.budget n rows.length W low.length z)

def factors : Code := stage LeafHeadFactorsProgram.program id (by decide) factorInputs factorOutputs

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramPrepare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The complete head-selection stage. All three objects consumed by the
matrix/bucket phase are computed from runtime masters by fixed programs. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def prepareHead : Code := .seq heads (.seq support factors)

def preparedHead (a : Data) (regs : Fin 8 → Bool) (n N : ℕ) (rows : List (List Bool))
    (low : List Bool) (W z : ℕ) : Data :=
  factorResult (scatterResult (countResult (headResult a n rows low W z)) regs n
    (selectedHeads n rows low z)) n N rows W z

def prepareHeadCost (a : Data) (regs : Fin 8 → Bool) (n N : ℕ) (rows : List (List Bool))
    (low : List Bool) (W z : ℕ) : ℕ :=
  let b := headResult a n rows low W z
  let c := countResult b
  let d := scatterResult c regs n (selectedHeads n rows low z)
  headCost a n rows low W z+countCost b+scatterCost c regs n (selectedHeads n rows low z)+
    factorCost d n N rows W z

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end
end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHighContextProgramBase
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A paid parser pipeline stages the current physical high assignment. -/
namespace SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.BlockSearchPreparation

def mergeStep : Code := .call (ProgramLinking.liftProgram HighIncidenceProgram.Restriction.program id mergeStacks)
def command : Code := .seq maskStep (.seq copyCounter (.seq flattenStep (.seq copyMask mergeStep)))
def program := compiled command 0 3


end SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafOuterProgramPrepareCode
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafOuterProgram
open SubexponentialSAT BitProgram StructuredCalls

/-- Numerical preparation followed by physical cleanup of the entire worker bank. -/
abbrev prepareHash : Cmd 40 896 :=
  .seq LeafProgram.HashParameters.command clearWorker

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramBankPred
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank

open BitProgram StructuredCalls BinaryArithmetic

theorem maxTwo_eval (r : Regs) (w : Words) (a : Fin 64) :
    ∃ t rf word, Eval (maxTwoCmd a) t (state r w)
        (state rf (Function.update w a word)) ∧
      BinaryArithmetic.toNat word = max 2 (BinaryArithmetic.toNat (w a)) ∧ word.length ≤ (w a).length+2 ∧
      t ≤ 100*((w a).length+3) := by
  obtain ⟨t1,r1,v1,h1,hv1,hl1,ht1⟩ := pred_eval r w a
  let w1 := Function.update w a v1
  obtain ⟨t2,r2,v2,h2,hv2,hl2,ht2⟩ := pred_eval r1 w1 a
  let w2 := Function.update w1 a v2
  obtain ⟨t3,r3,v3,h3,hv3,hl3,ht3⟩ := addConst_eval r2 w2 a 2
  simp only [w1,w2,Function.update_self] at hv2 hl2 ht2 hv3 hl3 ht3
  refine ⟨t1+(t2+t3),r3,v3,?_,?_,by omega,by omega⟩
  · simpa only [maxTwoCmd,w2,w1,Function.update_idem] using h1.seq (h2.seq h3)
  · rw [hv3,hv2,hv1]
    omega

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native runtime leaf parameter production, integer guards, and paid setup.
The former composition modules are import-only compatibility shims. -/


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramBankRoots -/

/-! A fixed ten-comparison bit guard. All operands are runtime binary words.
This module states their data relation separately from parameter production. -/

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit

open BitProgram StructuredCalls BinaryArithmetic Bank

/-- Uniform exact semantic and physical-cost contract, discharged by the
concrete Boolean-stack routines for every instruction constructor. -/
theorem instruction_eval (i : Instr) (r : Regs) (w : Words) (h : Ready w i) :
    ∃ t rf word, Eval (command i) t (state r w)
        (state rf (Function.update w (output i) word)) ∧
      BinaryArithmetic.toNat word = value (values w) i ∧ word.length  ≤  lengthBound (values w) (lengths w) i ∧
      t  ≤  cost (values w) (lengths w) i := by
  cases i with
  | clear a =>
    have he := ArithmeticExpressionSupport.clear_eval (port a) (state r w)
    refine ⟨2*(w a).length+3,readRegs r 0 1 none,[],?_,rfl,le_rfl,le_rfl⟩
    rw [state_update] at he
    have hr : (state r w).regs = r := rfl
    rw [hr] at he
    simpa only [command, output, state_port] using he
  | load o bits =>
    obtain ⟨rf,he⟩ := load_eval r w o bits h
    exact ⟨2*bits.length,rf,bits,he,rfl,le_rfl,le_rfl⟩
  | copy a o ha =>
    obtain ⟨rf,he⟩ := copy_eval r w a o ha h
    exact ⟨7*(w a).length+5,rf,w a,he,rfl,le_rfl,le_rfl⟩
  | add a b o ha hb => exact add_eval r w a b o ha hb h
  | mul a b o ha hb => exact multiply_eval r w a b o ha hb h
  | pow a b o ha hb =>
    obtain ⟨t,rf,word,he,hv,hl,ht⟩ := power_eval r w a b o ha hb h
    refine ⟨t,rf,word,he,hv,hl,?_⟩
    simpa only [cost,values,lengths,PowerPrograms.runtimeBound,PowerPrograms.workBound,PowerPrograms.callbackBound,
      CounterPrograms.value_eq_toNat] using ht
  | quot a b o ha hb =>
    obtain ⟨t,rf,word,he,hv,hl,ht⟩ := quotient_eval r w a b o ha hb h.1 h.2
    exact ⟨t,rf,word,he,hv,hl.le,ht⟩
  | sqrt a o ha => exact sqrt_eval r w a o ha h
  | logSucc a => exact logSucc_eval r w a
  | addConst a k => exact addConst_eval r w a k
  | pred a => exact pred_eval r w a
  | maxTwo a => exact maxTwo_eval r w a

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramCircuitRun -/

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit

open BitProgram StructuredCalls BinaryArithmetic Bank

theorem instruction_shape (m : Model) (w : Words) (r : Regs) (hs : Shape m w)
    (i : Instr) (hi : Admissible m i) :
    ∃ t rf w', Eval (command i) t (state r w) (state rf w') ∧
      Shape (next m i) w' ∧ t ≤ cost m.val m.len i := by
  obtain ⟨t,rf,word,he,hv,hl,ht⟩ := instruction_eval i r w (shape_ready m w hs i hi)
  have hval : values w=m.val := funext hs.1
  rw [hval] at hv hl ht
  have hl' := hl.trans (lengthBound_mono m.val (lengths w) m.len hs.2 i)
  have ht' := ht.trans (cost_mono m.val (lengths w) m.len hs.2 i)
  refine ⟨t,rf,Function.update w (output i) word,he,⟨?_,?_⟩,ht'⟩
  · intro a
    by_cases ha : a=output i
    · subst a; simpa [next] using hv
    · simpa [next,ha] using hs.1 a
  · intro a
    by_cases ha : a=output i
    · subst a; simpa [next] using hl'
    · simpa [next,ha] using hs.2 a

/-- Execute a fixed finite arithmetic circuit. Its returned bound includes
all arithmetic, copying, and every nested loop in the concrete primitives. -/
theorem program_eval (is : List Instr) (m : Model) (w : Words) (r : Regs)
    (hs : Shape m w) (hi : AdmissibleCode is m) :
    ∃ t rf w', Eval (program is) t (state r w) (state rf w') ∧
      Shape (result is m) w' ∧ t ≤ budget is m := by
  induction is generalizing m w r with
  | nil => exact ⟨0,r,w,.base (.skip _),hs,le_rfl⟩
  | cons i is ih =>
    obtain ⟨t,rf,w',he,hs',ht⟩ := instruction_shape m w r hs i hi.1
    obtain ⟨u,rg,w'',hf,hs'',hu⟩ := ih (next m i) w' rf hs' hi.2
    exact ⟨t+u,rg,w'',he.seq hf,hs'',Nat.add_le_add ht hu⟩

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramLayout -/


namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.GuardSetup

open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

def upper (m : Model) (j : Fin 10) : ℕ :=
  match j.val with
  | 0 => m.val 1
  | 1 => m.val 0
  | 2 => m.val 2
  | 3 => m.val 3
  | 4 => m.val 4
  | 5 | 8 => m.val 7
  | 6 | 7 => m.val 21
  | _ => m.val 1

def lower (m : Model) (j : Fin 10) : ℕ :=
  match j.val with
  | 0 | 2 | 3 | 4 => 1
  | 1 | 5 => m.val 1
  | 6 => 2
  | 7 => 4*m.val 29
  | 8 => 4*(m.val 3+m.val 4)*(m.val 31)^2*(m.val 25)^2
  | _ => 16*m.val 21*(m.val 18)^2

end SubexponentialSAT.SqrtLog.LeafParametersProgram.GuardSetup


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramPrepared -/


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafOuterProgramCode
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The complete outer leaf instruction table. The two remaining arguments
are actual native commands for the mass and final accepted-count services.
All setup, code search, serialization, selector iteration and positivity
testing below are fixed programs, independent of the input dimensions. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram

open SubexponentialSAT BitProgram StructuredCalls

abbrev start : Cmd 40 896 :=
  .seq LeafProgram.ClauseCount.caller (.seq prepareHash saveWidth)

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNativeSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Validity and storage bounds for the actual raw dictionaries produced by
native hash-row execution. No canonical-output premise is used. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram
open HashCircuitProgram
open HashCircuitProgram.Native

structure Good {n B d : ℕ} (vars : Finset (Fin n)) (u J : ℕ)
    (a : List (Product.Entry n B d)) : Prop where
  valid : ∀ x ∈ a, Product.ValidKey vars u J x.1
  nodup : (Squarefree.Sparse.keys a).Nodup

end SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics


/-! Denotation of the concrete raw row recurrence used by the native program. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram
open HashCircuitProgram
open HashCircuitProgram.Native
open scoped BigOperators

noncomputable def rawDenote {R : Type*} [CommRing R] {n B d : ℕ}
    (f : RingProgram.Code (Word B) d → R) (a : List (Product.Entry n B d)) :
    Squarefree.Jet (Fin n) R := Squarefree.Sparse.denote (Dictionary.denoteTable f a)

end SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics


/-! Instantiation at the actual supplied-polynomial unramified ring. -/


/-! Original literal identifiers remain unchanged when the native dictionaries
carry padded jets from the free coordinates of a branch. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramAssignmentSemanticsCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Typed selected-ID semantics of the actual factor fold. Neutral IDs are
skipped, including in the output list; no redundant multiplication is added. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics

open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open NativeSemantics
open scoped BigOperators

variable {p t n d : ℕ} [Fact p.Prime]

abbrev Raw := List (MomentsProgram.Product.Entry n (baseWidth p t) d)

end SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramExpansion
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native expansion of one selected raw hash row.  The row is read from the
dispatcher result; every original clause lookup and coefficient lift is paid
by the fixed assembler.  The original formula and dynamic width words are
read in place, so they remain available for the next factor. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Expansion

open SubexponentialSAT BitProgram StructuredCalls

def outputWord (t d : ℕ) (clauses : List (List Bool))
    (terms : List (Fin clauses.length × ZMod 3)) : List Bool :=
  Encoding.encodeList id (terms.map (HashInputProgram.Loop.payload t d clauses))

end SubexponentialSAT.SqrtLog.LeafProgram.Expansion

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramIndicator
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A closed native sparse-hash indicator service. It first interprets the
actual inline weighted-clause row and then applies the computed idempotent
coefficient tape. The resulting indicator is never supplied as input. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Indicator

attribute [local simp] Fin.addCases

open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps
open MomentsProgram

noncomputable abbrev command : Cmd 8 96 :=
  .seq (.call HashCircuitProgram.Native.program) IdempotentApplyProgram.command

noncomputable def program := compiled command 64 67

end SubexponentialSAT.SqrtLog.LeafProgram.Indicator

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Joined per-query core. Mathematical values below describe physical input
words and computed outputs; they are not extra machine inputs. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

def Query.scopeRows (q : Query) := HashScopeProgram.Complete.scopes 1 0 q.codes q.rows q.mark
def Query.forward (q : Query) := (highMask q.scopeRows (BinaryArithmetic.toNat q.ambient)).reverse

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramNative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! The fixed executable preparation pipeline.  Its input is the actual
numerical bank emitted by `LeafParametersProgram`; no field polynomial,
modulus, multiplication table, nodes, or idempotent coefficients are inputs.
The stage-by-stage execution theorem is separate from this code definition.
-/


/-! Arithmetic consumers use the same bytes generated by the preceding
stages.  These are structural handoff lemmas; the complete production
trace must establish `NativeBytes` before invoking them. -/

namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls StackRoutines

/-- Finite staged cache copies; this is executable code, including clearing
reused destinations and the preserving copy loops. -/
def copyPlan : List (Fin 640 × Fin 640) → Cmd 32 640
  | [] => .base .skip
  | p::ps => .seq (overwrite p.1 p.2) (copyPlan ps)

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! Convert a physically scanned factor-index stream to incidence plans. -/


/-! Native per-variable incident-factor scan from the original scope stream. -/


/-! Fixed cleanup for the native scope-address scanner. -/


/-! Calls to the fixed record mapper inside the native scope scan. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Lift
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
abbrev Data := Scan.Data
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Lift


/-! One native low-variable step, including its uncovered neutral factor. -/


/-! Runtime high-mask loop for the original-address incidence stream. -/


/-! Count the physical scope stream before constructing native incidence plans. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramCofactorOuter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.CofactorOuter

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpCRTOuterProgram
open CRTLocalProgram (ServiceSpec LowFrame)

local infixr:55 " ;; " => seq

abbrev command (multiply : Cmd 16 256) : Code :=
  copy 258 215 ;; copy 257 215 ;; copy 207 240 ;;
    lowerCall (Cofactor.scan multiply) 215 240 ;; move 240 262

end SubexponentialSAT.SqrtLog.ReconstructionProgram.CofactorOuter

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramHorner
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical staging of local CRT correction evaluation. The dense correction
is consumed from 244; its value at the retained point 263 is returned on 264. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Horner

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpCRTOuterProgram
open CRTLocalProgram (ServiceSpec LowFrame)

local infixr:55 " ;; " => seq

abbrev command (multiply add : Cmd 16 256) : Code :=
  move 244 246 ;; copy 263 247 ;; copy 243 248 ;; copy 104 250 ;; copy 104 240 ;;
  lowerCall (HornerProgram.command multiply add) 246 240 ;;
  move 240 264 ;; clearMany [247,250]

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Horner

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramScalar
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Framed outer calls to the native scalar ring arithmetic. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Scalar

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpCRTOuterProgram
open CRTLocalProgram (ServiceSpec LowFrame)

local infixr:55 " ;; " => seq_p0

abbrev binary (code : Cmd 16 256) (src right dst : Fin 320) : Code :=
  copy src 240 ;; copy right 241 ;; lowerCall code 240 244 ;; clear dst ;;
  move 244 dst ;; clearMany [240,241]

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Scalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramScalarSteps
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Scalar

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpCRTOuterProgram
open CRTLocalProgram (ServiceSpec)

local infixr:55 " ;; " => seq_p1

abbrev negative (multiply : Cmd 16 256) : Code := binary multiply 259 211 263

abbrev accumulate (multiply add : Cmd 16 256) : Code :=
  binary multiply 262 264 263 ;; binary add 261 263 261 ;; clearMany [262,263,264]

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Scalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramMiddle
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Composition of the physical arithmetic stages for one Hermite node. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpCRTOuterProgram
open CRTLocalProgram (LowFrame ServiceSpec)

local infixr:55 " ;; " => seq

abbrev command (localCode multiply add : Cmd 16 256) : Code :=
  CofactorOuter.command multiply ;; Scalar.negative multiply ;; Local.command localCode ;;
    Horner.command multiply add ;; Scalar.accumulate multiply add

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One finite instruction table for arbitrary dynamic coefficient degree,
ring precision, node count, and jet order. All such parameters reside on
input tapes. The scalar and polynomial services here are concrete programs. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Native

open SubexponentialSAT BitProgram StructuredCalls

/-- Fixed local correction producer, with native scalar and array services. -/
abbrev localCode : Cmd 16 256 :=
  CRTLocalProgram.localCommand HornerProgram.Services.multiply HornerProgram.Services.add
    DensePolynomialProgram.Fixed.mulCommand DensePolynomialProgram.AddService.command

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Native

end OAI.Algorithms
end


