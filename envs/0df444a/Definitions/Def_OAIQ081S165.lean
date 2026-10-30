-- Prove2me | Definitions.Def_OAIQ081S165
-- name    : OAIQ081S165
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T23:09:16.500079+00:00
-- url     : https://prove2.me/theorems/bbbf95a7-af02-4687-8866-dcf3f16b00b5
-- title:
--   Definitions bundle OAIQ081S165 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 132 declarations of OpenAI's Lean: 97 definitions, 11 inductive types or structures and 24 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.ZeroInvariant`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.FactorInput`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.StagedInput`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.lowOutput`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentLoop.recordState`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentLoop.state`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram.callbackFinished`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram.cleared`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram.moved`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram.returned`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.ScalarMasters`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.sourceCallData`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.ExecutesOuter`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.RelLiteralBody`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumAssembly.clearWorkCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumAssembly.cleared`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.Cursor`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.bodyBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.finalized`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.gateValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.powerResult`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.seeded`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountSeed.branch`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountSeed.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountSeed.initializeCmd`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountSeed.initializeProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountSeed.initialized`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountSeed.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountSeed.result`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.cleanupProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.highSet`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.NativeHeadSelect.resetCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.NativeHeadSelect.resetState`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.NativeOverlay.resetCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.NativeOverlay.resetState`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.copyHighCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.highCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.prepareHigh`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.resetHighCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.resetHighState` and 68 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_FactorAssignmentLoop`, `SubexponentialSAT_SqrtLogSpace_FactorAssignmentProgram`, `SubexponentialSAT_SqrtLogSpace_FactorTableNative`, `SubexponentialSAT_SqrtLogSpace_FactorTableProgram`, `SubexponentialSAT_SqrtLogSpace_HeadSumAssembly`, `SubexponentialSAT_SqrtLogSpace_HeadSumProgram`, `SubexponentialSAT_SqrtLogSpace_HighCountSeed`, `SubexponentialSAT_SqrtLogSpace_HighFrontendMask`, `SubexponentialSAT_SqrtLogSpace_HighMarkedCleanup`, `SubexponentialSAT_SqrtLogSpace_HighQueryAdapter`, `SubexponentialSAT_SqrtLogSpace_HighQueryExecution`, `SubexponentialSAT_SqrtLogSpace_HighQueryProgram`, `SubexponentialSAT_SqrtLogSpace_HighQuerySetup`, `SubexponentialSAT_SqrtLogSpace_HighQueryStart`, `SubexponentialSAT_SqrtLogSpace_NativeLayoutLoad`, `SubexponentialSAT_SqrtLogSpace_NativeLeafRun`, `SubexponentialSAT_SqrtLogSpace_NativeLeafStartup`, `SubexponentialSAT_SqrtLogSpace_NativeQueryPreparation`, `SubexponentialSAT_SqrtLogSpace_NodeAppendSpace`, `SubexponentialSAT_SqrtLogSpace_NodeReadoutSpace`, `SubexponentialSAT_SqrtLogSpace_QueryIncidenceCommand`, `SubexponentialSAT_SqrtLogSpace_QueryNodeFinish`, `SubexponentialSAT_SqrtLogSpace_QueryProducerSpace`, `SubexponentialSAT_SqrtLogSpace_QueryProgram`, `SubexponentialSAT_SqrtLogSpace_QueryRepresentativeFold`, `SubexponentialSAT_SqrtLogSpace_QueryTupleSum`, `SubexponentialSAT_SqrtLogSpace_RingNodeMetadata`, `SubexponentialSAT_SqrtLogSpace_SignatureHeadLoaderCore`, `SubexponentialSAT_SqrtLogSpace_SignatureTupleLoader`, `SubexponentialSAT_SqrtLog_LayoutBinomialProgramCell`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyFactorInput`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyLow`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyRelInput`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S139`, `OAIQ081S142`, `OAIQ081S144`, `OAIQ081S145`, `OAIQ081S146`, `OAIQ081S150`, `OAIQ081S151` and `OAIQ081S152` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S172` and `OAIQ081S179`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedSpace.head_resources_of_local_time`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSelectionSpace.prepare_trace_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.body_cursor_next`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.body_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumSpace.scan_resources`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighBranchSpace.prepare_high_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountSeed.initialize_trace_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountSeed.trace_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryExecution.markedReturn_trace_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop.prepare_high_resources`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryStart.resources`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.staged_rounds_time_hashCalls`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun.ready_rounds`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace.run_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.localResult_nonoutput_length`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.localResult_outputs` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.result_headsize`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableSpace.staged_stack_bound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMarkedReturn.cost_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMarkedReturn.trace_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedCorrect.overlay_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedSpace.accumulate_return_bound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedSpace.head_resources_of_local_time`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSelectionSpace.prepare_trace_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumCorrect.prepared_head_update`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.accumulate_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.body_cursor_next`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.body_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.finalize_prefix`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumSpace.scan_resources`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumSpace.seed_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighBranchSpace.prepare_high_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountSeed.initialize_trace_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountSeed.trace_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryExecution.markedReturn_trace_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop.add_rank`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop.advance_resources`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop.prepare_high_resources`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryStart.resources`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun.ready_rounds`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace.run_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.localResult_nonoutput_length`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.localResult_outputs`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.result_headsize` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.binomial_eval`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S139
import Definitions.Def_OAIQ081S142
import Definitions.Def_OAIQ081S144
import Definitions.Def_OAIQ081S145
import Definitions.Def_OAIQ081S146
import Definitions.Def_OAIQ081S150
import Definitions.Def_OAIQ081S151
import Definitions.Def_OAIQ081S152

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutBinomialProgramCell
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Consolidated fixed-control binomial-cache implementation. Component module
paths re-export this file so all interfaces remain stable. -/

/-! A Pascal cell saves the old entry, adds and emits the new entry, then
restores the saved entry as the carry. Every copy and clear is paid. -/

/-! One paid Pascal row pass over the framed cache. -/

/-! A fixed while loop consumes the runtime unary iteration count. -/

/-! A fixed loop builds the initial zero cache row from a runtime unary
length. The constant program contains one record, independent of that length. -/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram
open SubexponentialSAT.SqrtLog.LayoutProgramScalar

def ZeroInvariant (base : State 8 18) (i : ℕ) (d : State 8 18) : Prop :=
  d.stacks 15 = pairEncoding (List.replicate i ([],[])) ∧
  ∀ j, j ≠ 15 → j ≠ 17 → d.stacks j = base.stacks j

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

/-! One fixed program builds the complete unsigned binomial row from the unary
runtime parameters h and R. No coefficient or initial cache is free input. -/

/-! A fixed component routine copies the runtime width, pads or truncates one
word, and consumes that word into a reverse output buffer. -/

/-! Generic framed unsigned rows are converted to flat signed-component
arrays at a supplied runtime width. Both output arrays are physically built.
-/

/-! Finish the generic cache adapter by reversing both physically accumulated
arrays. The common width is preserved for downstream indexed reads. -/

/-! Value and shape contracts for the generic adapter and binomial row. -/

/-! Complete fixed-control binomial cache construction. The three parameters
are runtime unary stacks; the output consists of actual flat fixed-width
positive and negative arrays in increasing column order. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyLow
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Closed low-variable incidence preparation from physical coefficient rows.
Beta evaluation, point construction, polynomial Horner, sparse emission, and
cache restoration are all performed by fixed finite commands. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open DensePolynomialProgram
open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def lowOutput (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (J N : ℕ) (theta : Coeff (baseWidth 3 t) d)
    (rows : List (Fixed.Array (baseWidth 3 t) d N × Bool)) (old : List Bool) : List Bool :=
  rowsResult (scanStep (RingProgram.modelProgram t a M cache) J rows.length N theta)
    0 (rows.map Prod.fst)
    (Encoding.frame (originKey rows.length) ++
      Encoding.frame (RingProgram.flat (PerturbationBetaProgram.runValue t a M cache theta
        (pairedRows rows))) ++ old)

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryProducerSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Immediate Boolean specialization followed by the actual additive dictionary
normalizer. The input is a polynomial-size origin/singleton incidence stream;
no multivariate product is materialized before specialization. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open MomentsProgram TruncatedRingProgram
open scoped BigOperators

def state (regs : Fin 8 → Bool) (modulus width degree dict source : List Bool)
    (scan : MomentsProjectionProgram.Tape) : State 8 38 :=
  ⟨regs, fun i => Fin.addCases (m := 28) (n := 10) (motive := fun _ => List Bool)
    (Normalize.state regs modulus width degree dict source).stacks
    (MomentsProjectionProgram.tapes scan) i⟩

def frameData (regs : Fin 8 → Bool) (modulus width degree remaining output : List Bool) :
    State 8 38 := state regs modulus width degree [] [] {input := output, tmp2 := remaining}

def frameReady (regs : Fin 8 → Bool) (modulus width degree remaining output : List Bool) :
    State 8 38 := frameData (readRegs regs 0 1 remaining.head?)
      modulus width degree remaining output

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryIncidenceCommand
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed native incidence command and its physical port ABI. The definitions
are extracted unchanged from the same emitter-specializer composition. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace
open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog MomentsProgram
open SubexpScanPrimitives SubexpSetupStorage

namespace Native

def joinedState (regs : Fin 16 → Bool) (low : Fin 256 → List Bool)
    (high : Fin 38 → List Bool) : State 16 294 :=
  ⟨regs, fun i => Fin.addCases (m := 256) (n := 38) (motive := fun _ => List Bool) low high i⟩

@[simp] theorem joinedState_low (regs : Fin 16 → Bool) (low : Fin 256 → List Bool)
    (high : Fin 38 → List Bool) (i : Fin 256) :
    (joinedState regs low high).stacks (lowPorts i) = low i := by
  simp [joinedState, lowPorts]

@[simp] theorem joinedState_high (regs : Fin 16 → Bool) (low : Fin 256 → List Bool)
    (high : Fin 38 → List Bool) (i : Fin 38) :
    (joinedState regs low high).stacks (producerPorts i) = high i := by
  simp [joinedState, producerPorts]

def emptyHigh (mask : List Bool) : Fin 38 → List Bool :=
  (state (fun _ => false) [] [] [] [] [] {target := mask}).stacks

def highPorts : List (Fin 294) := (List.finRange 38).map producerPorts

def finishCommand : Cmd 16 294 := .seq outputMove (clearMany highPorts)

def finished (a : State 16 294) : State 16 294 := clearManyState highPorts (movedOutput a)

end Native
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace
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

structure ExecutesOuter (code : OuterCode) (K : ℕ) (before after : OuterStore) : Prop where
  run : ∀ regs : Fin 16 → Bool, ∃ k rf, k≤K ∧
    Eval code k (⟨regs,before⟩ : OuterData) (⟨rf,after⟩ : OuterData)

/-- The payload is existential after the actual incoming registers, not before
all executions. The accumulator bound is the complete table's size bound. -/
structure RelLiteralBody (s : OuterStore) (body : OuterCode)
    (P : ℕ → List Bool → Prop) (K n L : ℕ) : Prop where
  run : ∀ j, j<n → ∀ acc, acc.length≤n*literalRecordBound n L →
    ∀ regs : Fin 16 → Bool, ∃ bits k rf,
      k≤K ∧ bits.length≤L ∧ P j bits ∧
      Eval body k (⟨regs,literalReady s (List.replicate j true) acc⟩ : OuterData)
        (⟨rf,literalReady s (List.replicate j true)
          (Encoding.frame (Encoding.encodeNat j)++Encoding.frame bits++acc)⟩ : OuterData)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The accepted-assignment factor product uses the original finite-ring
indicator and clause programs after the concrete specialized table producer.
Every cache is rebuilt from persistent source words by paid native copies;
neutral factor IDs leave the running multiplicative identity unchanged. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram

open OAI BitProgram StructuredCalls SubexpSetupStorage
open SqrtLog SqrtLog.LeafProgram
noncomputable section

def cleared (a : Data) (src : Fin 896) : Data :=
  ⟨readRegs a.regs 0 1 none, Function.update a.stacks src []⟩

def moved (a : Data) (src dst : Fin 896) : Data :=
  ⟨readRegs a.regs 0 1 none,
    Function.update (Function.update a.stacks dst (a.stacks src ++ a.stacks dst)) src []⟩

def returned (a : Data) : Data :=
  ⟨Function.update (Function.update (Function.update a.regs 13 false) 14 true) 15 false,
    a.stacks⟩

def callbackFinished (a : Data) : Data := returned (cleared a 149)

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Relational execution of the fixed specialized factor-record loop. This
adapts the original FactorLoop reader/while proof to the shared 896-stack ABI
and empty-support dictionaries. The explicit callback premise must be proved
for the actual callback before this component can close an algorithm endpoint. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentLoop
attribute [local simp] Fin.coe_ofNat_eq_mod
open OAI BitProgram StructuredCalls SqrtLog SqrtLog.LeafProgram MomentsProgram

def state {n B d : ℕ} (base : Fin 896 → List Bool) (regs : Fin 40 → Bool)
    (seed : Raw n B d) (source payload : List Bool) : FactorAssignmentProgram.Data :=
  ⟨regs,Function.update (Function.update (Function.update base 151 (Product.bytes seed))
    150 source) 149 payload⟩

def recordState {n B d : ℕ} (base : Fin 896 → List Bool) (regs : Fin 40 → Bool)
    (seed : Raw n B d) (v pr f : Bool) (source payload : List Bool) : FactorAssignmentProgram.Data :=
  RecordPrograms.state FactorAssignmentProgram.ports (state base regs seed [] []) v pr f source payload

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentLoop
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyFactorInput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One invariant of the physically staged masters yields every per-literal
low-worker precondition. No beta, shifted polynomial, or output table occurs
as an input hypothesis. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls DensePolynomialProgram SubexpConvolutionControl
open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
attribute [local simp] Fin.coe_ofNat_eq_mod

structure FactorInput (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (J N : ℕ) (theta : Coeff (baseWidth 3 t) d)
    (rows : FactorRows t N (d:=d)) (s : OuterStore) (n : ℕ) : Prop where
  arithmetic : ArithmeticInput t a M cache (projectInner s)
  widthPositive : 0 < baseWidth 3 t
  zeroCanonical : BinaryArithmetic.toNat cache.zero.val < 3^t
  zeroBits : RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1=
    List.replicate (d*baseWidth 3 t) false
  rowsLength : ∀ j,j < n → (rows j).length=n
  choices : ∀ j,j < n → s 546=(rows j).map Prod.snd
  zeroWord : s 547=RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1
  oneWord : s 548=RingProgram.flat (RingProgram.modelProgram t a M cache).oneRun.1
  thetaWord : s 549=RingProgram.flat theta
  sourceCount : (s 550).length=N
  wordWidth : (s 551).length=d*baseWidth 3 t
  ambientCount : s 552=List.replicate n true
  targetCount : s 553=List.replicate J true
  workEmpty : ∀ i∈lowScratch,205 ≤ i.val → s (innerPort i)=[]

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyRelInput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Common physical input invariant, independent of whichever exact source
arrays are returned by the next native source execution. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls DensePolynomialProgram SubexpConvolutionControl
open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
attribute [local simp] Fin.coe_ofNat_eq_mod

structure StagedInput (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (J N : ℕ) (theta : Coeff (baseWidth 3 t) d) (s : OuterStore) (n : ℕ) : Prop where
  arithmetic : ArithmeticInput t a M cache (projectInner s)
  widthPositive : 0 < baseWidth 3 t
  zeroCanonical : BinaryArithmetic.toNat cache.zero.val < 3^t
  zeroBits : RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1=
    List.replicate (d*baseWidth 3 t) false
  choicesLength : (s 546).length=n
  zeroWord : s 547=RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1
  oneWord : s 548=RingProgram.flat (RingProgram.modelProgram t a M cache).oneRun.1
  thetaWord : s 549=RingProgram.flat theta
  sourceCount : (s 550).length=N
  wordWidth : (s 551).length=d*baseWidth 3 t
  ambientCount : s 552=List.replicate n true
  targetCount : s 553=List.replicate J true
  workEmpty : ∀ i∈lowScratch,205 ≤ i.val → s (innerPort i)=[]

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTableNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical source preparation for the specialized factor table. The old
master-word argument is generalized to the actually selected unary factor,
then transported through the fixed protected-port embedding. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative
open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram
open PerturbationAssembly LayoutProgram SubexpSetupStorage DensePolynomialProgram
open OAI.Algorithms.SubexponentialSAT.Subexp OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking OAI.Algorithms.SubexponentialSAT.MulticolorTypes
attribute [local simp] Fin.coe_ofNat_eq_mod

structure ScalarMasters (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (J R : ℕ) (theta : Coeff (baseWidth 3 t) d) (s : OuterData) (n : ℕ) : Prop where
  widthPositive : 0<baseWidth 3 t
  zeroCanonical : BinaryArithmetic.toNat cache.zero.val<3^t
  zeroBits : RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1=
    List.replicate (d*baseWidth 3 t) false
  modulus : s.stacks 194=M.bits
  width : (s.stacks 202).length=baseWidth 3 t
  zero : s.stacks 203=cache.zero.val
  table : s.stacks 201=RingTriple.tableEncoding (HornerProgram.modelTable t a M cache)
  degree : (s.stacks 204).length=d
  choicesLength : (s.stacks 145).length=n
  zeroWord : s.stacks 280=RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1
  oneWord : s.stacks 207=RingProgram.flat (RingProgram.modelProgram t a M cache).oneRun.1
  thetaWord : s.stacks 78=RingProgram.flat theta
  ambientCount : s.stacks 128=List.replicate n true
  targetCount : s.stacks 243=List.replicate J true
  radius : s.stacks 138=List.replicate R true
  highLength : (s.stacks 703).length=n

variable {r Q d n J S f : ℕ}
  {ps : List (ℕ × ℕ)}
  {P : PackingData (Fin ps.length) (UniversalType r Q 1)}
  {a : SourceReady.Data}




/-- One iteration carries the actual original-variable counter, retained
lookup accumulator and its unary key into the source call. -/
def sourceCallData (s : FactorTableProgram.OuterStore) (j : ℕ) (acc : List Bool)
    (regs : Fin 16 → Bool) : FactorTableProgram.OuterData :=
  ⟨regs, Function.update (FactorTableProgram.literalReady s (List.replicate j true) acc)
    555 (Encoding.encodeNat j)⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSumProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The head rescan retains one raw Boolean assignment and a binary countdown.
The full-key/correction gate is executed for every candidate. Accepted values
are accumulated before the cursor advances, including the empty-head case. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram

open OAI BitProgram StructuredCalls CounterPrograms

/-- The terminal cursor may have one overflow bit; it is never queried. -/
structure Cursor (h i : ℕ) (d : Data) : Prop where
  rank : value (d.stacks 859) = i
  fuel : value (d.stacks 860) + i = 2 ^ h
  fuelWidth : (d.stacks 860).length = h + 1
  wordWidth : (d.stacks 859).length ≤ h + 1
  activeWidth : i < 2 ^ h → (d.stacks 859).length = h
  scratch : d.stacks 861 = []

theorem Cursor.index_lt {h i : ℕ} {d : Data} (hc : Cursor h i d)
    (hp : 0 < value (d.stacks 860)) : i < 2 ^ h := by
  have := hc.fuel
  omega

noncomputable def powerResult (d : Data) : Data :=
  embedState powerRegisters powerStacks d
    (CounterForPrograms.localData false false (d.regs 2) []
      (List.replicate (d.stacks 861).length false ++ [true]))

@[simp] theorem powerResult_fuel (d : Data) :
    (powerResult d).stacks 860 = List.replicate (d.stacks 861).length false ++ [true] :=
  embedState_stack powerRegisters powerStacks d _ (by decide) 1

@[simp] theorem powerResult_scratch (d : Data) : (powerResult d).stacks 861 = [] :=
  embedState_stack powerRegisters powerStacks d _ (by decide) 0

open HeadEvaluationProgram.StagedGate (copy copyState clear clearState )

noncomputable def seeded (d : Data) : Data :=
  clearState (powerResult (copyState (copyState d 651 859) 651 861)) 853


open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram OAI.Algorithms.SubexponentialSAT.SubexpLiftRing
open OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing TruncatedRingProgram


open OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

/-- The tested value uses every integer-signature component and local correction bit. -/
def gateValue (a : Data) (rows : List (List (List Bool))) : Bool :=
  decide (signatureValue (a.stacks 864) (a.stacks 859) rows = a.stacks 866) &&
    LeafWeightProgram.good (a.stacks 859) (a.stacks 867) (a.stacks 868)

def bodyBudget (a : Data) (rows : List (List (List Bool))) (acceptedCost : ℕ) : ℕ :=
  HeadEvaluationProgram.HeadGate.budget (a.stacks 864) (a.stacks 859) rows (a.stacks 866) +
    9 * HeadEvaluationProgram.StagedGate.sourceLength a + acceptedCost +
    8 * (a.stacks 859).length + 58

open scoped BigOperators

noncomputable def finalized (a : Data) : Data :=
  embedState FactorEnvironment.registerMap id a
    (SubexpSetupStorage.clearManyState [859, 860]
      (projectState FactorEnvironment.registerMap id a))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryAdapter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete per-high-assignment setup and compressed head overlays.
The routines read physical counter/mask words and preserve ambient coordinates. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram

def highCommand : Code := .call (ProgramLinking.liftProgram
  LeafHighContextProgram.Local.program highRegs highStacks)

def resetHighState (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none,BankRoutines.clearBankStacks highChanged a.stacks⟩

def resetHighCost (a : Data) :=
  2*(a.stacks 702).length+3+
    (2*(highChanged.map (fun i => ((StackRoutines.clearStacks 702 a.stacks) i).length)).sum+27)

def prepareHigh : Code := .seq resetHigh highCommand

namespace NativeHeadSelect
open OAI.Algorithms.SubexponentialSAT.StackRoutines

def resetState (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none,BankRoutines.clearBankStacks changed a.stacks⟩

def resetCost (a : Data) :=
  2*(a.stacks 880).length+3+
    (2*(changed.map (fun i => ((StackRoutines.clearStacks 880 a.stacks) i).length)).sum+21)

end NativeHeadSelect

open OAI.Algorithms.SubexponentialSAT.StackRoutines

def copyHighCost (a : Data) : ℕ :=
  2*(a.stacks 330).length+2*(a.stacks 792).length+7*(a.stacks 789).length+11

namespace NativeOverlay
open OAI.Algorithms.SubexponentialSAT.StackRoutines

def resetState (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none,BankRoutines.clearBankStacks changed a.stacks⟩

def resetCost (a : Data) :=
  2*(a.stacks 875).length+3+
    (2*(changed.map (fun i => ((StackRoutines.clearStacks 875 a.stacks) i).length)).sum+24)

end NativeOverlay


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSumAssembly
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete head-sum assembly. The first head gate receives a physically
cleared arithmetic bank; persistent source parameters remain outside that bank.
Accepted assignments continue through dense addition and workspace reclamation,
including empty factor products and zero-valued products. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumAssembly

open OAI BitProgram StructuredCalls StackRoutines
open HeadEvaluationProgram.StagedGate

def cleared (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none, BankRoutines.clearBankStacks workPorts a.stacks⟩

def clearWorkCost (a : Data) : ℕ :=
  2 * (a.stacks 31).length + 3 +
    (2 * (workPorts.map (fun i => (clearStacks 31 a.stacks i).length)).sum + 186)

open CommandRegisterFrames

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumAssembly
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighCountSeed
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Each marked count regenerates its own zero high-assignment odometer from
its current physical mask. No common high set or retained previous seed is
assumed. The original two-stack branch initializer is executed concretely. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountSeed

open OAI BitProgram StructuredCalls StackRoutines HighQueryAdapter
open OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram

def branch : Code := .call (ProgramLinking.liftProgram Branches.program regMap stackMap)
noncomputable def result (a : Data) (rf : Fin 2 → Bool) : Data :=
  embedState regMap stackMap (copied a) (Branches.state rf []
    (Encoding.encodeList id (List.replicate (Branches.trueCount (a.stacks 338)) [false])))
def command : Code := .seq reset (.seq copy branch)
def program := compiled command 338 330

@[simp] theorem result_counter (a : Data) (rf : Fin 2 → Bool) :
    (result a rf).stacks 330=Encoding.encodeList id
      (List.replicate (Branches.trueCount (a.stacks 338)) [false]) :=
  embedState_stack regMap stackMap (copied a) _ (by decide) 1

@[simp] theorem result_maskcopy (a : Data) (rf : Fin 2 → Bool) :
    (result a rf).stacks 792=[] := embedState_stack regMap stackMap (copied a) _ (by decide) 0

/-- Actual per-mark entry: regenerate from this mask, then initializeCmd the
fixed durable high counter and empty binary count buffers. -/
def initializeCmd : Code := .seq (.call program) (.call HighCountInit.program)
def initializeProgram := compiled initializeCmd 338 789
noncomputable def initialized (a : Data) (rf : Fin 2 → Bool) : Data := HighCountInit.result (result a rf)

@[simp] theorem initialized_guard (a : Data) (rf : Fin 2 → Bool) :
    (initialized a rf).regs 21=true := HighCountInit.guard (result a rf)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountSeed
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighMarkedCleanup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
/-! Actual lower-workspace reclamation in the shared leaf ABI. Source masters,
collector, count and upper caller words are preserved by the paid cleanup. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend
open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
def cleanupProgram := compiled cleanupCommand 699 323

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighFrontendMask
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Exact current-query mask and attained counter semantics. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open LeafParametersProgram

/-- This set is derived from the current marked scope rows, with the original
ambient dimension. Its physical mask is the one produced by the frontend. -/
def highSet (q : LeafQueryFrontend.Query) : Finset (Fin (BinaryArithmetic.toNat q.ambient)) :=
  HighIncidence.high
    (OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.suppliedScope (BinaryArithmetic.toNat q.ambient) q.scopeRows)
    ((OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.mass q.scopeRows *
      EarlyThreshold.threshold (BinaryArithmetic.toNat q.ambient)) ⌈/⌉ BinaryArithmetic.toNat q.ambient)

theorem physical_high_mask (q : LeafQueryFrontend.Query) :
    LeafQueryFrontend.highMask q.scopeRows (BinaryArithmetic.toNat q.ambient)=
      OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighIncidenceProgram.descendingHighMask (highSet q) := by
  exact OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Order.physical_mask _ _ _

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryExecution
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete outer count execution. The final canonicalization and marked
return consume the entire accumulated binary count. Their compact boundary is
proved separately from the transient workspace used by the query. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryExecution

open OAI BitProgram StructuredCalls HighQueryAdapter DisjointReuse
open HashGreedyProgram.NativeRound

noncomputable def canonicalized (a : Data) : Data :=
  CanonicalHigh.result (CanonicalHigh.resetState a)

@[simp] theorem canonicalized_count (a : Data) :
    (canonicalized a).stacks 788 = countWord (BinaryArithmetic.toNat (a.stacks 788)) :=
  CanonicalHigh.final_count a

@[simp] theorem canonicalized_scratch (a : Data) :
    (canonicalized a).stacks 793 = [] ∧ (canonicalized a).stacks 794 = [] := by
  constructor
  · exact embedState_stack CanonicalHigh.regMap CanonicalHigh.stackMap
      (CanonicalHigh.resetState a) _ (by decide) 1
  · exact embedState_stack CanonicalHigh.regMap CanonicalHigh.stackMap
      (CanonicalHigh.resetState a) _ (by decide) 2

/-- The whole-count readback does not use the count head as a SAT bit. -/
def markedReturn : Code := .seq canonicalize HashMarkedReturn.command
noncomputable def returned (a : Data) : Data := HashMarkedReturn.result (canonicalized a)

open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram OAI.Algorithms.SubexponentialSAT.StackRoutines

noncomputable def installedAccepted (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none,Function.update (Function.update a.stacks 788 (a.stacks 323)) 323 []⟩
def acceptedReturn : Code := .seq markedReturn installAccepted
noncomputable def accepted (a : Data) : Data := installedAccepted (returned a)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryExecution
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeQueryPreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete query packing and arithmetic preparation. Numeric and physical
input caps are kept separate from the subsequent exponential node traversal.
Every arithmetic object is returned by its actual native producer. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation

open OAI BitProgram StructuredCalls SqrtLog LeafParametersProgram
open LeafProgram.Query CostAssembly.Polynomial

/-- Erasing only the three syntactically untouched carried words is a proof
construction; the actual preparation still runs with those words present. -/
def shadow (a : Data) : Data :=
  ProgramTapeReplay.rebaseState LeafProgram.OuterCarried.hidden (fun _ => []) a

theorem shadow_visible (a : Data) (i : Fin 768)
    (hi : i.val < 320 ∨ 332 < i.val) : (shadow a).stacks i = a.stacks i := by
  apply ProgramTapeReplay.rebaseStacks_of_not_mem
  intro h
  simp only [LeafProgram.OuterCarried.hidden, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> norm_num [Fin.coe_ofNat_eq_mod] at hi

theorem shadow_bank (a : Data) :
    projectState Exports.bankRegs Exports.bank (shadow a) =
      projectState Exports.bankRegs Exports.bank a := by
  apply CommandStackTransport.projectState_rebase
  intro i h
  have hi : 340 ≤ (Exports.bank i).val := by simp [Exports.bank]
  simp only [LeafProgram.OuterCarried.hidden, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h <;> have hv := congrArg Fin.val h <;>
    norm_num [Fin.coe_ofNat_eq_mod] at hv <;> omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeLayoutLoad
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Paid node-start loading of the parked source bank. Only the original
layout copy program is called; no head enumeration is imported or executed. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLayoutLoad

open OAI BitProgram StructuredCalls SubexpSetupStorage SqrtLog
open LeafProgram LeafHeadSetupProgram

abbrev Data := State 40 896

noncomputable def prepared (a : Data) : Data :=
  embedState registers id a
    (clearManyState clearPorts (projectState registers id a))

def prepareCost (a : Data) : ℕ :=
  clearManyCost clearPorts (projectState registers id a)+1

noncomputable def source (a : Data) : State 40 768 :=
  projectState id stackMap (prepared a)

noncomputable def loaded (a : Data) : State 40 768 :=
  embedState LayoutMasters.registers id (source a)
    (LayoutMasters.loaded (LayoutMasters.project (source a)))

noncomputable def result (a : Data) : Data :=
  embedState id stackMap (prepared a) (loaded a)

noncomputable def cost (a : Data) : ℕ :=
  prepareCost a+LayoutMasters.loadCost (LayoutMasters.project (source a))+2

theorem prepared_stack (a : Data) (i : Fin 896) :
    (prepared a).stacks i = if i ∈ clearPorts then [] else a.stacks i := by
  calc
    _ = (clearManyState clearPorts (projectState registers id a)).stacks i :=
      embedState_stack registers id a _ Function.injective_id i
    _ = _ := clearMany_stacks clearPorts (projectState registers id a) i

theorem loaded_stack (a : Data) (i : Fin 768) :
    (loaded a).stacks i =
      (LayoutMasters.loaded (LayoutMasters.project (source a))).stacks i := by
  exact embedState_stack _ _ _ _ Function.injective_id i

theorem result_stack (a : Data) (i : Fin 768) :
    (result a).stacks (stackMap i) = (loaded a).stacks i :=
  embedState_stack _ _ _ _ (Fin.castAdd_injective _ _) i

theorem result_low (a : Data) (i : Fin 14) :
    (result a).stacks (stackMap (LayoutMasters.low i)) =
      a.stacks (stackMap (LayoutMasters.high i)) := by
  rw [result_stack,loaded_stack,LayoutMasters.loaded_low]
  · exact (prepared_stack a _).trans (ite_eq_right (not_mem_high_clear i))
  · intro j
    exact (prepared_stack a _).trans (ite_eq_left (mem_low_clear j))

theorem result_frame (a : Data) (i : Fin 896) (hi : i ∉ clearPorts) :
    (result a).stacks i = a.stacks i := by
  by_cases hlt : i.val<768
  · let j : Fin 768 := ⟨i.val,hlt⟩
    have hj : stackMap j=i := Fin.ext rfl
    have hn : j ∉ LayoutMasters.lowPorts := by
      intro h
      exact hi (List.mem_append_right _ (List.mem_map.mpr ⟨j,h,hj⟩))
    rw [←hj,result_stack,loaded_stack,LayoutMasters.loaded_frame _ _ hn]
    exact (prepared_stack a _).trans (ite_eq_right (by simpa only [hj] using hi))
  · rw [result,embedState_stack_frame]
    · exact (prepared_stack a i).trans (ite_eq_right hi)
    · rintro ⟨j,hj⟩
      have hv := congrArg Fin.val hj
      change j.val=i.val at hv
      omega

theorem result_empty (a : Data) (i : Fin 768)
    (hi : i ∈ ([684,660,665] : List (Fin 768))) :
    (result a).stacks (stackMap i)=[] := by
  have hn : i ∉ LayoutMasters.lowPorts := by
    intro h
    obtain ⟨j,_,hj⟩ := List.mem_map.mp h
    have hv := congrArg Fin.val hj
    change 128+j.val=i.val at hv
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
    rcases hi with rfl|rfl|rfl <;> omega
  rw [result_stack,loaded_stack,LayoutMasters.loaded_frame _ _ hn]
  apply (prepared_stack a _).trans
  apply ite_eq_left
  apply List.mem_append_left
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
  rcases hi with rfl|rfl|rfl <;> decide

/-- All fields name actual parked words or the retained live node counter. -/
structure SourceBank (s : Native.Inputs) (a : Data) : Prop where
  ambient : a.stacks 730=unary s.n
  factors : a.stacks 731=unary s.N
  colors : a.stacks 732=unary s.r
  nodes : a.stacks 733=unary s.Q
  wordWidth : a.stacks 734=unary (s.Q*s.r)
  words : a.stacks 735=s.rows.flatten
  low : a.stacks 736=s.low
  metadata : a.stacks 737=s.metadata
  plans : a.stacks 738=LayoutOwnerFiberProgram.stream s.plans
  order : a.stacks 740=unary s.R
  height : a.stacks 741=s.height
  width : a.stacks 742=s.width
  offset : BinaryArithmetic.toNat (a.stacks 743)=s.offset
  node : a.stacks 307=unary s.node.val

theorem result_ready (s : Native.Inputs) (a : Data) (h : SourceBank s a) :
    Native.Ready s (projectState registers stackMap (result a)) := by
  constructor
  · exact (result_low a 0).trans h.ambient
  · exact (result_low a 1).trans h.factors
  · exact (result_low a 2).trans h.colors
  · exact (result_low a 3).trans h.nodes
  · exact (result_low a 4).trans h.wordWidth
  · exact (result_low a 5).trans h.words
  · exact (result_low a 6).trans h.low
  · exact (result_low a 7).trans h.metadata
  · exact (result_low a 8).trans h.plans
  · exact (result_low a 10).trans h.order
  · exact (result_low a 11).trans h.height
  · exact (result_low a 12).trans h.width
  · exact (congrArg BinaryArithmetic.toNat (result_low a 13)).trans h.offset
  · exact (result_frame a 307 (by decide)).trans h.node
  · exact result_empty a 660 (by decide)
  · exact result_empty a 665 (by decide)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLayoutLoad
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NodeReadoutSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual node-array readout after all finite-difference pairs. The fixed
cleanup pays for transient lower words and clears the old output. Preserved
masters supply the coefficient zero vector and both truncation bounds. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeReadoutSpace

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open MomentsProgram TruncatedRingProgram

def cleared (i : Fin 896) (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none, Function.update a.stacks i []⟩

def clearedMany : List (Fin 896) → Data → Data
  | [], a => a
  | i :: is, a => clearedMany is (cleared i a)

def clearCost : List (Fin 896) → Data → ℕ
  | [], _ => 0
  | i :: is, a => 2 * (a.stacks i).length + 3 + clearCost is (cleared i a)

theorem clearedMany_stack (ps : List (Fin 896)) (a : Data) (i : Fin 896) :
    (clearedMany ps a).stacks i = if i ∈ ps then [] else a.stacks i := by
  induction ps generalizing a with
  | nil => simp [clearedMany]
  | cons p ps ih =>
      rw [clearedMany, ih]
      by_cases hp : i = p <;> by_cases hs : i ∈ ps <;> simp [cleared, hp, hs]

/-- Only actual retained words are hypotheses; scratch is physically cleared. -/
structure Ready (a : Data) (modulus width degree dictionary zero marker taylor shape : List Bool) : Prop where
  modulus : a.stacks 5 = modulus
  width : a.stacks 12 = width
  degree : a.stacks 39 = degree
  dictionary : a.stacks 850 = dictionary
  zero : a.stacks 280 = zero
  marker : a.stacks 212 = marker
  taylor : a.stacks 243 = taylor
  shape : a.stacks 128 = shape

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeReadoutSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NodeAppendSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeAppendSpace
open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open MomentsProgram TruncatedRingProgram

def transferred (src dst : Fin 896) (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none, StackRoutines.transferStacks src dst a.stacks⟩

def appendResult (a : Data) : Data :=
  transferred 89 863 (transferred 862 89 (transferred 863 89 a))

def appendCost (a : Data) : ℕ := 6 * ((a.stacks 863).length + (a.stacks 862).length) + 9

def copied (src dst : Fin 896) (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none, StackRoutines.copyStacks src dst a.stacks⟩

def prepared (a : Data) : Data := copied 204 39 (copied 202 12
  (copied 194 5 (NodeReadoutSpace.clearedMany [89,5,12,39] a)))

def prepareCost (a : Data) : ℕ := NodeReadoutSpace.clearCost [89,5,12,39] a +
  7 * (a.stacks 194).length + 5 + 7 * (a.stacks 202).length + 5 +
  7 * (a.stacks 204).length + 5

structure MasterReady (a : Data) (modulus width degree dictionary zero marker taylor shape : List Bool) : Prop where
  modulus : a.stacks 194 = modulus
  width : a.stacks 202 = width
  degree : a.stacks 204 = degree
  dictionary : a.stacks 850 = dictionary
  zero : a.stacks 280 = zero
  marker : a.stacks 212 = marker
  taylor : a.stacks 243 = taylor
  shape : a.stacks 128 = shape

def handoffResult (a : Data) : Data :=
  transferred 89 265 (transferred 863 89 (NodeReadoutSpace.cleared 265 a))

def handoffCost (a : Data) : ℕ :=
  2 * (a.stacks 265).length + 6 * (a.stacks 863).length + 9

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeAppendSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryNodeFinish
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual node readout and loop continuation. The emitted coefficient stream
retains its order. Node temporaries are physically reclaimed before refreshing
the outer guard, and every completed node restores one fixed boundary bound. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeFinish

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open MomentsProgram TruncatedRingProgram

def guarded (a : Data) : Data :=
  ⟨readRegs a.regs 37 38 (a.stacks 301).head?,a.stacks⟩

def advanced (a : Data) : Data :=
  ⟨Function.update a.regs 0 true,Function.update a.stacks 307 (true::a.stacks 307)⟩

def finished (a : Data) : Data :=
  guarded (advanced (NodeReadoutSpace.clearedMany [78,850] a))

def finishNodeCost (a : Data) : ℕ := 2*((a.stacks 78).length+(a.stacks 850).length)+9

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeFinish
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete bit primitives for streamed finite-difference queries. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram

open OAI BitProgram
open scoped BigOperators

open StructuredCalls

def afterScan {s : ℕ} (d : State 3 s) (src : Fin s) : State 3 s :=
  ⟨![false, false, parity (d.stacks src) (d.regs 2)], Function.update d.stacks src []⟩

def pairStart (regs : Fin 3 → Bool) (E U : List Bool) : State 3 4 :=
  ⟨regs, ![E, U, [], []]⟩

def pairFinish (E U : List Bool) : State 3 4 :=
  ⟨![false, false, parity U (parity E false)],
    ![E, U, [parity U (parity E false)], []]⟩

section SignedArray

attribute [local simp] Fin.coe_ofNat_eq_mod

open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open MomentsProgram TruncatedRingProgram

def signedEntries (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (minusOne : RingProgram.Code (Word (baseWidth p t)) d) (sign : Bool)
    (a : List (Product.Entry n (baseWidth p t) d)) :=
  if sign then Squarefree.ScaleProgram.scaled p t M cache table minusOne a else a

/-- The normalized result is an exact signed addition in the retained array. -/
def signedSum (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (minusOne : RingProgram.Code (Word (baseWidth p t)) d) (sign : Bool)
    (source seed : List (Product.Entry n (baseWidth p t) d)) :=
  Normalize.run p t M cache (signedEntries p t M cache table minusOne sign source) seed

end SignedArray

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryTupleSum
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete unsigned tuple accumulation. The complete head product on852
is normalized into the pair accumulator851. Physical caches are copied from
retained masters and every native peripheral scratch word is paid for. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleSum

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open MomentsProgram TruncatedRingProgram

def prepared (a : Data) : Data :=
  NodeReadoutSpace.clearedMany scratchPorts (NodeAppendSpace.prepared a)

def prepareCost (a : Data) : ℕ := NodeAppendSpace.prepareCost a +
  NodeReadoutSpace.clearCost scratchPorts (NodeAppendSpace.prepared a)

structure Ready (a : Data) (modulus width degree seed source : List Bool) : Prop where
  modulus : a.stacks 194 = modulus
  width : a.stacks 202 = width
  degree : a.stacks 204 = degree
  seed : a.stacks 851 = seed
  source : a.stacks 852 = source

noncomputable def result (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree output : List Bool) : Data :=
  embedState registers ports (prepared a) (Normalize.state rr modulus width degree output [])

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleSum
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureHeadLoaderCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The fixed head-loader table uses the actual integer entry program. Its
physical matrix view follows LeafHeadSetupProgramHead/MatrixRun exactly, while
its controller emits one matrix and never constructs assignment tables. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

/-- State of the paid one-head loader, before its high-bank export. -/
def localResult (a : Data) (rp : Fin 8 → Bool) (rm : Fin 16 → Bool)
    (rs : Fin 8 → Bool) (n N W z : ℕ) (rows : List (List Bool)) (low : List Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool))) : Data :=
  let preparedHeadState := preparedHead a rp n N rows low W z
  let rawState := returned id (by decide) matrixInputs rawOutputs preparedHeadState
    (LayoutMatrixProgram.finalState (matrixBase preparedHeadState) rm raw)
  clearState 669 (returned shiftRegs (by decide) shiftInputs shiftOutputs rawState
    (BucketProgram.preMatrixState rs (rawState.stacks 141) []
      (Subexp.MatrixProgramSupport.words (shifted.map Subexp.MatrixProgramSupport.words))))

/-- The budget includes every stage and the final raw-word clear. -/
def localBudget (a : Data) (rp : Fin 8 → Bool) (rm : Fin 16 → Bool)
    (rs : Fin 8 → Bool) (n N W z : ℕ) (rows : List (List Bool)) (low : List Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (T B D : ℕ) : ℕ :=
  let p := preparedHead a rp n N rows low W z
  let mlocal := LayoutMatrixProgram.finalState (matrixBase p) rm raw
  let m := returned id (by decide) matrixInputs rawOutputs p mlocal
  let slocal := BucketProgram.preMatrixState rs (m.stacks 141) []
    (Subexp.MatrixProgramSupport.words (shifted.map Subexp.MatrixProgramSupport.words))
  let e := returned shiftRegs (by decide) shiftInputs shiftOutputs m slocal
  prepareHeadCost a rp n N rows low W z+
    (stageCost id (by decide) matrixInputs rawOutputs p mlocal
      (LayoutMatrixProgram.commandCost T B D n (selectedHeads n rows low z)+1)+
    (stageCost shiftRegs (by decide) shiftInputs shiftOutputs m slocal
      (BucketProgram.preMatrixCost (m.stacks 141) raw+1)+(2*(e.stacks 669).length+3)))

def exportedState (a : State 16 896) : State 16 896 :=
  clearManyState [668,669,846] (copyState 668 847 (clearState 659 a))

def exportCost (a : State 16 896) : ℕ :=
  2*(a.stacks 659).length+3+(7*(a.stacks 668).length+5+
    clearManyCost [668,669,846] (copyState 668 847 (clearState 659 a)))

def addressStateFrom (src : Fin 896) (a : State 16 896) : State 16 896 :=
  copyState src 649 (clearManyState [649,659,846,847] a)

def lowResultFrom (src : Fin 896) (a : State 16 896) (b : Data) : State 16 896 :=
  embedState id lowStacks (addressStateFrom src a) b

/-- The actual lower input reached after the paid address copy. -/
def leafInputFrom (src : Fin 896) (frame : State 40 896) : Data :=
  projectState id lowStacks (addressStateFrom src (projectState leafRegs id frame))

def leafOutputFrom (src : Fin 896) (frame : State 40 896) (b : Data) : State 40 896 :=
  embedState leafRegs id frame
    (exportedState (lowResultFrom src (projectState leafRegs id frame) b))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed finite syntax for both marked and final accepted queries. The only
program parameter is the fixed clause width. Every mark regenerates its own
physical high mask and zero counter. The semantic proof must establish that
the actual frontend guard holds on every reachable input. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram

open OAI BitProgram StructuredCalls HighQueryAdapter
noncomputable section

/-- This initializer reads the current338 mask, including when it is empty.
The singleton zero tuple is still visited once in that case. -/
def seed : Code := .call HighCountSeed.initializeProgram

open HashGreedyProgram.NativeRound

namespace Carried

open SqrtLog.ProgramTapeReplay

local notation "H" => (fun i : Fin 896 => i ∈ words)

structure LowerSafeAvoids (c : Cmd 40 768) : Prop where
  proof : AvoidsCmd (H ∘ HighMarkedFrontend.stackMap) c

attribute [local irreducible] HashMarkedReturn.upperClear

end Carried

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryStart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual entry to each high-assignment count. The current frontend mask
survives concrete packing/arithmetic and drives the fixed zero-seed program.
The compact returned boundary is separate from the transient prefix bound. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryStart

open OAI BitProgram StructuredCalls SqrtLog LeafParametersProgram
open LeafProgram.Query HashGreedyProgram.NativeRound

def command : Cmd 40 896 := .call HighCountSeed.initializeProgram

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryStart
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQuerySetup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete preparation and fresh high-counter initialization for the fixed
marked and accepted queries. The witness below is produced by the actual
programs; no implementation or evaluator is supplied as a hypothesis. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup

open OAI BitProgram StructuredCalls SqrtLog LeafParametersProgram
open LeafProgram.Query HashGreedyProgram.NativeRound
open HighMarkedFrontend

def boundaryBound (q : LeafQueryFrontend.Query) (S cost B : ℕ) : ℕ :=
  max (4 * BinaryArithmetic.toNat q.ambient + 1) (max (localBound S cost) B)

def prefixBound (q : LeafQueryFrontend.Query) (S cost B : ℕ) : ℕ :=
  max (12 * localBound S cost + 5) (boundaryBound q S cost B)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeLeafStartup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual loaded-leaf startup and canonical saved selector parameters. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup

open BitProgram StructuredCalls SqrtLog SqrtLog.LeafOuterProgram

/-- The fixed startup program scans the loaded clauses and then saves the
actual arithmetic results. It does not assume prepared selector metadata. -/
def canonicalStart : Cmd 40 896 := .seq start saveCanonical

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeLeafRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete leaf control: prepared code history, all physically staged greedy
rounds, and a separate history-only exact count. The query execution proofs
remain explicit development seams until the native query bodies instantiate them. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram
open HashGreedyProgram HashGreedyProgram.NativeRound HashGreedyRound
open HashMassAdapter HashGreedyExecution

def roundsTime (base : State 40 896) (n m depth : ℕ)
    (queryCost : List Bool → ℕ) (L : ℕ) : ℕ :=
  HashSelectProgram.roundsBudget
    (NativeRound.roundBudget
      (stagedAttemptBudget base n m depth queryCost L)
      (HashSelect.loopCap n m) (HashCandidates.payloadWidth m depth))
    (HashSelect.loopCap n m)

def roundsSpace (base : State 40 896) (n m depth L K : ℕ) : ℕ :=
  max (HashGreedyStagedSpace.attemptSpace base n m depth L K)
    (896 * L + 100 * (HashSelect.loopCap n m +
      HashCandidates.payloadWidth m depth + 1) +
      7 * (2 * HashCandidates.payloadWidth m depth + 3) + 20)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryRepresentativeFold
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryRepresentativeFold
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open LeafAssignmentMergeProgram

/-- Mathematical fold matching the visitor's decreasing physical head address. -/
def run (mask : ℕ → List Bool) (base : ℕ) : List (List Bool) → List Bool → List Bool
  | [], baseline => baseline
  | word :: rest, baseline => run mask base rest
      (merge (HighIncidenceProgram.Restriction.zeroMerge (mask (base + rest.length)) word)
        (mask (base + rest.length)) baseline)

@[simp] theorem run_nil (mask : ℕ → List Bool) (base : ℕ) (baseline : List Bool) :
    run mask base [] baseline = baseline := rfl

@[simp] theorem run_cons (mask : ℕ → List Bool) (base : ℕ)
    (word : List Bool) (rest : List (List Bool)) (baseline : List Bool) :
    run mask base (word :: rest) baseline = run mask base rest
      (merge (HighIncidenceProgram.Restriction.zeroMerge (mask (base + rest.length)) word)
        (mask (base + rest.length)) baseline) := rfl

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryRepresentativeFold
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_RingNodeMetadata
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual ring producer determines both the factor cutoff and the native
arithmetic cutoff. Its framed node stream uses the same increasing indices as
the physical cursor and the interpolation nodes. -/

noncomputable section

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.RingNodeMetadata

open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open OAI.Algorithms.SubexponentialSAT.SqrtLog LeafParametersProgram LeafProgram.PreparedSource

/-- The physical producer's node words are indexed in interpolation order. -/
def nodeBits (t d Q : ℕ) : List (List Bool) :=
  (LeafRingSetupProgram.nodeWords t d Q).map RingProgram.flat

@[simp] theorem nodeBits_length (t d Q : ℕ) : (nodeBits t d Q).length = Q := by
  simp [nodeBits]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.RingNodeMetadata
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleLoader
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete head reloads for the attained-signature DFS.  The matrix comes
from the fixed native integer-entry machine, and each reload restores one
fixed retained-word bound before the next candidate scan. -/

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open SignatureTupleProgram SignatureTupleNative SignatureTupleRefinement
open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

/-- The physical result of that one concrete head loader. -/
def result (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool))) :
    State 40 896 :=
  SignatureHeadLoader.leafOutputFrom headAddress frame
    (SignatureHeadLoader.localResult (SignatureHeadLoader.leafInputFrom headAddress frame)
      rp rm rs s.n s.N (s.Q*s.r) z s.rows s.low raw shifted)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader
end
end


