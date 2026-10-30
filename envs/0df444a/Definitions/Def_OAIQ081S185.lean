-- Prove2me | Definitions.Def_OAIQ081S185
-- name    : OAIQ081S185
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T23:37:17.502927+00:00
-- url     : https://prove2.me/theorems/41e7df70-dabd-4df2-a489-a67455cd0fb9
-- title:
--   Definitions bundle OAIQ081S185 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 60 declarations of OpenAI's Lean: 28 definitions, 11 inductive types or structures and 21 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.literalCount`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEmittedSourceTarget.enumerate`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEmittedSourceTarget.selectedEquiv`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEmittedSourceTarget.selectedIds`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadSourceFacts.addressedSource`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.bootstrapped`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.loadedNode`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.nodeSource`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.sourceSnapshot`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation.Invariant`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation.callbackSpace`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReadyConstruction.CommonReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState.QueryReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor.installedRepresentative`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor.overlaidRepresentative`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor.restartCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.SourceFacts`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.representativeWord`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.mask`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadPrepare.mastersState`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadPrepare.result`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.Boundary`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.HaltBoundary`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.LeafBoundary`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.Rel`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.RetainedCap`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.ScanBoundary`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.ScanMatrix`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.emittedRepresentatives`, `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowEmitCall.result`, `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowFactorLoop.effect`, `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowFactorLoop.output`, `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowFactorLoop.prependFactor`, `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowFactorLoop.updated`, `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowProgram.factorCost`, `OAI.Algorithms.SubexponentialSAT.SubexpKernelControl.afterCounter`, `OAI.Algorithms.SubexponentialSAT.SubexpKernelControl.afterTag`, `OAI.Algorithms.SubexponentialSAT.SubexpKernelControl.bump`, `OAI.Algorithms.SubexponentialSAT.SubexpKernelControl.emptyAccumulator`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_NativeHashQueries`, `SubexponentialSAT_SqrtLogSpace_QueryEmittedSourceTarget`, `SubexponentialSAT_SqrtLogSpace_QueryHeadSourceFacts`, `SubexponentialSAT_SqrtLogSpace_QueryModelBudgets`, `SubexponentialSAT_SqrtLogSpace_QueryNodeEvaluation`, `SubexponentialSAT_SqrtLogSpace_QueryPairEvaluation`, `SubexponentialSAT_SqrtLogSpace_QueryReadyConstruction`, `SubexponentialSAT_SqrtLogSpace_QuerySourceSnapshot`, `SubexponentialSAT_SqrtLogSpace_QueryTupleState`, `SubexponentialSAT_SqrtLogSpace_QueryTupleVisitor`, `SubexponentialSAT_SqrtLogSpace_QueryVisitorHead`, `SubexponentialSAT_SqrtLogSpace_QueryVisitorSemantics`, `SubexponentialSAT_SqrtLogSpace_SignatureHeadPrepare`, `SubexponentialSAT_SqrtLogSpace_SignatureTupleComplete`, `SubexponentialSAT_SqrtLogSpace_SignatureTupleRun`, `SubexponentialSAT_SqrtLogSpace_SignatureTupleSourceAlignment`, `SubexponentialSAT_SqrtLog_PackingCallerProgramSuffix`, `SubexponentialSAT_SqrtLog_PackingLoaderProgram`, `SubexponentialSAT_SubexpKernelControl`, `SubexponentialSAT_Subexp_UniversalRowEmitCall`, `SubexponentialSAT_Subexp_UniversalRowFactorLoop`, `SubexponentialSAT_Subexp_UniversalRowProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S173`, `OAIQ081S174`, `OAIQ081S175`, `OAIQ081S177`, `OAIQ081S178` and `OAIQ081S179` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S186`, `OAIQ081S187` and `OAIQ081S188`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBoundary.entry_of_query`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.literal_accepted_count`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.literal_trial_count`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.bootstrap_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.prepare_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.prepare_native_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.prepared_words`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeReadout.run_common`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeSourceBounds.retainedCap`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation.commit_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState.finish`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState.initialize_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram.install_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram.multiply_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram.prepare_run` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.representativeWord_selected`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBoundary.entry_of_query`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.literal_accepted_count`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.literal_trial_count`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution.replay_resources`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.bootstrap_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.prepare_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.prepare_native_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.prepared_words`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeReadout.run_common`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeSourceBounds.retainedCap`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation.commit_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState.finish`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState.initialize_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram.install_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram.multiply_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram.prepare_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.representativeWord_selected` and `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowFactorLoop.loop_indices_eval`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S173
import Definitions.Def_OAIQ081S174
import Definitions.Def_OAIQ081S175
import Definitions.Def_OAIQ081S177
import Definitions.Def_OAIQ081S178
import Definitions.Def_OAIQ081S179

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

def afterCounter (i : Fin 3) (word src zero one : Word) (a : Accumulator) : State 3 8 :=
  state (word.head?.getD false) word.head?.isSome src zero one (setCounter i word.tail a)

/-! The following induction rule accounts for actual executions of the fixed
payload body. Its premises will be proved for `termBody`, `groupBody`, and
`blockBody`; the exported whole-controller statement has no callback argument. -/

def afterTag {α : Type*} (encode : α → Word) (xs : List α) (rest zero one : Word)
    (a : Accumulator) : State 3 8 :=
  match xs with
  | [] => state false true rest zero one a
  | x :: xs => state true true
      (Encoding.frame (encode x) ++ (Encoding.encodeList encode xs ++ rest)) zero one a

def bump (i : Fin 3) (a : Accumulator) : Accumulator :=
  setCounter i (true :: counterWord i a) a

/-! ## Forward-output service boundary -/

def emptyAccumulator : Accumulator := ⟨[], [], [], []⟩

end SubexponentialSAT.SubexpKernelControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical source construction for universal interpolation rows

The input holds raw coefficient payloads, node inverses, and negative nodes.
It does not contain polynomial instructions. Fixed nested scans emit the
Lagrange products and correction sum as postfix source in canonical list order.
The surrounding row-data producer supplies the selected mismatch positions;
its matrix, cache, and type-mask construction is tracked separately.
-/

namespace SubexponentialSAT.Subexp.UniversalRowProgram

open BitProgram StructuredCalls
open SubexpKernelControl (Word Accumulator pushWord operator operators emit bump
  state counterWord setCounter counterPort popTag unframe emitFramedLiteral emitLiteral
  emitOperator countOne drain scan )

def factorCost (x : Word) (f : Factor Word) : ℕ :=
  7 * f.inverseDifference.length + 7 * f.negativeNode.length + 8 * x.length + 29

end SubexponentialSAT.Subexp.UniversalRowProgram

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

def prependFactor (differences negatives : List Word) (j : ℕ) (out : Word) : Word :=
  true :: (Encoding.frame (UniversalRowProgram.encodeFactor (factor differences negatives j)) ++ out)

def updated (differences negatives : List Word) (outer index out : Word) : Word :=
  if index = outer then out else prependFactor differences negatives index.length out

def effect (differences negatives : List Word) (outer bits : Word) (a b : Data) : Prop :=
  b.stacks 21 = updated differences negatives outer bits.reverse (a.stacks 21)

def output (differences negatives : List Word) (outer : Word)
    (records : List Word) (acc : Word) : Word :=
  records.foldl (fun out bits => updated differences negatives outer bits.reverse out) acc

end SubexponentialSAT.Subexp.UniversalRowFactorLoop

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowEmitCall
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A framed call to the actual row source emitter inside the row workspace. -/

namespace SubexponentialSAT.Subexp.UniversalRowEmitCall

open BitProgram StructuredCalls
open UniversalRowProgram (Row)
open SubexpKernelControl (Word)

def result (a : Data) (output : Word) : Data :=
  ⟨(resetState a).regs, Function.update a.stacks 31 output⟩

end SubexponentialSAT.Subexp.UniversalRowEmitCall

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingLoaderProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One fixed native loader from the incidence installer's actual tapes and
binary metadata to the sequential packing selector's initialized tapes. -/
namespace SubexponentialSAT.SqrtLog.PackingLoaderProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-- No prepared alphabet, seed indices, or assignment is supplied. They are
all generated by the fixed loader, whose endpoint preserves a scope master. -/
theorem command_eval (outside : Store) (regs : Fin 16 → Bool)
    (scopes : List Bool) (n k f : ℕ) (pairs : List Bool)
    (h60 : outside 60=[]) (hr : 0 < SubexponentialSAT.BinaryArithmetic.toNat (outside 59)) :
    ∃ t rf, t+1 ≤ budget outside scopes n k f pairs ∧ Eval command t
      (rawInput outside regs scopes n k f pairs)
      (framed (Function.update outside 60 scopes)
        (readyLocal rf (SubexponentialSAT.BinaryArithmetic.toNat (outside 59))
          (SubexponentialSAT.BinaryArithmetic.toNat (outside 55)) n f pairs
          (outside 56) (outside 57) (outside 58) (outside 59))) := by
  let saved := Function.update outside 60 scopes
  obtain ⟨r0,h0⟩ := capture_eval outside regs scopes n k f pairs h60
  obtain ⟨t1,r1,ht1,h1⟩ := parameters_eval saved r0 n f pairs
  obtain ⟨t2,ht2,h2⟩ := core_eval saved r1
    (SubexponentialSAT.BinaryArithmetic.toNat (outside 59))
    (SubexponentialSAT.BinaryArithmetic.toNat (outside 55)) n f pairs hr
  obtain ⟨rf,h3⟩ := finish_eval saved (SubexponentialSAT.BinaryArithmetic.toNat (outside 59))
    (SubexponentialSAT.BinaryArithmetic.toNat (outside 55)) n f pairs
  have hparams : parameterBudget saved=parameterBudget outside := by simp [saved,parameterBudget]
  have hfinish : finishBudget saved=finishBudget outside := by simp [saved,finishBudget]
  simp only [saved,Function.update_of_ne (by decide : (59 : Fin 64)≠60),
    Function.update_of_ne (by decide : (55 : Fin 64)≠60)] at h1
  have hall := h0.seq (h1.seq (h2.seq h3))
  refine ⟨captureBudget scopes.length n k f+(t1+(t2+finishBudget saved)),rf,?_,?_⟩
  · rw [hparams] at ht1
    rw [hfinish]
    unfold budget
    omega
  · simpa only [command,saved,Function.update_of_ne (by decide : (56 : Fin 64)≠60),
      Function.update_of_ne (by decide : (57 : Fin 64)≠60),
      Function.update_of_ne (by decide : (58 : Fin 64)≠60),
      Function.update_of_ne (by decide : (59 : Fin 64)≠60)] using hall

end SubexponentialSAT.SqrtLog.PackingLoaderProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramSuffix
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Full native layout suffix followed by a paid metadata save and cleanup. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
open PackingLoaderProgram

theorem suffix_eval {U : Type*} [DecidableEq U] (outside : Store)
    (regs : Fin 16 → Bool) (s : LayoutProgram.NativePacking.Spec U)
    (hdelta : s.params.Δ=1) (h52 : outside 52=[]) (h63 : outside 63=[])
    (hD : SubexponentialSAT.BinaryArithmetic.toNat (outside 58)=s.params.D)
    (hwidth : outside 53=s.params.width)
    (halphabet : outside 54=ProgramEncoding.encodeRecords s.params.alphabet)
    (hplans : outside 61=s.params.planStream) (hwords : outside 62=s.params.rows.flatten) :
    ∃ t rf, t ≤ suffixBudget outside s ∧ Eval suffix t
      (framed outside (⟨regs,fun _=>[]⟩ : Small))
      (framed (Function.update outside 63 s.suffix.metadata) (⟨rf,fun _=>[]⟩ : Small)) := by
  obtain ⟨tp,rp,htp,hp⟩ := prepareSuffix_eval outside regs s.params hdelta h52 hD
    hwidth halphabet hplans hwords
  obtain ⟨tn,htn,rn,hn⟩ := LayoutProgram.NativePacking.program_trace s rp
  have hnative := framed_call LayoutProgram.NativePacking.program outside hn
  obtain ⟨rs,hs⟩ := saveHigh_eval outside (s.suffix.outputState rn) 32 63
    (by decide) (by decide) h52 h63
  have hmeta : (s.suffix.outputState rn).stacks 32=s.suffix.metadata := by
    simp [LayoutProgram.PackLabels.Spec.outputState,PackingProgram.outputState]
  rw [hmeta] at hs
  obtain ⟨rf,hclear⟩ := clearLow_run (Function.update outside 63 s.suffix.metadata)
    (setRegs (s.suffix.outputState rn) rs)
  have hclearCost : clearLowBudget (setRegs (s.suffix.outputState rn) rs)=
      clearLowBudget (s.suffix.outputState (fun _=>false)) := rfl
  rw [hclearCost] at hclear
  exact ⟨tp+(tn+((7*s.suffix.metadata.length+5)+
      clearLowBudget (s.suffix.outputState (fun _=>false)))),rf,
    by dsimp [suffixBudget]; omega,hp.seq (hnative.seq (hs.seq hclear))⟩

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryModelBudgets
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryModelBudgets
open SqrtLog SqrtLog.LeafParametersProgram Circuit

/-- Every literal packing scalar is read from the actual guarded bank.
This statement is independent of a supplied packing problem or layout. -/
theorem produced_layout_scalars_le (x : Input) (padding : Fin 8 → ℕ) (S : ℕ)
    (hv : ∀ j, (Execute.guardedModel x padding).val j ≤ S) :
    x.ambient ≤ S ∧ x.factors ≤ S ∧ x.incidences ≤ S ∧
      (produce x).r ≤ S ∧ (produce x).Q ≤ S ∧ (produce x).epsilonDen ≤ S ∧
      (produce x).r ^ (produce x).Q ≤ S ∧
      (produce x).r ^ (2 * (produce x).Q) ≤ S ∧ (produce x).R ≤ S := by
  have hn := hv 0
  have hf := hv 5
  have hi := hv 7
  have he0 : (Execute.guardedModel x padding).val 0 = x.ambient :=
    Execute.guardedModel_input x padding 0
  have he5 : (Execute.guardedModel x padding).val 5 = x.factors :=
    Execute.guardedModel_input x padding 5
  have he7 : (Execute.guardedModel x padding).val 7 = x.incidences :=
    Execute.guardedModel_input x padding 7
  rw [he0] at hn
  rw [he5] at hf
  rw [he7] at hi
  have hr := hv 18
  rw [Execute.guardedModel_radius] at hr
  obtain ⟨_, _, _, _, hQ, hs, hR, hN⟩ := Layout.model_core_values x padding
  have hQ' := hv 21
  have hs' := hv 25
  have hR' := hv 29
  have hN' := hv 31
  have heQ : (Execute.guardedModel x padding).val 21 = (produce x).Q :=
    (Execute.guardedModel_public x padding 4).trans hQ
  have heS : (Execute.guardedModel x padding).val 25 = (produce x).epsilonDen :=
    (Execute.guardedModel_public x padding 5).trans hs
  have heR : (Execute.guardedModel x padding).val 29 = (produce x).R :=
    (Execute.guardedModel_public x padding 6).trans hR
  have heN : (Execute.guardedModel x padding).val 31 = (produce x).N :=
    (Execute.guardedModel_public x padding 7).trans hN
  rw [heQ] at hQ'
  rw [heS] at hs'
  rw [heR] at hR'
  rw [heN] at hN'
  refine ⟨hn, hf, hi, hr, hQ', hs', ?_, hN', hR'⟩
  apply le_trans _ hN'
  change (produce x).r ^ (produce x).Q ≤ (produce x).r ^ (2 * (produce x).Q)
  exact Nat.pow_le_pow_right (by have := produce_r_ge_two x; omega) (by omega)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryModelBudgets
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryTupleVisitor
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The representative tuple is already a polynomial-length stack of escaped
frames, deepest head first. These fixed commands copy that stack, extract one
actual representative, and decrement its unary physical head address. They do
not enumerate assignments or construct a Cartesian product. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor

open OAI BitProgram StructuredCalls
open SignatureTupleProgram

def restartCost (a : Data) : ℕ :=
  2 * (a.stacks 840).length + 7 * (a.stacks 837).length +
    2 * (a.stacks 843).length + 7 * (a.stacks 845).length + 16

noncomputable def overlaidRepresentative (a : Data) (rf : Fin 8 → Bool) : Data :=
  HighQueryAdapter.NativeOverlay.result
    (HighQueryAdapter.NativeOverlay.resetState (stagedRepresentative a)) rf
noncomputable def installedRepresentative (a : Data) (rf : Fin 8 → Bool) : Data :=
  let b := overwriteState 145 869 (overlaidRepresentative a rf)
  ⟨readRegs b.regs 0 1 none,StackRoutines.clearStacks 859 b.stacks⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureHeadPrepare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Paid setup for one visited signature head. The physical key workspace,
old master words and selector outputs are cleared by the command itself. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadPrepare

open BitProgram StructuredCalls StackRoutines
open HighQueryAdapter QueryTupleVisitor
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport

noncomputable def mastersState (a : State 40 896) : State 40 896 :=
  overwriteState 671 175 (overwriteState 847 865 (overwriteState 141 864 a))

noncomputable def result (a : State 40 896) (keyRegs : Fin 8 → Bool)
    (selectRegs : Fin 4 → Bool) (W bits : List Bool)
    (rows : List (List (List Bool))) : State 40 896 :=
  NativeHeadSelect.result (NativeHeadSelect.resetState
    (mastersState (SignatureKeyNative.outputState (resetState a) keyRegs W bits rows))) selectRegs

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadPrepare
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryTupleState
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The attained-tuple traversal retains the actual query inputs and the
meaning of its current pair accumulator. These predicates contain word
identities and algebraic facts, with no execution or algorithm-service fields. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState

open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog SubexpLiftRing SubexpQuarticRing
open LeafProgram MomentsProgram LayoutProgram Subexp.ConstructivePacking MulticolorTypes
open TruncatedRingProgram SubexpSetupStorage

/-- These are the bytes of the genuine factor specification at one generated
node. In particular the lifting cutoff is the ring precision, rather than an
independently chosen positive number. Head buffers are produced inside the
visitor and are not supplied by this predicate. -/
structure QueryReady {r Q n d : ℕ} (q : Factor.Spec r Q n d) (node : Fin Q)
    (H : Finset (Fin n)) (high : H → Bool) (E U : Finset (Fin n))
    (P : ℕ) (a : Data) : Prop where
  lifting : q.u=q.p.t
  generatedTheta : q.theta=RingNodeProgram.nodeCode q.p.t d (node.val+1)
  sourceMinus : q.minus=q.p.minusOne
  ambient : a.stacks 128=List.replicate n true
  theta : a.stacks 78=RingProgram.flat q.theta
  modulus : a.stacks 194=q.p.modulus.bits
  table : a.stacks 201=RingTriple.tableEncoding
    (HornerProgram.modelTable q.p.t q.p.model q.p.modulus q.p.cache)
  width : a.stacks 202=q.width
  scalarZero : a.stacks 203=q.p.cache.zero.val
  degree : a.stacks 204=List.replicate d true
  one : a.stacks 207=RingProgram.flat q.p.ops.oneRun.1
  minus : a.stacks 211=RingProgram.flat q.minus
  precision : a.stacks 212=List.replicate q.p.t true
  order : a.stacks 243=List.replicate q.J true
  zero : a.stacks 280=RingProgram.flat q.p.ops.zeroRun.1
  code : a.stacks 281=RingProgram.flat q.code
  clauses : a.stacks 700=Encoding.encodeList id q.clauses
  rows : a.stacks 701=Encoding.encodeList id q.rawRows
  rowCount : a.stacks 704=List.replicate q.rawRows.length true
  markedIndex : a.stacks 705=Encoding.encodeNat q.mark
  markedFlag : a.stacks 706=[q.marked]
  indexModulus : BinaryArithmetic.toNat (a.stacks 707)=q.clauses.length
  indexWidth : (a.stacks 708).length=q.bitWidth
  highMask : a.stacks 702=List.ofFn (fun v : Fin n => decide (v∈H))
  highBits : a.stacks 703=List.ofFn (fun v : Fin n => if h : v∈H then high ⟨v,h⟩ else false)
  outer : a.stacks 858=List.ofFn (fun v : Fin n => decide (v∈E))
  inner : a.stacks 857=List.ofFn (fun v : Fin n => decide (v∈U))
  outerFree : Disjoint E H
  innerSubset : U⊆E
  colors : a.stacks 130=List.replicate r true
  nodes : a.stacks 131=List.replicate Q true
  typeWidth : a.stacks 132=List.replicate (Q*r) true
  positive : a.stacks 710=(LayoutProgramScalar.FromCounts.unsignedSaved q.p.hwords q.p.width q.p.power q.p.R q.p.aWord).hp
  negative : a.stacks 711=(LayoutProgramScalar.FromCounts.unsignedSaved q.p.hwords q.p.width q.p.power q.p.R q.p.aWord).hn
  sourceWidth : a.stacks 140=q.p.width
  power : a.stacks 712=q.p.power.1
  powerNegative : q.p.power.2=[]
  radius : a.stacks 138=List.replicate q.p.R true
  offset : a.stacks 139=q.p.aWord
  metadata : a.stacks 135=OAI.Algorithms.SubexponentialSAT.Subexp.SelectorProgram.rawRecords
    (OAI.Algorithms.SubexponentialSAT.Subexp.PackingMetadata.records q.packing (fun v => List.replicate v.val true) OAI.Algorithms.SubexponentialSAT.Subexp.CollisionProgram.encodeType)
  plans : a.stacks 136=LayoutOwnerFiberProgram.stream q.ps
  inverses : a.stacks 713=(List.ofFn (fun i : Fin Q => RingProgram.flat (InterpolationCacheProgram.inverseValue q.p.t q.p.model q.p.modulus q.p.cache q.p.minusOne
      (RingNodeProgram.nodeCode q.p.t d (i.val+1))))).flatten
  negatives : a.stacks 714=(List.ofFn (fun i : Fin Q => RingProgram.flat (InterpolationCacheProgram.negativeValue q.p.t q.p.model q.p.modulus q.p.cache q.p.minusOne
      (RingNodeProgram.nodeCode q.p.t d (i.val+1))))).flatten
  differences : a.stacks 715=(List.ofFn (fun i : Fin Q =>
    (List.ofFn (fun j : Fin Q => RingProgram.flat (InterpolationCacheProgram.differenceValue q.p.t q.p.model q.p.modulus q.p.cache q.p.minusOne
      (RingNodeProgram.nodeCode q.p.t d (i.val+1)) (RingNodeProgram.nodeCode q.p.t d (j.val+1))))).flatten)).flatten
  ringWidth : a.stacks 717=q.p.ringWidth
  rowWidth : a.stacks 716=q.p.rowWidth
  inverseDenominator : a.stacks 728=RingProgram.flat q.p.invDenom
  cacheCaps : ∀ p∈LeafNodeCacheProgram.directCopies,
    (a.stacks (p.1.castAdd 128)).length≤P
  ambientCap : (a.stacks 128).length≤P
  oneCap : (a.stacks 207).length≤P

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryReadyConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete query-entry facts from the actual arithmetic and native cache
producers. Pair masks are installed by the paid pair-start command. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReadyConstruction

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open LeafParametersProgram LeafProgram LeafProgram.PreparedSource
open LeafHeadSetupProgram QueryTupleState
open ProgramTapeReplay
attribute [local simp] Fin.coe_ofNat_eq_mod

/-- Physical query data before a pair is selected. In particular this record
places no condition on either pair-mask destination857/858. -/
structure CommonReady {r Q n d : ℕ} (q : Factor.Spec r Q n d) (node : Fin Q)
    (H : Finset (Fin n)) (high : H → Bool) (P : ℕ) (a : State 40 896) : Prop where
  lifting : q.u=q.p.t
  generatedTheta : q.theta=RingNodeProgram.nodeCode q.p.t d (node.val+1)
  sourceMinus : q.minus=q.p.minusOne
  ambient : a.stacks 128=List.replicate n true
  theta : a.stacks 78=RingProgram.flat q.theta
  modulus : a.stacks 194=q.p.modulus.bits
  table : a.stacks 201=RingTriple.tableEncoding
    (HornerProgram.modelTable q.p.t q.p.model q.p.modulus q.p.cache)
  width : a.stacks 202=q.width
  scalarZero : a.stacks 203=q.p.cache.zero.val
  degree : a.stacks 204=List.replicate d true
  one : a.stacks 207=RingProgram.flat q.p.ops.oneRun.1
  minus : a.stacks 211=RingProgram.flat q.minus
  precision : a.stacks 212=List.replicate q.p.t true
  order : a.stacks 243=List.replicate q.J true
  zero : a.stacks 280=RingProgram.flat q.p.ops.zeroRun.1
  code : a.stacks 281=RingProgram.flat q.code
  clauses : a.stacks 700=Encoding.encodeList id q.clauses
  rows : a.stacks 701=Encoding.encodeList id q.rawRows
  rowCount : a.stacks 704=List.replicate q.rawRows.length true
  markedIndex : a.stacks 705=Encoding.encodeNat q.mark
  markedFlag : a.stacks 706=[q.marked]
  indexModulus : BinaryArithmetic.toNat (a.stacks 707)=q.clauses.length
  indexWidth : (a.stacks 708).length=q.bitWidth
  highMask : a.stacks 702=List.ofFn (fun v : Fin n => decide (v∈H))
  highBits : a.stacks 703=List.ofFn (fun v : Fin n => if h : v∈H then high ⟨v,h⟩ else false)
  colors : a.stacks 130=List.replicate r true
  nodes : a.stacks 131=List.replicate Q true
  typeWidth : a.stacks 132=List.replicate (Q*r) true
  positive : a.stacks 710=(LayoutProgramScalar.FromCounts.unsignedSaved q.p.hwords q.p.width q.p.power q.p.R q.p.aWord).hp
  negative : a.stacks 711=(LayoutProgramScalar.FromCounts.unsignedSaved q.p.hwords q.p.width q.p.power q.p.R q.p.aWord).hn
  sourceWidth : a.stacks 140=q.p.width
  power : a.stacks 712=q.p.power.1
  powerNegative : q.p.power.2=[]
  radius : a.stacks 138=List.replicate q.p.R true
  offset : a.stacks 139=q.p.aWord
  metadata : a.stacks 135=OAI.Algorithms.SubexponentialSAT.Subexp.SelectorProgram.rawRecords
    (OAI.Algorithms.SubexponentialSAT.Subexp.PackingMetadata.records q.packing (fun v => List.replicate v.val true) OAI.Algorithms.SubexponentialSAT.Subexp.CollisionProgram.encodeType)
  plans : a.stacks 136=LayoutOwnerFiberProgram.stream q.ps
  inverses : a.stacks 713=(List.ofFn (fun i : Fin Q => RingProgram.flat (InterpolationCacheProgram.inverseValue q.p.t q.p.model q.p.modulus q.p.cache q.p.minusOne
      (RingNodeProgram.nodeCode q.p.t d (i.val+1))))).flatten
  negatives : a.stacks 714=(List.ofFn (fun i : Fin Q => RingProgram.flat (InterpolationCacheProgram.negativeValue q.p.t q.p.model q.p.modulus q.p.cache q.p.minusOne
      (RingNodeProgram.nodeCode q.p.t d (i.val+1))))).flatten
  differences : a.stacks 715=(List.ofFn (fun i : Fin Q =>
    (List.ofFn (fun j : Fin Q => RingProgram.flat (InterpolationCacheProgram.differenceValue q.p.t q.p.model q.p.modulus q.p.cache q.p.minusOne
      (RingNodeProgram.nodeCode q.p.t d (i.val+1)) (RingNodeProgram.nodeCode q.p.t d (j.val+1))))).flatten)).flatten
  ringWidth : a.stacks 717=q.p.ringWidth
  rowWidth : a.stacks 716=q.p.rowWidth
  inverseDenominator : a.stacks 728=RingProgram.flat q.p.invDenom
  cacheCaps : ∀ p∈LeafNodeCacheProgram.directCopies,
    (a.stacks (p.1.castAdd 128)).length ≤ P
  ambientCap : (a.stacks 128).length ≤ P
  oneCap : (a.stacks 207).length ≤ P

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReadyConstruction
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryVisitorHead
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The concrete one-head visitor composes its actual loader, paid key setup,
restricted head rescan and tuple multiplication. Exponential work is kept
separate from the reusable boundary and all-prefix storage bounds. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead
open OAI BitProgram StructuredCalls SqrtLog SqrtLog.LeafProgram SqrtLog.MomentsProgram
open SubexpLiftRing SubexpQuarticRing TruncatedRingProgram HeadIdentifierProgram
open BucketTupleProgram.Concrete QueryTupleState SubexpSetupStorage
open scoped BigOperators
noncomputable section

/-- These facts identify the actual produced source across all heads. Every
field is an equation about saved source data or its original integer meaning. -/
structure SourceFacts (s : LeafHeadSetupProgram.Native.Inputs) {d : ℕ}
    (q : Factor.Spec s.r s.Q s.n d) (H : Finset (Fin s.n))
    (owner : Fin q.ps.length → Fin s.n) (nativeOwner : Fin s.D → Fin s.n)
    (head : Fin s.Q → Fin s.n → Fin s.r) : Prop where
  dimension : q.ps.length=s.D
  plans_owner : ∀ i : Fin s.plans.length,
    (s.plans.get i).1=(nativeOwner (Fin.cast s.plans_length i)).val
  literal : ∀ j v,
    LayoutProducedMatrix.literalNat q.packing owner q.p.aWord.length q.p.R s.node j v=
    LayoutProducedMatrix.literalNat s.packing nativeOwner s.height.length s.R s.node j v
  selected : ∀ (g : Fin s.r) (v : Fin s.n),
    v.val∈chosenIds (predicate s.rows s.low (s.node.val*s.r+g.val)) s.n ↔
      ∃ _ : v∉H,head s.node v=g
  source_zero : ∀ id j (v : Fin s.n),v∈H →
    PerturbationAssembly.fixedSourceRow q.p q.ps q.packing s.n id j v=0
  rows_length : s.rows.length=s.n+s.N

/-- The physical compressed representative for this source head. -/
def representativeWord (s : LeafHeadSetupProgram.Native.Inputs) {d : ℕ}
    (q : Factor.Spec s.r s.Q s.n d) (H : Finset (Fin s.n))
    (owner : Fin q.ps.length → Fin s.n) (nativeOwner : Fin s.D → Fin s.n)
    (head : Fin s.Q → Fin s.n → Fin s.r) (facts : SourceFacts s q H owner nativeOwner head)
    (g : Fin s.r)
    (reps : ∀ k, Moments.Head (fun v : ResidualEmbedding.Free H => head s.node v.val) k → Bool) :
    List Bool :=
  List.ofFn (freeAssignmentEquiv H (fun v => head s.node v.val) g
    (chosenIds (predicate s.rows s.low (s.node.val*s.r+g.val)) s.n)
    (chosenIds_bound _ _) (chosenIds_nodup _ _) (facts.selected g) (reps g))

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryVisitorSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete execution of the two representative passes. The saved frame
stack is traversed in place, and every semantic dictionary is the one written
by the actual arithmetic command. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open SubexpSetupStorage LeafHeadSetupProgram
open SubexpLiftRing SubexpQuarticRing MomentsProgram TruncatedRingProgram
open QueryTupleState QueryTupleVisitor SignatureTupleProgram SignatureTupleSource

/-- The mask produced by the actual addressed head loader. -/
def mask (s : ProducedSource) (z : ℕ) : List Bool :=
  List.ofFn (fun v : Fin s.input.n =>
    HeadIdentifierProgram.predicate s.input.rows s.input.low z v.val)


open scoped BigOperators

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleComplete
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete cursor invariants for the fixed attained-signature controller.
The integer head matrices come from native source words.  Each boundary uses
one retained cap; reload and predecessor-scan prefix bounds remain transient.
-/

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete

open Classical
open OAI.Algorithms.SubexponentialSAT.SubexpLiftRing
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage
open SignatureTupleDFS SignatureTupleTraversal SignatureTupleProgram
open SignatureTupleNative SignatureTupleRefinement SignatureTupleLoader SignatureTupleSource


/-- The concrete raw/shifted matrix is retained as proof evidence only.
Runtime storage is the encoded shifted matrix on847 and bounded cursors. -/
structure ScanMatrix (s : ProducedSource) (depth candidate : ℕ) (a : State 40 896) : Prop where
  data : ∃ raw shifted,
    LayoutMatrixProgram.MatrixRel s.input.relation s.input.columnLength s.input.D
      (selectedHeads s.input.n s.input.rows s.input.low (s.base+depth)) raw ∧
    List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord (s.source.stacks 141))) raw shifted ∧
    ∀ hc : candidate < 2 ^ s.headSize depth,
      CandidateReady a (s.source.stacks 141) shifted (s.headSize depth) ⟨candidate,hc⟩

/-- Low649 is explicit: it is reused as the node base at the next pair.
The current physical address is maintained across every scan boundary. -/
structure ScanBoundary (s : ProducedSource) (F : ℕ) (depth : Fin s.input.r)
    (ancestors : Prefix (Representatives s.key) depth.val) (candidate : ℕ)
    (a : State 40 896) : Prop extends
    ScanStorage s.headSize s.key s.input.r s.base depth ancestors candidate a where
  bound : WordBound F a
  masters : SignatureHeadLoader.MasterFrame s.masters
    (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a)
  matrix : ScanMatrix s depth.val candidate a
  address649 : a.stacks 649=unary (s.base+depth.val)

structure LeafBoundary (s : ProducedSource) (F : ℕ)
    (ancestors : Prefix (Representatives s.key) s.input.r) (a : State 40 896) : Prop extends
    LeafStorage s.headSize s.key s.input.r s.base ancestors a where
  bound : WordBound F a
  masters : SignatureHeadLoader.MasterFrame s.masters
    (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a)
  zero_address649 : s.input.r=0 → a.stacks 649=unary s.base

structure HaltBoundary (s : ProducedSource) (F : ℕ) (a : State 40 896) : Prop where
  active : a.regs controllerPorts.active=false
  bound : WordBound F a
  masters : SignatureHeadLoader.MasterFrame s.masters
    (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a)
  address649 : a.stacks 649=unary s.base

inductive Boundary (s : ProducedSource) (F : ℕ) : Cursor s.key s.input.r → State 40 896 → Prop
  | scan {depth ancestors candidate a} : ScanBoundary s F depth ancestors candidate a →
      Boundary s F (.scan depth ancestors candidate) a
  | leaf {ancestors a} : LeafBoundary s F ancestors a → Boundary s F (.leaf ancestors) a
  | halt {a} : HaltBoundary s F a → Boundary s F .halt a

/-- Static bounds are chosen once before traversal; they are never updated
with a transient prefix bound or with a candidate's numeric value. -/
structure RetainedCap (s : ProducedSource) (F : ℕ) : Prop where
  positive : 1 ≤ F
  cursor : s.input.n+1 ≤ F
  frames : 6*s.input.r*(s.input.n+1)+(s.base+s.input.r)+(s.input.n+1) ≤ F
  output : SignatureHeadLoader.retainedOutputBound s.input.n s.input.N s.input.D
    s.input.columnLength s.bound ≤ F
  scanner : scannerEnvelope s.bound ≤ F

/-- The traversal relation carries the actual ring inputs and the SAME
physical851 dictionary's additive readout together with its cursor state. -/
structure Rel (s : ProducedSource) (F : ℕ) {r Q n d : ℕ}
    (q : LeafProgram.Factor.Spec r Q n d) (node : Fin Q)
    (H : Finset (Fin n)) (high : H → Bool) (E U : Finset (Fin n)) (P : ℕ)
    (cursor : Cursor s.key s.input.r) (acc : Truncated (q.p.model.O q.p.t) q.J)
    (a : State 40 896) : Prop where
  boundary : Boundary s F cursor a
  query : QueryTupleState.QueryReady q node H high E U P a
  accumulator : QueryTupleState.PairAccumulatorMeaning q acc a

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Complete runs of the fixed attained-signature controller. The retained
boundary cap is separate from transient prefix storage and measured time. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun

open Classical
open OAI SubexpLiftRing BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage
open SignatureTupleDFS SignatureTupleTraversal SignatureTupleProgram
open SignatureTupleNative SignatureTupleRefinement SignatureTupleLoader SignatureTupleSource
open SignatureTupleComplete

/-- Decode exactly the bounded numeric representative already retained by
the controller, in the actual loader's increasing ambient-coordinate order. -/
def emittedRepresentatives (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d)
    (H : Finset (Fin s.input.n)) (owner : Fin q.ps.length → Fin s.input.n)
    (head : Fin s.input.Q → Fin s.input.n → Fin s.input.r)
    (facts : QueryVisitorHead.SourceFacts s.input q H owner s.owner head)
    (ancestors : Prefix (Representatives s.key) s.input.r) (g : Fin s.input.r) :
    Moments.Head (fun v : ResidualEmbedding.Free H => head s.input.node v.val) g → Bool :=
  (BucketTupleProgram.Concrete.freeAssignmentEquiv H
    (fun v : ResidualEmbedding.Free H => head s.input.node v.val) g
    (selectedHeads s.input.n s.input.rows s.input.low (s.base+g.val))
    (HeadIdentifierProgram.chosenIds_bound _ _) (HeadIdentifierProgram.chosenIds_nodup _ _)
    (facts.selected g)).symm (AttainedSignatures.assignmentEquiv (s.headSize g.val) (ancestors g).val)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleSourceAlignment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The frontend's actual mask, the produced head rows and the authentic
source factory use the same ambient variables and the same full integer keys.
No selected-coordinate or factory-alignment witness is supplied by the caller. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSourceAlignment

open scoped BigOperators
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open MulticolorTypes Subexp.ConstructivePacking
open LeafHeadSetupProgram LeafParametersProgram LayoutProgram
open BucketTupleProgram.Concrete

/-- Reversing the physical descending mask gives the forward ambient mask. -/
theorem forward_bits (q : LeafQueryFrontend.Query) :
    q.forward = List.ofFn (fun v => decide (v ∈ HighMarkedFrontend.highSet q)) := by
  rw [LeafQueryFrontend.Query.forward, HighMarkedFrontend.physical_high_mask,
    HighIncidenceProgram.descendingHighMask,
    OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Order.coordinates_stream, List.reverse_reverse]

/-- Every ambient coordinate is retained, including variables with no source
occurrence. The low mask is the actual complement of the produced high set. -/
theorem low_bits (q : LeafQueryFrontend.Query) :
    q.forward.map Bool.not =
      HeadIdentifierProgram.lowBits (fun v => decide (v ∉ HighMarkedFrontend.highSet q)) := by
  rw [forward_bits]
  simp [HeadIdentifierProgram.lowBits, List.map_ofFn, Function.comp_def]

section Query
attribute [local instance] Classical.propDecidable
variable (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k))
local notation "p" => LeafProgram.Query.packingProblem q k hg
variable (first : Word (LeafProgram.Query.packingProblem q k hg).r
    (LeafProgram.Query.packingProblem q k hg).Q)
  (tail : List (Word (LeafProgram.Query.packingProblem q k hg).r
    (LeafProgram.Query.packingProblem q k hg).Q))
  (node : Fin (LeafProgram.Query.packingProblem q k hg).Q)
local notation "s" => Native.queryInputsAddressed q k hg first tail node
local notation "H" => HighMarkedFrontend.highSet q
local notation "head" => (fun t v => ProducedQueryRank.words p first tail (Sum.inl v) t)
local notation "owner" => ProducedQueryRank.owner p
local notation "js" => (fun g : Fin (PackingCallerProgram.Problem.r p) =>
  selectedHeads (Native.Inputs.n s) (Native.Inputs.rows s) (Native.Inputs.low s)
    (Fin.val node * PackingCallerProgram.Problem.r p + Fin.val g))
include q k hg first tail node

theorem query_rows_length : (s).rows.length = (s).n+(s).N := by
  change (ProducedQueryRank.rows p first tail).length = (p).n+(p).factors
  simp [ProducedQueryRank.rows, PackingCallerProgram.Problem.words_length]

/-- The actual row lookup selects exactly the free coordinates of the
produced head, without a packing-coverage or occurrence premise. -/
theorem selected_mem (g : Fin (p).r) (v : Fin (p).n) :
    v.val ∈ js g ↔ v ∉ H ∧ head node v = g := by
  change v.val ∈ selectedHeads (p).n (ProducedQueryRank.rows p first tail)
    (q.forward.map Bool.not) (node.val*(p).r+g.val) ↔ _
  rw [low_bits q]
  simp only [selectedHeads, HeadIdentifierProgram.chosenIds, List.mem_filter,
    List.mem_range, v.isLt, true_and, HeadIdentifierProgram.predicate]
  rw [ProducedQueryRank.head_row, HeadIdentifierProgram.encodeWord_getD]
  have hvl : v.val < BinaryArithmetic.toNat q.ambient := v.isLt
  let v' : Fin (BinaryArithmetic.toNat q.ambient) := ⟨v.val,hvl⟩
  have hv : v'=v := Fin.ext rfl
  have hl : (HeadIdentifierProgram.lowBits (fun w => decide (w ∉ H))).getD v.val false =
      decide (v' ∉ H) := by
    unfold HeadIdentifierProgram.lowBits
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hvl),
      List.getElem_ofFn]
  rw [hl]
  simp only [Bool.and_eq_true,decide_eq_true_eq]
  rw [hv]
  exact Iff.rfl

theorem selected_spec (g : Fin (p).r) (v : Fin (p).n) :
    v.val ∈ js g ↔ ∃ _ : v ∉ H, head node v = g :=
  by simpa only [exists_prop] using selected_mem q k hg first tail node g v

omit first tail node in
/-- Every actual incidence owner is low; unused low coordinates still
participate in selected_mem independently of whether they own an incidence. -/
theorem owner_low (i : Fin (p).incidences) : owner i ∉ H := by
  let entry := (PackingIncidenceInput.Semantics.nativeEntries (p).scopes (p).mask).get i
  have hm := List.get_mem (PackingIncidenceInput.Semantics.nativeEntries (p).scopes (p).mask) i
  have hl := LeafStatisticsSemantics.entries_owner_low (p).scopes (p).mask 0 (p).scopes.length
    entry.1 entry.2 hm
  obtain ⟨j,hj,hb⟩ := (LeafStatisticsSemantics.lowOwners_mem 0 entry.1 (p).mask).mp hl
  have hj' : j.val = (owner i).val := by
    change j.val = entry.1
    simpa only [Nat.zero_add] using hj
  have hmask : q.forward.getD (owner i).val false = false := by
    change (p).mask.getD (owner i).val false = false
    rw [← hj', List.getD_eq_getElem _ _ j.isLt]
    exact hb
  have he := congrArg (fun bs : List Bool => bs.getD (owner i).val false) (forward_bits q)
  have hoi : (owner i).val < BinaryArithmetic.toNat q.ambient := (owner i).isLt
  have hlow : (⟨(owner i).val,hoi⟩ : Fin (BinaryArithmetic.toNat q.ambient)) ∉ H := by
    simpa [List.getD_eq_getElem?_getD, hoi] using he.symm.trans hmask
  change (⟨(owner i).val,hoi⟩ : Fin (BinaryArithmetic.toNat q.ambient)) ∉ H
  exact hlow

/-- Changing factor IDs to physical ambient-offset addresses preserves the
owner in each actual saved plan position. -/
theorem plans_owner (i : Fin (s).plans.length) :
    ((s).plans.get i).1 = (owner (Fin.cast (s).plans_length i)).val := by
  unfold ProducedQueryRank.owner PackingIncidenceInput.Semantics.owner
  have hn : i.val < (PackingIncidenceInput.Semantics.nativeEntries
      (p).scopes (p).mask).length := (Fin.cast (s).plans_length i).isLt
  have ha : i.val < (PackingIncidenceInput.addressedEntries
      (p).scopes (p).n (p).mask).length := by
    simpa only [PackingIncidenceInput.addressedEntries_length] using hn
  have ha' : i.val < ((PackingIncidenceInput.Semantics.nativeEntries
      (p).scopes (p).mask).map (fun x => (x.1,(p).n+x.2))).length := by
    simpa only [List.length_map] using hn
  change ((PackingIncidenceInput.addressedEntries (p).scopes (p).n (p).mask)[i.val]'ha).1 =
    ((PackingIncidenceInput.Semantics.nativeEntries (p).scopes (p).mask)[i.val]'hn).1
  change (((PackingIncidenceInput.Semantics.nativeEntries (p).scopes (p).mask).map
    (fun x => (x.1,(p).n+x.2)))[i.val]'ha').1 =
      ((PackingIncidenceInput.Semantics.nativeEntries (p).scopes (p).mask)[i.val]'hn).1
  rw [List.getElem_map]


end Query
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSourceAlignment
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryEmittedSourceTarget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The exact completed native tuple aggregate, with the same bounded numeric
representatives and the same physical factor IDs, has the source-target value. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEmittedSourceTarget
open scoped BigOperators
open Classical Polynomial OAI OAI.Algorithms.SubexponentialSAT.SqrtLog
open LeafProgram NodeConcrete Moments
open SignatureTupleDFS SignatureTupleTraversal SignatureTupleSource
open SignatureTupleRun HeadSourceLocality BucketTupleProgram.Concrete

variable (s : ProducedSource) {d : ℕ}
    (q : Factor.Spec s.input.r s.input.Q s.input.n d)
    (H : Finset (Fin s.input.n)) (high : H → Bool)
    (owner : Fin q.ps.length → Fin s.input.n)
    (head : Fin s.input.Q → Fin s.input.n → Fin s.input.r)
    (facts : QueryVisitorHead.SourceFacts s.input q H owner s.owner head)

/-- The physical selected-coordinate stream for one produced head. -/
def selectedIds (g : Fin s.input.r) : List ℕ :=
  LeafHeadSetupProgram.selectedHeads s.input.n s.input.rows s.input.low (s.base+g.val)

theorem selectedIds_bound (g : Fin s.input.r) :
    ∀ v ∈ selectedIds s g, v < s.input.n :=
  HeadIdentifierProgram.chosenIds_bound _ _

theorem selectedIds_nodup (g : Fin s.input.r) : (selectedIds s g).Nodup :=
  HeadIdentifierProgram.chosenIds_nodup _ _

/-- The canonical physical order identifies selected bits with typed free-head
assignments. Keeping this equivalence named avoids reconstructing its dependent
proof arguments when it is used in both directions. -/
def selectedEquiv (g : Fin s.input.r) :
    (Head (fun v : ResidualEmbedding.Free H => head s.input.node v.val) g → Bool) ≃
      (Fin (selectedIds s g).length → Bool) :=
  BucketTupleProgram.Concrete.freeAssignmentEquiv H
    (fun v : ResidualEmbedding.Free H => head s.input.node v.val) g
    (selectedIds s g) (selectedIds_bound s g) (selectedIds_nodup s g)
    (facts.selected g)

/-- Decode the controller's actual bounded numeric candidates in the actual
increasing selected-coordinate order, without choosing new representatives. -/
def enumerate (g : Fin s.input.r) : Fin (2^s.headSize g.val) ≃
    (Head (fun v : ResidualEmbedding.Free H => head s.input.node v.val) g → Bool) :=
  (AttainedSignatures.assignmentEquiv (s.headSize g.val)).trans
    (selectedEquiv s q H owner head facts g).symm

@[simp] theorem emittedRepresentatives_eq
    (ancestors : Prefix (Representatives s.key) s.input.r) :
    emittedRepresentatives s q H owner head facts ancestors =
      fun g => enumerate s q H owner head facts g (ancestors g).val := rfl

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEmittedSourceTarget
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryHeadSourceFacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual addressed query source fixes the native layout and factor
specification together. Its semantic facts require no independent source,
selected-head, integer-matrix or successful-layout alignment premise. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadSourceFacts
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open MulticolorTypes Subexp.ConstructivePacking SubexpLiftRing SubexpQuarticRing
open LeafHeadSetupProgram LeafParametersProgram LayoutProgram LeafProgram
open SignatureTupleSourceAlignment

variable (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k))
local notation "p" => LeafProgram.Query.packingProblem q k hg
variable (first : Word (LeafProgram.Query.packingProblem q k hg).r
    (LeafProgram.Query.packingProblem q k hg).Q)
  (tail : List (Word (LeafProgram.Query.packingProblem q k hg).r
    (LeafProgram.Query.packingProblem q k hg).Q))
  (node : Fin (LeafProgram.Query.packingProblem q k hg).Q)
local notation "s" => Native.queryInputsAddressed q k hg first tail node
variable (physical : Data)
  (ready : Native.Ready (Native.queryInputsAddressed q k hg first tail node) physical)
  (bound : ℕ) (bounded : OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage.WordBound bound physical)
  (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
  (hc : CacheCorrect (Native.queryInputsAddressed q k hg first tail node).height
    (unary (Native.queryInputsAddressed q k hg first tail node).R)
    (Native.queryInputsAddressed q k hg first tail node).width words)

/-- Physical output data of the actual addressed loader and cache producer,
with the semantic owners and plans fixed by that same addressed constructor. -/
def addressedSource : SignatureTupleSource.ProducedSource where
  input := s
  source := physical
  ready := ready
  bound := bound
  bounded := bounded
  rows := query_rows_length q k hg first tail node
  owner := ProducedQueryRank.owner p
  plans := fun i => (s).plans.get (Fin.cast (s).plans_length.symm i)
  plans_eq := (List.ofFn_get (s).plans).symm.trans (List.ofFn_congr (s).plans_length _)
  owners_eq := by
    intro i
    have h := plans_owner q k hg first tail node (Fin.cast (s).plans_length.symm i)
    change ((s).plans.get (Fin.cast (s).plans_length.symm i)).1 =
      (ProducedQueryRank.owner p i).val
    have ho : ProducedQueryRank.owner p
        (Fin.cast (s).plans_length (Fin.cast (s).plans_length.symm i)) =
        ProducedQueryRank.owner p i := Fin.ext rfl
    exact h.trans (congrArg Fin.val ho)
  addressRegisters := ra
  dimensionRegisters := rd
  cacheRegisters := rc
  cacheWords := words
  cache := hc

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadSourceFacts
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryPairEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual finite-difference callback uses the physical pair masks and
one semantic node accumulator. The reference support decoding below is used
only in the proof; the executed controller retains its four finite words. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open LeafProgram QueryTupleState QueryPairCommit QueryReadyConstruction
open SignatureTupleSource
open scoped BigOperators
open SqrtLog.ProgramTapeReplay

/-- The semantic accumulator and compact off-controller words form the DFS
invariant. The four controller lengths are bounded by its separate geometry. -/
structure Invariant {r Q n d : ℕ} (q : Factor.Spec r Q n d) (node : Fin Q)
    (H : Finset (Fin n)) (high : H → Bool) (P F : ℕ)
    (source : ProducedSource) (origin : State 40 896)
    (total : Truncated (q.p.model.O q.p.t) q.J) (a : State 40 896) : Prop where
  common : CommonReady q node H high P a
  accumulator : NodeAccumulatorMeaning q total a
  compact : ∀ i,(∀ j,i≠QueryStreamProgram.pairPorts.stack j) → (a.stacks i).length ≤ F
  masters : SignatureHeadLoader.MasterFrame source.masters
    (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a)
  frame : ∀ i ∈ framePorts,a.stacks i=origin.stacks i

def callbackSpace (s : ProducedSource) {d : ℕ}
    (q : Factor.Spec s.input.r s.input.Q s.input.n d) (N F B : ℕ) : ℕ :=
  max (SignatureTupleRun.completeSpace s q F B) (896*F+startBudget s.input.n F+commitBudget q N F)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QuerySourceSnapshot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! A proof-only native source snapshot retains the actual readiness words.
It does not clear the running machine. The loader starts from the same native
input and generated cache, so all of its eighteen masters remain identical.
Unrelated scratch from earlier nodes is excluded from the source-local cap. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QuerySourceSnapshot
open OAI BitProgram StructuredCalls SqrtLog SubexpSetupStorage
open LeafHeadSetupProgram LeafParametersProgram LeafProgram LeafProgram.PreparedSource

theorem snapshot_ready {s : Native.Inputs} {a : LeafHeadSetupProgram.Data}
    (ha : Native.Ready s a) : Native.Ready s (snapshot a) := by
  have hf := snapshot_retained a
  exact ⟨(hf 128 (by decide)).trans ha.ambient,(hf 129 (by decide)).trans ha.factors,
    (hf 130 (by decide)).trans ha.colors,(hf 131 (by decide)).trans ha.nodes,
    (hf 132 (by decide)).trans ha.wordWidth,(hf 133 (by decide)).trans ha.words,
    (hf 134 (by decide)).trans ha.low,(hf 135 (by decide)).trans ha.metadata,
    (hf 136 (by decide)).trans ha.plans,(hf 138 (by decide)).trans ha.order,
    (hf 139 (by decide)).trans ha.height,(hf 140 (by decide)).trans ha.width,
    (congrArg BinaryArithmetic.toNat (hf 141 (by decide))).trans ha.offset,
    (hf 307 (by decide)).trans ha.node,(hf 660 (by decide)).trans ha.tuples,
    (hf 665 (by decide)).trans ha.marker⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QuerySourceSnapshot
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryNodeEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete initialization of a node evaluation. The paid node read, layout
load, native cache bootstrap and pair setup are the fixed commands used by the
streaming query; no evaluator is supplied to these constructions. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation

open OAI BitProgram StructuredCalls SqrtLog SubexpSetupStorage
open LeafHeadSetupProgram QueryTupleState

noncomputable def loadedNode (a : Data) (bits : List Bool) (tail : List (List Bool)) : Data :=
  NativeLayoutLoad.result (QueryAssembler.Nodes.begunNode a bits tail)

/-- Reading the current node leaves the parked source bank and node index intact. -/
theorem begun_sourceBank (s : Native.Inputs) (a : Data)
    (bits : List Bool) (tail : List (List Bool)) (h : NativeLayoutLoad.SourceBank s a) :
    NativeLayoutLoad.SourceBank s (QueryAssembler.Nodes.begunNode a bits tail) := by
  have hf := QueryAssembler.Nodes.begunNode_frame a bits tail
  exact ⟨(hf 730 (by decide)).trans h.ambient,
    (hf 731 (by decide)).trans h.factors,(hf 732 (by decide)).trans h.colors,
    (hf 733 (by decide)).trans h.nodes,(hf 734 (by decide)).trans h.wordWidth,
    (hf 735 (by decide)).trans h.words,(hf 736 (by decide)).trans h.low,
    (hf 737 (by decide)).trans h.metadata,(hf 738 (by decide)).trans h.plans,
    (hf 740 (by decide)).trans h.order,(hf 741 (by decide)).trans h.height,
    (hf 742 (by decide)).trans h.width,
    (congrArg BinaryArithmetic.toNat (hf 743 (by decide))).trans h.offset,
    (hf 307 (by decide)).trans h.node⟩

theorem loadedNode_ready (s : Native.Inputs) (a : Data)
    (bits : List Bool) (tail : List (List Bool)) (h : NativeLayoutLoad.SourceBank s a) :
    Native.Ready s (projectState SignatureHeadLoader.leafRegs
      QueryAssembler.Nodes.lowPort (loadedNode a bits tail)) :=
  NativeLayoutLoad.result_ready s _ (begun_sourceBank s a bits tail h)

noncomputable def bootstrapped (s : Native.Inputs) (a : Data)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool)) : Data :=
  embedState SignatureHeadLoader.leafRegs QueryAssembler.Nodes.lowPort a
    (SignatureHeadLoader.bootstrapResult s
      (projectState SignatureHeadLoader.leafRegs QueryAssembler.Nodes.lowPort a) ra rd rc words)

theorem loadedNode_frame (a : Data) (bits : List Bool) (tail : List (List Bool))
    (i : Fin 896) (hi : i ∈ framePorts) :
    (loadedNode a bits tail).stacks i=a.stacks i := by
  have hn : i ∉ NativeLayoutLoad.clearPorts ∧ i ∉ 301::QueryAssembler.Nodes.nodeResetPorts := by
    simp only [framePorts,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals decide
  exact (NativeLayoutLoad.result_frame _ i hn.1).trans
    (QueryAssembler.Nodes.begunNode_frame a bits tail i hn.2)

open LeafParametersProgram LeafProgram LeafProgram.PreparedSource

noncomputable def sourceSnapshot (a : Data) (bits : List Bool) (tail : List (List Bool)) :
    LeafHeadSetupProgram.Data :=
  projectState SignatureHeadLoader.leafRegs QueryAssembler.Nodes.lowPort (loadedNode a bits tail)

theorem sourceSnapshot_ready (s : Native.Inputs) (a : Data)
    (bits : List Bool) (tail : List (List Bool)) (h : NativeLayoutLoad.SourceBank s a) :
    Native.Ready s (sourceSnapshot a bits tail) := loadedNode_ready s a bits tail h

/-- Repeating a node requires only the parked native inputs and the current
index to have the fresh source cap. Paid loading discards stale native scratch;
no bound on unrelated caller words is used here. -/
theorem sourceSnapshot_native_bound (a : Data) (bits : List Bool)
    (tail : List (List Bool)) (A : ℕ)
    (hparked : ∀ j : Fin 14,
      (a.stacks (NativeLayoutLoad.stackMap (LayoutMasters.high j))).length ≤ A)
    (hindex : (a.stacks 307).length ≤ A) :
    ∀ i : Fin 768, ((128 : ℕ) ≤ Fin.val i ∧ Fin.val i < 142) ∨ i=307 ∨ i=660 ∨ i=665 →
      ((sourceSnapshot a bits tail).stacks i).length ≤ A := by
  have hlow (j : Fin 14) :
      ((sourceSnapshot a bits tail).stacks (LayoutMasters.low j)).length ≤ A := by
    change ((NativeLayoutLoad.result (QueryAssembler.Nodes.begunNode a bits tail)).stacks
      (NativeLayoutLoad.stackMap (LayoutMasters.low j))).length ≤ A
    rw [NativeLayoutLoad.result_low]
    have hf : NativeLayoutLoad.stackMap (LayoutMasters.high j) ∉         301::QueryAssembler.Nodes.nodeResetPorts := by
      simp only [QueryAssembler.Nodes.nodeResetPorts,List.mem_cons,
        List.not_mem_nil,or_false]
      intro h
      rcases h with h|h|h|h|h|h|h|h|h|h
      all_goals have hv := congrArg Fin.val h
      all_goals change 730+j.val=_ at hv
      all_goals simp only [Fin.coe_ofNat_eq_mod,Nat.reduceMod] at hv
      all_goals have hj := j.isLt
      all_goals omega
    rw [QueryAssembler.Nodes.begunNode_frame a bits tail _ hf]
    exact hparked j
  intro i hi
  rcases hi with hi|rfl|rfl|rfl
  · let j : Fin 14 := ⟨i.val-128,by omega⟩
    have hj : LayoutMasters.low j=i := by apply Fin.ext; change 128+(i.val-128)=i.val; omega
    rw [←hj]
    exact hlow j
  · exact (congrArg List.length (loadedNode_frame a bits tail 307 (by decide))).le.trans hindex
  · change ((NativeLayoutLoad.result _).stacks (NativeLayoutLoad.stackMap 660)).length ≤ A
    rw [NativeLayoutLoad.result_empty _ 660 (by decide)]
    exact Nat.zero_le _
  · change ((NativeLayoutLoad.result _).stacks (NativeLayoutLoad.stackMap 665)).length ≤ A
    rw [NativeLayoutLoad.result_empty _ 665 (by decide)]
    exact Nat.zero_le _

/-- The genuine restricted source constructor receives bounds on exactly
its sixteen retained native words, even after arbitrarily large local scratch. -/
theorem sourceSnapshot_retained_bound (a : Data) (bits : List Bool)
    (tail : List (List Bool)) (A : ℕ)
    (hparked : ∀ j : Fin 14,
      (a.stacks (NativeLayoutLoad.stackMap (LayoutMasters.high j))).length ≤ A)
    (hindex : (a.stacks 307).length ≤ A) :
    ∀ i ∈ QuerySourceSnapshot.retainedPorts,
      ((sourceSnapshot a bits tail).stacks i).length ≤ A := by
  intro i hi
  apply sourceSnapshot_native_bound a bits tail A hparked hindex i
  simp only [QuerySourceSnapshot.retainedPorts,List.mem_cons,
    List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals decide

open SubexpLiftRing SubexpQuarticRing
open scoped BigOperators


/-- The source bank already pays for the current index: its unary node count
bounds the actual unary index. No independent per-node cap is assumed. -/
theorem sourceSnapshot_bank_bound (s : Native.Inputs) (a : Data)
    (bits : List Bool) (remaining : List (List Bool)) (A : ℕ)
    (hbank : NativeLayoutLoad.SourceBank s a)
    (hparked : ∀ j : Fin 14,
      (a.stacks (NativeLayoutLoad.stackMap (LayoutMasters.high j))).length ≤ A) :
    ∀ i ∈ QuerySourceSnapshot.retainedPorts,
      ((sourceSnapshot a bits remaining).stacks i).length ≤ A := by
  apply sourceSnapshot_retained_bound a bits remaining A hparked
  have hQ := hparked 3
  change (a.stacks 733).length ≤ A at hQ
  rw [hbank.nodes,unary,List.length_replicate] at hQ
  rw [hbank.node,unary,List.length_replicate]
  exact s.node.isLt.le.trans hQ

section AddressedSource
variable (query : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (query.input k))
  (first : MulticolorTypes.Word (LeafProgram.Query.packingProblem query k hg).r
    (LeafProgram.Query.packingProblem query k hg).Q)
  (tail : List (MulticolorTypes.Word (LeafProgram.Query.packingProblem query k hg).r
    (LeafProgram.Query.packingProblem query k hg).Q))
  (node : Fin (LeafProgram.Query.packingProblem query k hg).Q)
local notation "native" => Native.queryInputsAddressed query k hg first tail node
variable (a : Data) (bits : List Bool) (remaining : List (List Bool)) (A : ℕ)
  (hbank : NativeLayoutLoad.SourceBank (Native.queryInputsAddressed query k hg first tail node) a)
  (hparked : ∀ j : Fin 14,
    (a.stacks (NativeLayoutLoad.stackMap (LayoutMasters.high j))).length ≤ A)
  (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
  (hc : CacheCorrect (Native.queryInputsAddressed query k hg first tail node).height
    (unary (Native.queryInputsAddressed query k hg first tail node).R)
    (Native.queryInputsAddressed query k hg first tail node).width words)

/-- The source used by the concrete tuple run is built from this actual
node's loaded input and this actual bootstrap's cache witnesses. Its fresh cap
uses only parked input words; the running state is never replaced or cleared. -/
noncomputable def nodeSource : SignatureTupleSource.ProducedSource :=
  QueryHeadSourceFacts.addressedSource query k hg first tail node
    (QuerySourceSnapshot.snapshot (sourceSnapshot a bits remaining))
    (QuerySourceSnapshot.snapshot_ready (sourceSnapshot_ready native a bits remaining hbank))
    A (QuerySourceSnapshot.snapshot_bound _ A
      (sourceSnapshot_bank_bound native a bits remaining A hbank hparked))
    ra rd rc words hc

end AddressedSource


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeHashQueries
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Literal marked and accepted query continuations for the actual prepared
leaf. Shadow execution preserves unrestricted caller words for time; the
same replay counts those words separately in maximum prefix storage. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries

open BitProgram StructuredCalls SqrtLog DisjointReuse
open HighFrontendSources HashGreedyCode HashQueryEntry LeafProgram
open HashGreedyProgram.NativeRound


open LeafParametersProgram HighMarkedFrontend HighQuerySetup ProducedQueryResources

/-- This is the literal full-count expression returned by the fixed native
high iterator. Its source uses the unchanged ambient dimension. -/
noncomputable def literalCount (q : LeafQueryFrontend.Query)
    (source : RawCNF (BinaryArithmetic.toNat q.ambient))
    (hsource : q.clauses = HashInputProgram.Expansion.encodedClauses source) : ℕ :=
  PreparedBranchCount.fullCount
    ((PreparedSource.castRows (congrArg List.length hsource) q.rows).map
      (fun terms => terms.map (fun term =>
        (term.2, HashInputProgram.Expansion.originalClause source term.1))))
    q.mark.isSome (source.getD (PreparedSource.markIndex q) [])


open NativeQueryInputBounds Statement

attribute [local irreducible] Execute.guardedModel

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries
end


