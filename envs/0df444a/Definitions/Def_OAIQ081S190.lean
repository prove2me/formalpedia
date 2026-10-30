-- Prove2me | Definitions.Def_OAIQ081S190
-- name    : OAIQ081S190
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T23:49:01.263375+00:00
-- url     : https://prove2.me/theorems/0979cbfc-80f2-44e1-8893-a083a97ccc75
-- title:
--   Definitions bundle OAIQ081S190 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 75 declarations of OpenAI's Lean: 66 definitions, 5 inductive types or structures and 4 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedExecution`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedResources`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.arithmeticSteps`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.arithmetic_output`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.cache`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.cleared`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.complete`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.counter`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.data`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.degree`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.execution`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.first`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.guard`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.half`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.high_guard`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.kept`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.mask`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.modulus`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.nodup`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.output`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.packed`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.packed_words`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.packingSteps`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.prefix_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.preparation`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.preparation_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.preparation_time`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.resources`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.rest`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.ringState`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.seed`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.seedRegs`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.seedSteps`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.seed_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun.seed_time`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup.SetupData`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup.SetupData.front`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup.SetupData.frontendSteps`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup.SetupData.guard` and 31 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: [`SubexponentialSAT_SqrtLogSpace_HighQuerySetup`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighQuerySetup.lean), [`SubexponentialSAT_SqrtLogSpace_NativeHashQuerySetup`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeHashQuerySetup.lean), [`SubexponentialSAT_SqrtLogSpace_NativeQueryPreparation`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeQueryPreparation.lean), [`SubexponentialSAT_SqrtLogSpace_QueryCountReconstruction`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryCountReconstruction.lean), [`SubexponentialSAT_SqrtLogSpace_QueryPairEvaluation`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryPairEvaluation.lean), [`SubexponentialSAT_SqrtLogSpace_QueryVisitorHead`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryVisitorHead.lean), [`SubexponentialSAT_SqrtLogSpace_SignatureTupleRun`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureTupleRun.lean), [`SubexponentialSAT_SqrtLog_PackingCallerProgram`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingCallerProgram.lean), [`SubexponentialSAT_SqrtLog_PackingCallerProgramJoin`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingCallerProgramJoin.lean), [`SubexponentialSAT_Subexp_UniversalRowExecution`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/Subexp/UniversalRowExecution.lean).
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S186`, `OAIQ081S187` and `OAIQ081S188` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ081S192`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.prepare_seed`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup.accepted_with_shadow`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup.marked_with_shadow`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEmittedSourceTarget.signed_target`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.nodeSource_target`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation.callback_cursor_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation.callback_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.evaluateHead_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.head_multiply_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.prepare_head_multiply_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.evaluation_pass`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.visitor_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.positive_run_resources` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.run_resources`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryReturnReplay.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryReturnReplay.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup.accepted_with_shadow`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup.marked_with_shadow`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEmittedSourceTarget.signed_target`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.nodeSource_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.nodeSource_target`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation.callback_cursor_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation.callback_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.evaluateHead_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.head_multiply_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.prepare_head_multiply_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.evaluation_pass`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.visitor_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.positive_run_resources`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.run_resources`, `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowEmitCall.command_eval` and `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowSourceBound.source_bound_le`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S186
import Definitions.Def_OAIQ081S187
import Definitions.Def_OAIQ081S188

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramJoin
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open PackingLoaderProgram PackingIncidenceInput

theorem compute_eval (a : Wide.Data) (p : Problem) (hs : Sources a p) (he : Empty a)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q))
    (hrows : (w::tail).map ReadPlan.encodeWord=AssignmentAlphabetSemantics.wordBytes p.r p.Q)
    (haN : (w::tail).Nodup) (haC : ∀ z,z∈w::tail) :
    ∃ t b, t ≤ computeBudget a p w tail ∧ Eval compute t a b ∧
      b.stacks=(middle a p w tail).stacks ∧
      (∀ i : Fin 40,16 ≤ i.val → b.regs i=a.regs i) := by
  obtain ⟨b,hb,hbs,hbr⟩ := Wide.stage_eval a he.temporary
  have hproj : projectState Wide.registers Wide.ports b=
      framed (Wide.parameterStore (Wide.project a))
        (Install.input (b.regs ∘ Wide.registers) p.scopes p.n p.mask) := by
    apply SubexponentialSAT.CounterForPrograms.data_ext
    · simp [projectState,Entry.install_eq]
    · have hh := congrArg StructuredProgram.State.stacks
        (Wide.staged_bank (Wide.project a) he.bank p.scopes p.n p.mask hs.scopes hs.ambientUnary hs.mask)
      funext i
      have hi := congrFun hh i
      simp only [projectState,framed_stack,Entry.install_eq] at hi ⊢
      simpa only [hbs] using hi
  obtain ⟨rf,nt,hnt,ht⟩ := core_run (Wide.parameterStore (Wide.project a)) p
    hs.parameters (parameters_workspace a) (b.regs ∘ Wide.registers) w tail hrows haN haC
  rw [← hproj] at ht
  have hc := Wide.bankCall_eval coreProgram b _ ht
  let e := embedState Wide.registers Wide.ports b
    (framed (outputStore (Wide.parameterStore (Wide.project a)) p w tail)
      (⟨rf,fun _=>[]⟩ : Small))
  refine ⟨_,e,by unfold computeBudget; omega,hb.seq hc,?_,?_⟩
  · funext i
    by_cases hi : 417 ≤ i.val ∧ i.val < 481
    · let j : Fin 64 := ⟨i.val-417,by omega⟩
      have hj : Wide.ports j=i := by apply Fin.ext; change 417+(i.val-417)=i.val; omega
      rw [← hj,middle_bank]
      change (embedState Wide.registers Wide.ports b _).stacks (Wide.ports j)=_
      rw [embedState_stack _ _ _ _ Wide.ports.injective]
      simp only [bankOutput,framed_stack]
    · have ho : i.val < 417 ∨ 481 ≤ i.val := by omega
      change (embedState Wide.registers Wide.ports b _).stacks i=_
      rw [Wide.bank_frame _ _ _ ho,middle_frame _ _ _ _ _ ho,hbs]
      exact Wide.staged_frame _ i ho
  · intro i hi
    exact (Wide.bank_register_frame b _ i hi).trans (hbr i hi)

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed per-query caller for actual native incidence construction, word
selection, layout metadata construction, and paid master-bank parking. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem command_eval (a : Wide.Data) (p : Problem) (hs : Sources a p) (he : Empty a)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q))
    (hrows : (w::tail).map ReadPlan.encodeWord=AssignmentAlphabetSemantics.wordBytes p.r p.Q)
    (haN : (w::tail).Nodup) (haC : ∀ z,z∈w::tail) :
    ∃ t b, t+1 ≤ budget a p w tail ∧ Eval command t a b ∧
      b.stacks=(result a p w tail).stacks ∧
      (∀ i : Fin 40,16 ≤ i.val → b.regs i=a.regs i) := by
  obtain ⟨tc,c,htc,hc,hcs,hcr⟩ := compute_eval a p hs he w tail hrows haN haC
  have ht : c.stacks 684=[] := by
    rw [hcs,middle_frame _ _ _ _ _ (by norm_num)]
    exact he.temporary
  obtain ⟨b,hf,hfs,hfr⟩ := Wide.finish_eval c ht
  have hcongr := Wide.finish_congr (Wide.project c) (middle a p w tail) hcs
  refine ⟨tc+(Wide.finishCost (Wide.project c)+1),b,?_,hc.seq hf,hfs.trans hcongr.1,?_⟩
  · unfold budget
    rw [hcongr.2]
    omega
  · intro i hi
    exact (hfr i hi).trans (hcr i hi)

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
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

/-- This certificate checks the actual producer, interpolation, denominator
and packing instruction tables, including every peek. -/
theorem command_avoids : ProgramTapeReplay.AvoidsCmd LeafProgram.OuterCarried.hidden command :=
  ⟨PackingCallerProgram.Replay.command_avoids,
    ⟨⟨LeafRingSetupProgram.Replay.producerWideCall_avoids,
      LeafRingSetupProgram.Interpolation.Replay.command_avoids⟩,
      LayoutDenominatorProgramQuery.command_avoids⟩⟩

/-- Semantic facts for one concrete native preparation run. -/
structure FrontExecution (q : LeafQueryFrontend.Query) (k : ℕ)
    (hg : Guard (q.input k)) (front : Data) (l : Fin 8 → ℕ)
    (data : FrontData q k hg l) : Prop where
  rows : (data.first :: data.rest).map Subexp.ReadPlan.encodeWord =
    Subexp.AssignmentAlphabetSemantics.wordBytes (packingProblem q k hg).r
      (packingProblem q k hg).Q
  nodup : (data.first :: data.rest).Nodup
  complete : ∀ z, z ∈ data.first :: data.rest
  packing : Eval PackingCallerProgram.command data.packingSteps front data.packed
  packed_words : data.packed.stacks =
    (PackingCallerProgram.result front (packingProblem q k hg) data.first data.rest).stacks
  arithmetic : Eval arithmeticCommand data.arithmeticSteps data.packed data.output
  arithmetic_output : ArithmeticOutput data.packed data.output
    (Execute.guardedModel (q.input k) l) (ring_degree_pos (q.input k) l hg)
    data.modulus data.cache data.half data.ringState
  degree : data.output.stacks 204 =
    List.replicate ((Execute.guardedModel (q.input k) l).val 34) true
  inverse :
    (RingProgram.modelRing ((Execute.guardedModel (q.input k) l).val 33)
      (ring_precision_pos (q.input k) l hg) (ring_degree_pos (q.input k) l hg)
      (IrreducibleSearch.data (ring_degree_pos (q.input k) l hg))
      data.modulus data.cache).decode
      (LayoutDenominatorProgramQuery.value ((Execute.guardedModel (q.input k) l).val 33)
        (IrreducibleSearch.data (ring_degree_pos (q.input k) l hg))
        data.modulus data.cache data.half (data.packed.stacks 740).length) *
      (2 : (IrreducibleSearch.data (ring_degree_pos (q.input k) l hg)).O
        ((Execute.guardedModel (q.input k) l).val 33)) ^
        ((data.packed.stacks 740).length - 1) = 1
  command : Eval command (data.packingSteps + data.arithmeticSteps) front data.output

/-- Time and all-prefix space facts for one concrete native preparation run. -/
structure FrontBounds (front : Data) (S B cost : ℕ)
    {q : LeafQueryFrontend.Query} {k : ℕ} {hg : Guard (q.input k)}
    {l : Fin 8 → ℕ} (data : FrontData q k hg l) : Prop where
  time : data.packingSteps + data.arithmeticSteps ≤ cost
  output_space : ∀ i, (data.output.stacks i).length ≤ max cost B
  trace : Trace (compiled command 700 728) (data.packingSteps + data.arithmeticSteps + 1)
    (front.withPC (some (compiled command 700 728).entry)) (data.output.withPC none)
  prefix_space : ∀ j c, j ≤ data.packingSteps + data.arithmeticSteps + 1 →
    Trace (compiled command 700 728) j
      (front.withPC (some (compiled command 700 728).entry)) c →
    ∀ i, (c.stacks i).length ≤ max cost B

/-- A concrete preparation output paired with its semantic and resource certificates. -/
def FrontRun (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k))
    (front : Data) (l : Fin 8 → ℕ) (S B cost : ℕ) : Type :=
  { data : FrontData q k hg l //
    FrontExecution q k hg front l data ∧ FrontBounds front S B cost data }

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowExecution
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed nested source emitter and its actual byte-level execution bound. -/
namespace SubexponentialSAT.Subexp.UniversalRowProgram

open BitProgram StructuredCalls
open SubexpKernelControl (Word Accumulator pushWord operator operators emit bump
  state counterWord setCounter counterPort popTag unframe emitFramedLiteral emitLiteral
  emitOperator countOne drain scan scanCost)

def termCost (one x : Word) (t : Term Word) : ℕ :=
  7 * t.value.length + 7 * t.inverseNode.length + 8 * x.length +
    productCost one x t.factors + 30

def termUpdate (one x : Word) (t : Term Word) (a : Accumulator) : Accumulator :=
  bump 2 (emit (termCode one x t) a)

def rowCost (zero one x : Word) (r : Row Word) : ℕ :=
  7 * r.delta.length + scanCost encodeTerm (termCost one x) r.terms +
    8 * zero.length + 5 * r.terms.length + 23

def commandCost (zero one : Word) (r : Row Word) : ℕ :=
  rowCost zero one (zero ++ one) r + 9 * (zero.length + one.length) +
    3 * (rowCode zero one (zero ++ one) r).length + 18

end SubexponentialSAT.Subexp.UniversalRowProgram

end OAI.Algorithms
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

structure PreparedExecution (q : LeafQueryFrontend.Query) (k : ℕ)
    (hg : Guard (q.input k)) (front : Data) (padding : Fin 8 → ℕ)
    (data : PreparedData q k hg padding) : Prop where
  rows : (data.first :: data.rest).map Subexp.ReadPlan.encodeWord =
    Subexp.AssignmentAlphabetSemantics.wordBytes (preparedProblem q k hg).r
      (preparedProblem q k hg).Q
  nodup : (data.first :: data.rest).Nodup
  complete : ∀ z, z ∈ data.first :: data.rest
  packing : Eval PackingCallerProgram.command data.packingSteps (project front) data.packed
  packed_words : data.packed.stacks =
    (PackingCallerProgram.result (project front) (preparedProblem q k hg)
      data.first data.rest).stacks
  arithmetic : Eval NativeQueryPreparation.arithmeticCommand data.arithmeticSteps
    data.packed data.output
  arithmetic_output : ArithmeticOutput data.packed data.output (preparedModel q k padding)
    (ring_degree_pos (q.input k) padding hg) data.modulus data.cache data.half data.ringState
  degree : data.output.stacks 204 =
    List.replicate ((preparedModel q k padding).val 34) true
  inverse : inverseLaw q k hg padding data.packed data.modulus data.cache data.half
  preparation : Eval HighQueryProgram.prepare
    (data.packingSteps + data.arithmeticSteps + 1) front (preparedOutput front data.output)
  seed : Eval HighQueryProgram.seed data.seedSteps (preparedOutput front data.output)
    (seededOutput front data.output data.seedRegs)

structure PreparedResources (q : LeafQueryFrontend.Query) (k : ℕ)
    (hg : Guard (q.input k)) (front : Data) (padding : Fin 8 → ℕ)
    (S B cost : ℕ) (data : PreparedData q k hg padding) : Prop where
  preparation_time : data.packingSteps + data.arithmeticSteps ≤ cost
  seed_time : data.seedSteps ≤ 110 * localBound S cost + 80
  guard : front.regs 8 = true
  mask : (preparedOutput front data.output).stacks 338 =
    LeafQueryFrontend.highMask q.scopeRows (BinaryArithmetic.toNat q.ambient)
  counter : (seededOutput front data.output data.seedRegs).stacks 789 =
    Encoding.encodeList id (List.replicate (highSet q).card [false])
  cleared : ∀ i ∈ ([788,790,323,791,792] : List (Fin 896)),
    (seededOutput front data.output data.seedRegs).stacks i = []
  high_guard : (seededOutput front data.output data.seedRegs).regs 21 = true
  kept : ∀ i, HashMarkedReturn.kept i = true →
    (seededOutput front data.output data.seedRegs).stacks i = front.stacks i
  boundary : ∀ i, ((seededOutput front data.output data.seedRegs).stacks i).length ≤
    boundaryBound q S cost B
  preparation_space : StageSpace HighQueryProgram.prepare
    (data.packingSteps + data.arithmeticSteps + 1) front (prefixBound q S cost B)
  seed_space : StageSpace HighQueryProgram.seed data.seedSteps (preparedOutput front data.output)
    (prefixBound q S cost B)
  prefix_space : StageSpace (.seq HighQueryProgram.prepare HighQueryProgram.seed)
    (data.packingSteps + data.arithmeticSteps + 1 + data.seedSteps + 1) front
    (prefixBound q S cost B)

/-- A factual output bundle for the fixed preparation and seed instructions.
All semantic objects and resource assertions refer to these same evaluations. -/
def PreparedRun (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k))
    (front : Data) (padding : Fin 8 → ℕ) (S B cost : ℕ) : Type :=
  { data : PreparedData q k hg padding //
    PreparedExecution q k hg front padding data ∧
      PreparedResources q k hg front padding S B cost data }

namespace PreparedRun

variable {q : LeafQueryFrontend.Query} {k : ℕ} {hg : Guard (q.input k)}
  {front : Data} {padding : Fin 8 → ℕ} {S B cost : ℕ}

abbrev data (run : PreparedRun q k hg front padding S B cost) := run.1
abbrev execution (run : PreparedRun q k hg front padding S B cost) := run.2.1
abbrev resources (run : PreparedRun q k hg front padding S B cost) := run.2.2

abbrev first (run : PreparedRun q k hg front padding S B cost) := run.data.first
abbrev rest (run : PreparedRun q k hg front padding S B cost) := run.data.rest
abbrev packed (run : PreparedRun q k hg front padding S B cost) := run.data.packed
abbrev packingSteps (run : PreparedRun q k hg front padding S B cost) := run.data.packingSteps
abbrev arithmeticSteps (run : PreparedRun q k hg front padding S B cost) :=
  run.data.arithmeticSteps
abbrev ringState (run : PreparedRun q k hg front padding S B cost) := run.data.ringState
abbrev modulus (run : PreparedRun q k hg front padding S B cost) := run.data.modulus
abbrev cache (run : PreparedRun q k hg front padding S B cost) := run.data.cache
abbrev half (run : PreparedRun q k hg front padding S B cost) := run.data.half
abbrev output (run : PreparedRun q k hg front padding S B cost) := run.data.output
abbrev seedSteps (run : PreparedRun q k hg front padding S B cost) := run.data.seedSteps
abbrev seedRegs (run : PreparedRun q k hg front padding S B cost) := run.data.seedRegs

abbrev nodup (run : PreparedRun q k hg front padding S B cost) := run.execution.nodup
abbrev complete (run : PreparedRun q k hg front padding S B cost) := run.execution.complete
abbrev packed_words (run : PreparedRun q k hg front padding S B cost) :=
  run.execution.packed_words
abbrev arithmetic_output (run : PreparedRun q k hg front padding S B cost) :=
  run.execution.arithmetic_output
abbrev degree (run : PreparedRun q k hg front padding S B cost) := run.execution.degree
abbrev preparation (run : PreparedRun q k hg front padding S B cost) :=
  run.execution.preparation
abbrev seed (run : PreparedRun q k hg front padding S B cost) := run.execution.seed

abbrev preparation_time (run : PreparedRun q k hg front padding S B cost) :=
  run.resources.preparation_time
abbrev seed_time (run : PreparedRun q k hg front padding S B cost) := run.resources.seed_time
abbrev guard (run : PreparedRun q k hg front padding S B cost) := run.resources.guard
abbrev mask (run : PreparedRun q k hg front padding S B cost) := run.resources.mask
abbrev counter (run : PreparedRun q k hg front padding S B cost) := run.resources.counter
abbrev cleared (run : PreparedRun q k hg front padding S B cost) := run.resources.cleared
abbrev high_guard (run : PreparedRun q k hg front padding S B cost) :=
  run.resources.high_guard
abbrev kept (run : PreparedRun q k hg front padding S B cost) := run.resources.kept
abbrev preparation_space (run : PreparedRun q k hg front padding S B cost) :=
  run.resources.preparation_space
abbrev seed_space (run : PreparedRun q k hg front padding S B cost) :=
  run.resources.seed_space
abbrev prefix_space (run : PreparedRun q k hg front padding S B cost) :=
  run.resources.prefix_space

end PreparedRun

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeHashQuerySetup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual prepared selector boundary supplies the literal marked and
history-only frontend, packing, arithmetic and high-counter initialization.
The common bound is unchanged. Suspended caller words have a separate bound
which never occurs in the measured setup time. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup

open BitProgram StructuredCalls SqrtLog DisjointReuse LeafParametersProgram
open HashGreedyCode HashQueryEntry HighFrontendSources NativeQueryInputBounds
open HighMarkedFrontend HighQuerySetup ProducedQueryResources
open HashGreedyProgram.NativeRound

local notation "H" => (fun i : Fin 896 => i ∈ HighQueryProgram.Carried.words)

/-- Concrete frontend and preparation data for one setup run. A standard
dependent pair avoids generating a large custom recursor. -/
def SetupData (q : LeafQueryFrontend.Query) (k : ℕ) (frontBudget S B Cp dp : ℕ) : Type :=
  PSigma fun guard : Guard (q.input k) =>
    Σ _frontendSteps : ℕ, Σ front : Data, Σ padding : Fin 8 → ℕ, Σ _words : Bank.Words,
      PreparedRun q k guard front padding (S + frontBudget) B
        (Cp * (S + frontBudget + 1) ^ dp)

namespace SetupData

variable {q : LeafQueryFrontend.Query} {k frontBudget S B Cp dp : ℕ}

abbrev guard (data : SetupData q k frontBudget S B Cp dp) := data.fst
abbrev frontendSteps (data : SetupData q k frontBudget S B Cp dp) := data.snd.fst
abbrev front (data : SetupData q k frontBudget S B Cp dp) := data.snd.snd.fst
abbrev padding (data : SetupData q k frontBudget S B Cp dp) := data.snd.snd.snd.fst
abbrev words (data : SetupData q k frontBudget S B Cp dp) := data.snd.snd.snd.snd.fst
abbrev prepared (data : SetupData q k frontBudget S B Cp dp) :=
  data.snd.snd.snd.snd.snd

end SetupData

/-- Execution and resource facts referring to one concrete setup datum. -/
structure SetupFacts (q : LeafQueryFrontend.Query) (k : ℕ) (input : Data)
    (frontCommand : Cmd 40 896) (markerInput : State 40 768)
    (frontBudget S B Cp dp timeCap spaceCap : ℕ)
    (data : SetupData q k frontBudget S B Cp dp) : Prop where
  input_visible : ∀ i, ¬H i → (input.stacks i).length ≤ S
  frontend : Eval frontCommand data.frontendSteps input data.front
  frontend_time : data.frontendSteps + 1 ≤ frontBudget
  frontend_state : LeafProgram.Query.FrontState q k markerInput
    (project data.front) data.padding data.words
  eval : Eval (.seq frontCommand (.seq HighQueryProgram.prepare HighQueryProgram.seed))
    (data.frontendSteps + (data.prepared.packingSteps + data.prepared.arithmeticSteps + 1 +
      data.prepared.seedSteps)) input
    (HighCountSeed.initialized (result data.front data.prepared.output) data.prepared.seedRegs)
  time : data.frontendSteps +
    (data.prepared.packingSteps + data.prepared.arithmeticSteps + 1 +
      data.prepared.seedSteps) ≤ timeCap
  kept : ∀ i, HashMarkedReturn.kept i = true →
    (HighCountSeed.initialized (result data.front data.prepared.output)
      data.prepared.seedRegs).stacks i = input.stacks i
  space : StageSpace (.seq frontCommand (.seq HighQueryProgram.prepare HighQueryProgram.seed))
    (data.frontendSteps + (data.prepared.packingSteps + data.prepared.arithmeticSteps + 1 +
      data.prepared.seedSteps) + 1) input (max spaceCap B)

/-- A factual bundle of the same executed frontend and constructed setup.
The command and marker input are instantiated by the two concrete theorems. -/
def SetupRun (q : LeafQueryFrontend.Query) (k : ℕ) (input : Data)
    (frontCommand : Cmd 40 896) (markerInput : State 40 768)
    (frontBudget S B Cp dp timeCap spaceCap : ℕ) : Type :=
  { data : SetupData q k frontBudget S B Cp dp //
    SetupFacts q k input frontCommand markerInput frontBudget S B Cp dp timeCap spaceCap data }

namespace SetupRun

variable {q : LeafQueryFrontend.Query} {k : ℕ} {input : Data}
  {frontCommand : Cmd 40 896} {markerInput : State 40 768}
  {frontBudget S B Cp dp timeCap spaceCap : ℕ}

abbrev data (run : SetupRun q k input frontCommand markerInput frontBudget S B Cp dp
    timeCap spaceCap) := run.1
abbrev facts (run : SetupRun q k input frontCommand markerInput frontBudget S B Cp dp
    timeCap spaceCap) := run.2
abbrev guard (run : SetupRun q k input frontCommand markerInput frontBudget S B Cp dp
    timeCap spaceCap) := run.data.guard
abbrev frontendSteps (run : SetupRun q k input frontCommand markerInput frontBudget S B Cp dp
    timeCap spaceCap) := run.data.frontendSteps
abbrev front (run : SetupRun q k input frontCommand markerInput frontBudget S B Cp dp
    timeCap spaceCap) := run.data.front
abbrev padding (run : SetupRun q k input frontCommand markerInput frontBudget S B Cp dp
    timeCap spaceCap) := run.data.padding
abbrev words (run : SetupRun q k input frontCommand markerInput frontBudget S B Cp dp
    timeCap spaceCap) := run.data.words
abbrev prepared (run : SetupRun q k input frontCommand markerInput frontBudget S B Cp dp
    timeCap spaceCap) := run.data.prepared
abbrev input_visible (run : SetupRun q k input frontCommand markerInput frontBudget S B Cp dp
    timeCap spaceCap) := run.facts.input_visible
abbrev frontend (run : SetupRun q k input frontCommand markerInput frontBudget S B Cp dp
    timeCap spaceCap) := run.facts.frontend
abbrev frontend_time (run : SetupRun q k input frontCommand markerInput frontBudget S B Cp dp
    timeCap spaceCap) := run.facts.frontend_time
abbrev frontend_state (run : SetupRun q k input frontCommand markerInput frontBudget S B Cp dp
    timeCap spaceCap) := run.facts.frontend_state
abbrev eval (run : SetupRun q k input frontCommand markerInput frontBudget S B Cp dp
    timeCap spaceCap) := run.facts.eval
abbrev kept (run : SetupRun q k input frontCommand markerInput frontBudget S B Cp dp
    timeCap spaceCap) := run.facts.kept
abbrev space (run : SetupRun q k input frontCommand markerInput frontBudget S B Cp dp
    timeCap spaceCap) := run.facts.space

end SetupRun

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryCountReconstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The coefficients emitted by the actual ordered node loop determine the
same fixed-length Hermite inputs consumed by the native reconstruction tail.
No canonical choice of coefficient bytes across node states is required. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryCountReconstruction

open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog SubexpLiftRing SubexpQuarticRing
open Polynomial DensePolynomialProgram LeafProgram LeafParametersProgram

theorem field_of_model (q : LeafQueryFrontend.Query) (k : ℕ)
    (lengths : Fin 8 → ℕ) (hg : Guard (q.input k)) (m : Circuit.Model)
    (hm : m = PreparedSource.numeric q k lengths) :
    (produce (q.input k)).Q < 3^(m.val 34) := by
  rw [hm]
  exact PreparedSource.numeric_field q k lengths hg

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryCountReconstruction
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

/-- The exact restricted full-signature fiber contributed by one head. -/
def fiberValue {r Q n d : ℕ} (q : Factor.Spec r Q n d) (u : ℕ)
    (node : Fin Q) (H E U : Finset (Fin n)) (high : H → Bool)
    (owner : Fin q.ps.length → Fin n) (head : Fin Q → Fin n → Fin r)
    (g : Fin r)
    (reps : ∀ k, Moments.Head (fun v : ResidualEmbedding.Free H => head node v.val) k → Bool)
    (ids : List ℕ) : Dense (q.p.model.O q.p.t) u q.J :=
  ∑ x : Moments.Head (fun v : ResidualEmbedding.Free H => head node v.val) g → Bool,
    if HeadSourceLocality.freeLabel q.p q.ps q.packing owner head H node g x =
        HeadSourceLocality.freeLabel q.p q.ps q.packing owner head H node g (reps g) ∧
        (∀ v, v.val.val ∈ E → x v = true) then
      QueryEvaluation.specializeDense u q.J
        (fun v : ResidualEmbedding.Free H => decide (v.val ∈ U))
        (HeadSourceLocality.sourceProduct q H high
          (HeadSourceLocality.stateFor H high
            (Moments.assemble (fun v : ResidualEmbedding.Free H => head node v.val)
              (Function.update reps g x))) ids) else 0

/-- The produced ring precision is the retained marker cutoff. -/
def headValue {r Q n d : ℕ} (q : Factor.Spec r Q n d)
    (node : Fin Q) (H E U : Finset (Fin n)) (high : H → Bool)
    (owner : Fin q.ps.length → Fin n) (head : Fin Q → Fin n → Fin r)
    (g : Fin r)
    (reps : ∀ k, Moments.Head (fun v : ResidualEmbedding.Free H => head node v.val) k → Bool)
    (ids : List ℕ) : Dense (q.p.model.O q.p.t) q.p.t q.J :=
  fiberValue q q.p.t node H E U high owner head g reps ids

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead
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

/-- Additive readout is applied after the completed product of actual
restricted full-signature head sums. -/
def emittedValue (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d)
    (H E U : Finset (Fin s.input.n)) (high : H → Bool)
    (owner : Fin q.ps.length → Fin s.input.n)
    (head : Fin s.input.Q → Fin s.input.n → Fin s.input.r)
    (facts : QueryVisitorHead.SourceFacts s.input q H owner s.owner head)
    (ancestors : Prefix (Representatives s.key) s.input.r) : Truncated (q.p.model.O q.p.t) q.J :=
  Dense.readout (∏ g : Fin s.input.r,
    QueryVisitorHead.headValue q s.input.node H E U high owner head g
      (emittedRepresentatives s q H owner head facts ancestors) (QueryVisitorHead.factorIds s.input g))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun
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

/-- The complete attained-tuple value for the actual emitted free supports. -/
noncomputable def pairValue (s : ProducedSource) {d : ℕ}
    (q : Factor.Spec s.input.r s.input.Q s.input.n d)
    (H : Finset (Fin s.input.n)) (high : H → Bool)
    (owner : Fin q.ps.length → Fin s.input.n)
    (head : Fin s.input.Q → Fin s.input.n → Fin s.input.r)
    (facts : QueryVisitorHead.SourceFacts s.input q H owner s.owner head)
    (E U : Finset (Fin (s.input.n-H.card))) : Truncated (q.p.model.O q.p.t) q.J :=
  SignatureTupleRun.tupleTotal s.key s.input.r (SignatureTupleRun.emittedValue s q H
    (E.image (fun i => (HighIncidenceProgram.freeOrder H i).val))
    (U.image (fun i => (HighIncidenceProgram.freeOrder H i).val)) high owner head facts)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation
end


