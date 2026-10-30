-- Prove2me | Definitions.Def_OAIQ081S107
-- name    : OAIQ081S107
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:23:26.955242+00:00
-- url     : https://prove2.me/theorems/cc3666d3-6428-494c-87bc-c7791f42317e
-- title:
--   Definitions bundle OAIQ081S107 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 49 declarations of OpenAI's Lean: 32 definitions, 1 inductive type or structure and 16 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.lookupBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutUniversal.data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafBranchProgram.Ports`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.FetchClean`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.Finished`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.Stable`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.TestClean`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.bumped`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.cleared`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.fetched`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.finishedStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.input`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs.lookupTime`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs.metadata`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs.size`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafPackingFiberBounds.freeOwner`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsSemantics.factorCodeEquiv`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsSemantics.nativeScope`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsSemantics.neutralOwnerEquiv`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.WideData`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryRank.addressPair`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryRank.owner`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryRank.packing`, `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowMismatchProgram.command`, `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowMismatchProgram.program`, `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowMismatchProgram.rangeCall`, `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowMismatchTypes.command`, `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowMismatchTypes.filter`, `OAI.Algorithms.SubexponentialSAT.SubexpUnaryRangeProgram.command`, `OAI.Algorithms.SubexponentialSAT.SubexpUnaryRangeProgram.emitCurrent`, `OAI.Algorithms.SubexponentialSAT.SubexpUnaryRangeProgram.loop`, `OAI.Algorithms.SubexponentialSAT.SubexpUnaryRangeProgram.program`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_LayoutProgramSourceBankRun`, `SubexponentialSAT_SqrtLog_LayoutUniversal`, `SubexponentialSAT_SqrtLog_LeafBranchProgram`, `SubexponentialSAT_SqrtLog_LeafFactorDispatchProgram`, `SubexponentialSAT_SqrtLog_LeafFactorDispatchProgramBranches`, `SubexponentialSAT_SqrtLog_LeafFactorDispatchProgramChoose`, `SubexponentialSAT_SqrtLog_LeafFactorDispatchProgramFetch`, `SubexponentialSAT_SqrtLog_LeafFactorDispatchProgramRun`, `SubexponentialSAT_SqrtLog_LeafFactorDispatchProgramTest`, `SubexponentialSAT_SqrtLog_LeafHeadSetupProgramNativeInputs`, `SubexponentialSAT_SqrtLog_LeafPackingFiberBounds`, `SubexponentialSAT_SqrtLog_LeafStatisticsSemanticsFactor`, `SubexponentialSAT_SqrtLog_LeafStatisticsSemanticsTransport`, `SubexponentialSAT_SqrtLog_MomentsReadoutProgramState`, `SubexponentialSAT_SqrtLog_ProducedQueryRankInventory`, `SubexponentialSAT_SqrtLog_ProducedQueryRankProvenance`, `SubexponentialSAT_SubexpUnaryRangeProgram`, `SubexponentialSAT_SubexpVertexIndexProgram`, `SubexponentialSAT_Subexp_DimensionProgram`, `SubexponentialSAT_Subexp_UniversalRowMismatchProgram`, `SubexponentialSAT_Subexp_UniversalRowMismatchTypes`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S082`, `OAIQ081S084`, `OAIQ081S085`, `OAIQ081S088`, `OAIQ081S089`, `OAIQ081S090`, `OAIQ081S091` and `OAIQ081S092` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S125`, `OAIQ081S127`, `OAIQ081S130` and `OAIQ081S136`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedMatrix.literalHead_rank`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.paddedConstraint_cover`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.paddedConstraint_shape`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.dispatch_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.hashBranch_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.markedBranch_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryRank.packing_coverage` and `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowMismatchTypes.filter_eval`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank.actualRank_sum_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedMatrix.literalHead_rank`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.paddedConstraint_cover`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.paddedConstraint_shape`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.dispatch_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.hashBranch_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.markedBranch_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryRank.packing_coverage` and `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowMismatchTypes.filter_eval`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S082
import Definitions.Def_OAIQ081S084
import Definitions.Def_OAIQ081S085
import Definitions.Def_OAIQ081S088
import Definitions.Def_OAIQ081S089
import Definitions.Def_OAIQ081S090
import Definitions.Def_OAIQ081S091
import Definitions.Def_OAIQ081S092

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpUnaryRangeProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed unary range enumerator which physically emits every framed index. -/
namespace SubexponentialSAT.SubexpUnaryRangeProgram

open BitProgram StructuredCalls SubexpIncidencePlanPrimitives

abbrev emitCurrent : Cmd 10 10 := .seq (copy 5 1 3) (.seq setSelected (.seq emit (increment 5)))

abbrev loop : Cmd 10 10 := .while 9 (.seq pop (.seq emitCurrent peek))
abbrev command : Cmd 10 10 := .seq peek loop

abbrev program : Program 10 10 (size command + 1) := compiled command 5 7

end SubexponentialSAT.SubexpUnaryRangeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_DimensionProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed generator for all unary dimensions from zero through a runtime bound

The input bound is a unary stack, and the output is a framed list of unary
payloads. The program has no bound-dependent control labels.
-/

namespace SubexponentialSAT.Subexp.DimensionProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.TupleProgram

theorem emitCurrent_eval (k : ℕ) (remaining : List Bool) (accum : Records)
    (a : State 5 5) (ha : Ready k remaining accum a) :
    ∃ b, Ready k remaining (List.replicate k true :: accum) b ∧
      b.regs 0 = a.regs 0 ∧ b.regs 1 = a.regs 1 ∧ Eval emitCurrent (12 * k + 12) a b := by
  rcases ha with ⟨h0,h1,h2,h3,h4⟩
  let b := pushedState 3 2 false a
  let c : State 5 5 :=
    ⟨readRegs b.regs 2 3 none, StackRoutines.copyStacks 1 2 b.stacks⟩
  let d := escapedState emitPorts c
  let e := pushedState 3 2 true d
  have t1 := pushConst_eval 3 2 false a
  have t2 := copy_eval 1 2 4 2 3 (by decide) (by decide) (by decide) (by decide) b
    (by simpa [b, pushedState] using h4)
  have t3 := escape_eval_state emitPorts c
  have t4 := pushConst_eval 3 2 true d
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · simp [Ready, e,d,c,b, emitPorts, StackRoutines.copyStacks,
      h0,h1,h2,h3,h4,ProgramEncoding.encodeRecords,Encoding.encodeList,
      frame_eq_escaped,List.append_assoc]
  · simp [e,d,c,b,emitPorts,readRegs]
  · simp [e,d,c,b,emitPorts,readRegs]
  · convert t1.seq (t2.seq (t3.seq t4)) using 1 ;
      simp [b,c,StackRoutines.copyStacks,emitPorts,h1,h2] ; omega

theorem enumerate_eval (k : ℕ) (remaining : List Bool) (accum : Records)
    (a : State 5 5) (ha : Ready k remaining accum a) :
    ∃ b, Ready (k + remaining.length) [] (earlierRows k remaining.length ++ accum) b ∧
      b.regs 1 = false ∧ Eval enumerate (loopCost k remaining.length) a b := by
  induction remaining generalizing k accum a with
  | nil =>
      let b := readCounterState a
      have hb : Ready k [] accum b := by
        rcases ha with ⟨h0,h1,h2,h3,h4⟩
        simp [Ready,b,readCounterState,h0,h1,h2,h3,h4]
      have hr : b.regs 1 = false := by simp [b,readCounterState,readRegs,ha.1]
      refine ⟨b, by simpa [earlierRows] using hb, hr, ?_⟩
      exact (readCounter_eval a).seq (Eval.while_false hr)
  | cons bit remaining ih =>
      let b := readCounterState a
      have hb : Ready k remaining accum b := by
        rcases ha with ⟨h0,h1,h2,h3,h4⟩
        simp [Ready,b,readCounterState,h0,h1,h2,h3,h4]
      have hr : b.regs 1 = true := by simp [b,readCounterState,readRegs,ha.1]
      obtain ⟨c,hc,hc0,hc1,he⟩ := emitCurrent_eval k remaining accum b hb
      let d := pushedState 1 2 true c
      have hd : Ready (k + 1) remaining (List.replicate k true :: accum) d := by
        rcases hc with ⟨h0,h1,h2,h3,h4⟩
        simp [Ready,d,h0,h1,h2,h3,h4,List.replicate_succ]
      obtain ⟨e,hs,hr',ht⟩ := ih (k + 1) (List.replicate k true :: accum) d hd
      refine ⟨e, ?_, hr', ?_⟩
      · simpa [earlierRows,List.append_assoc,Nat.add_assoc,Nat.add_left_comm,
          Nat.add_comm] using hs
      · generalize hsteps : loopCost (k + 1) remaining.length = steps at ht
        cases ht with
        | @seq first second n m x y z hp hl =>
            have h := (readCounter_eval a).seq
              (Eval.while_true hr (he.seq ((pushConst_eval 1 2 true c).seq hp)) hl)
            convert h using 1 ; simp only [loopCost,List.length_cons] ; omega

end SubexponentialSAT.Subexp.DimensionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpVertexIndexProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed generator for exactly the vertex indices below unary D. -/
namespace SubexponentialSAT.SubexpVertexIndexProgram

open BitProgram StructuredCalls

theorem command_eval (D : ℕ) (a : State 5 5)
    (h0 : a.stacks 0 = unary D) (h1 : a.stacks 1 = []) (h2 : a.stacks 2 = [])
    (h3 : a.stacks 3 = []) (h4 : a.stacks 4 = []) :
    ∃ b, Eval command (6*D^2+10*D+4) a b ∧
      Subexp.DimensionProgram.Ready D [] ((List.range' 0 D).reverse.map unary) b := by
  let c := Subexp.TupleProgram.pushedState 3 2 false a
  have hc : Subexp.DimensionProgram.Ready 0 (unary D) [] c := by
    simp [Subexp.DimensionProgram.Ready,c,
      h0,h1,h2,h3,h4,ProgramEncoding.encodeRecords,Encoding.encodeList]
  obtain ⟨b,hb,_,he⟩ := Subexp.DimensionProgram.enumerate_eval 0 (unary D) [] c hc
  have h := (Subexp.TupleProgram.pushConst_eval 3 2 false a).seq he
  refine ⟨b,?_,?_⟩
  · convert h using 1
    all_goals try with_reducible_and_instances rfl
    simp [Subexp.DimensionProgram.loopCost_eq]
    ring
  · simpa [earlierRows_eq] using hb

theorem program_trace (D : ℕ) (a : State 5 5)
    (h0 : a.stacks 0 = unary D) (h1 : a.stacks 1 = []) (h2 : a.stacks 2 = [])
    (h3 : a.stacks 3 = []) (h4 : a.stacks 4 = []) :
    ∃ b, Trace program (6*D^2+10*D+5) (a.withPC (some program.entry)) (b.withPC none) ∧
      Subexp.DimensionProgram.Ready D [] ((List.range' 0 D).reverse.map unary) b := by
  obtain ⟨b,he,hb⟩ := command_eval D a h0 h1 h2 h3 h4
  exact ⟨b,by simpa [Nat.add_assoc] using compiled_halt_trace he 0 3,hb⟩

end SubexponentialSAT.SubexpVertexIndexProgram

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
open MismatchPlanProgram (indexRecords )

abbrev rangeCall : Cmd 10 17 := .call (ProgramLinking.liftProgram
  SubexpUnaryRangeProgram.program id rangeMap)

abbrev command : Cmd 10 17 :=
  .seq (.call (copyProgram 16 6 15 (0 : Fin 10) 1))
    (.seq initializeSource (.seq rangeCall (.seq (.call (clearProgram 5 (0 : Fin 10) 1)) filterCall)))

abbrev program : Program 10 17 (size command + 1) := compiled command 16 14

end SubexponentialSAT.Subexp.UniversalRowMismatchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowMismatchTypes
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Read the two relevant words from the complete types, generate their
mismatch positions, and restore the temporary extracted words. -/

namespace SubexponentialSAT.Subexp.UniversalRowMismatchTypes

open BitProgram StructuredCalls StackRoutines MulticolorTypes

abbrev filter : Cmd 10 49 := .call (ProgramLinking.liftProgram
  UniversalRowMismatchProgram.program id filterStacks)

abbrev command : Cmd 10 49 := .seq extract (.seq filter clearRows)

end SubexponentialSAT.Subexp.UniversalRowMismatchTypes

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBankRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Complete packed source dispatch from actual metadata. All possible
branches execute native commands and return an exact typed compiler source. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.Subexp.ConstructivePacking IntegerRingLiftProgram RowSelectionProgram

variable {r Q d D : ℕ}

def lookupBudget (P : PackingData (Fin D) (UniversalType r Q 1)) (row col : Fin D) : ℕ :=
  400*(GlobalBasisMetadata.volume (metadataRecords P) (List.replicate row.val true))^2+
  400*(GlobalBasisMetadata.volume (metadataRecords P) (List.replicate col.val true))^2+1

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutUniversal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual universal incidence-copy block over a commutative coefficient
ring in which the power-of-two denominator is a unit. -/

namespace SubexponentialSAT.SqrtLog.LayoutUniversal

open scoped BigOperators
open Matrix
open SubexponentialSAT.MulticolorTypes
open LayoutPullback LayoutExactBuckets LayoutScaledMatrices

variable {r Q : ℕ} {O : Type*} [CommRing O]

/-- Every row, constraint, origin and degree in this block is the concrete
universal swap construction; no abstract locality hypothesis is an input. -/
noncomputable def data {node : Fin Q → O} (A R : ℕ) (denom : Oˣ)
    (hdenom : (denom : O) = (LayoutNumerator.denominator R : O))
    (units : SubexponentialSAT.SubexpRowInterpolation.NodeUnits node) :
    Layout.Data (O := O) (G := Fin r) (id : U r Q → U r Q)
      (id : U r Q → U r Q) Q R :=
  Layout.ofIndexed node units (fun t u => u.head t) (fun u => u.slot 0)
    (fun a => sourceRow (LayoutNumerator.family r Q 1 A R) denom a 0 R units)
    (by
      intro a y
      have h := congrFun (sourceRow_origin (LayoutNumerator.family r Q 1 A R)
        denom a 0 R units) y
      simpa [Pi.single_apply, eq_comm] using h)
    (fun a y => sourceRow_degree (LayoutNumerator.family r Q 1 A R)
      denom a 0 R units y)
    (fun t g => Joint t g (0 : Fin 1)) (constraints A R)
    (fun t a g hg => locality A R denom hdenom units a t g hg)

end SubexponentialSAT.SqrtLog.LayoutUniversal

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafBranchProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The branch callback is a real residual-count program followed by the native
binary adder. Semantic branch counts occur only in its verification contract. -/
namespace SubexponentialSAT.SqrtLog.LeafBranchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.ExecCNFTupleEnumeration

structure Ports (R S : ℕ) where
  counter : CounterForPrograms.Ports R S
  mass : SqrtLog.LeafProgram.Mass.Ports R S
  disjoint_counter : ∀ i, mass.stack i ≠ counter.counter
  disjoint_scratch : ∀ i, mass.stack i ≠ counter.scratch

end SubexponentialSAT.SqrtLog.LeafBranchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafFactorDispatchProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid factor classification and source lookup. IDs are runtime data. -/
namespace SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def cleared (d : Data) (src : Fin 16) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks src []⟩

def Stable (d e : Data) : Prop := ∀ i : Fin 8, 4 ≤ i.val → e.regs i = d.regs i

end SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafFactorDispatchProgramFetch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The selected payload is fetched by scanning the actual source record list. -/
namespace SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def fetched (d : Data) (flag : Bool) (bits : List Bool) : Data :=
  ⟨Function.update (Function.update (Function.update d.regs 0 false) 1 false) 2 flag,
    Function.update (Function.update d.stacks 6 []) 15 bits⟩

end SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafFactorDispatchProgramTest
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def bumped (d : Data) (extra : Bool) : Data :=
  ⟨Function.update d.regs 0 true,
    Function.update d.stacks 9 (unary (if extra then 2 else 1) ++ d.stacks 9)⟩

end SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafFactorDispatchProgramBranches
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def marked (d : Data) (isHash isMarked : Bool) : Data :=
  ⟨Function.update (Function.update d.regs 5 isHash) 6 isMarked,d.stacks⟩

def finishedStacks (d : Data) (bits : List Bool) : Fin 16 → List Bool :=
  Function.update (Function.update d.stacks 6 []) 15 bits

def Finished (d e : Data) (isHash isMarked : Bool) (bits : List Bool) : Prop :=
  e.stacks=finishedStacks d bits ∧ e.regs 5=isHash ∧ e.regs 6=isMarked ∧ e.regs 7=d.regs 7

def FetchClean (d : Data) : Prop :=
  ∀ j ∈ ([10,11,12,15] : List (Fin 16)), d.stacks j=[]

end SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafFactorDispatchProgramChoose
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def TestClean (d : Data) : Prop := d.stacks 8=[] ∧ d.stacks 9=[] ∧ d.stacks 14=[]

end SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafFactorDispatchProgramRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native dispatcher: reverse the incoming ID, classify it, and scan
only the selected source. No selected payload is supplied as an input. -/
namespace SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def input (regs : Fin 8 → Bool) (rows clauses : List (List Bool))
    (hasMarked : Bool) (m f : ℕ) : Data :=
  ⟨Function.update regs 7 hasMarked,baseStacks rows clauses m f⟩

end SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramNativeInputs
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime source facts for the closed head setup. No cache output, matrix,
entry evaluator, or running-time witness is supplied in this interface. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.Subexp.ConstructivePacking RowSelectionProgram

def Inputs.metadata (s : Inputs) : List Bool :=
  SelectorProgram.rawRecords (LayoutProgram.EntryBank.metadataRecords s.packing)
def Inputs.size (s : Inputs) : ℕ :=
  s.n+s.D+s.metadata.length+(LayoutOwnerFiberProgram.stream s.plans).length+
    s.R*s.width.length+s.width.length+s.R+s.height.length+s.r+s.Q+s.Q*s.r+1

def Inputs.lookupTime (s : Inputs) : ℕ := 800*(s.metadata.length+s.D+1)^2+1

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsSemanticsFactor
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The exact native neutral ID is the rank of its uncovered original owner.
This is an explicit indexing equivalence, not just equality of cardinalities. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

open PackingIncidenceInput LeafStatisticsProgram HighIncidence

def neutralOwnerEquiv (scopes : List (List ℕ)) (mask : List Bool) :
    Fin (neutralOwners scopes 0 mask).length ≃ uncovered (residualScope scopes mask) where
  toFun := neutralAt scopes mask
  invFun := neutralIndex scopes mask
  left_inv j := by
    apply Fin.ext
    change (neutralOwners scopes 0 mask).idxOf ((neutralOwners scopes 0 mask).get j) = j.val
    simpa only [List.get_eq_getElem] using
      (neutralOwners_nodup scopes 0 mask).idxOf_getElem j.val j.isLt
  right_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    apply Fin.ext
    change (neutralOwners scopes 0 mask).get (neutralIndex scopes mask v) = v.val.val.val
    exact List.getElem_idxOf (neutralIndex scopes mask v).isLt

/-- Encode a semantic factor by its actual native ID: original IDs are retained,
and an uncovered owner gets `q + idxOf owner` in the forward owner list. -/
def factorCodeEquiv (scopes : List (List ℕ)) (mask : List Bool) :
    (Fin scopes.length ⊕ uncovered (residualScope scopes mask)) ≃
      Fin (Semantics.factorCount scopes mask) :=
  ((Equiv.sumCongr (Equiv.refl _) (neutralOwnerEquiv scopes mask).symm).trans
    finSumFinEquiv).trans (finCongr (factorCount_eq scopes mask).symm)

@[simp] theorem factorCode_original_value (scopes : List (List ℕ)) (mask : List Bool)
    (e : Fin scopes.length) :
    (factorCodeEquiv scopes mask (Sum.inl e)).val = e.val := rfl

@[simp] theorem factorCode_neutral_value (scopes : List (List ℕ)) (mask : List Bool)
    (v : uncovered (residualScope scopes mask)) :
    (factorCodeEquiv scopes mask (Sum.inr v)).val =
      scopes.length + (neutralOwners scopes 0 mask).idxOf v.val.val.val := rfl

end SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsSemanticsTransport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Scope transport for the actual native factor IDs. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

open PackingIncidenceInput HighIncidence

/-- Read the scope from exactly the emitted `(original owner, native factor)`
records, retaining the original free-coordinate subtype. -/
def nativeScope (scopes : List (List ℕ)) (mask : List Bool)
    (e : Fin (Semantics.factorCount scopes mask)) : Finset (Free mask) :=
  Finset.univ.filter fun v => (v.val.val,e.val) ∈ Semantics.nativeEntries scopes mask

@[simp] theorem mem_nativeScope (scopes : List (List ℕ)) (mask : List Bool)
    (e : Fin (Semantics.factorCount scopes mask)) (v : Free mask) :
    v ∈ nativeScope scopes mask e ↔
      (v.val.val,e.val) ∈ Semantics.nativeEntries scopes mask := by
  simp [nativeScope]

theorem nativeScope_original (scopes : List (List ℕ)) (mask : List Bool)
    (e : Fin scopes.length) :
    nativeScope scopes mask (factorCodeEquiv scopes mask (Sum.inl e)) =
      residualScope scopes mask e := by
  ext v
  rw [mem_nativeScope, factorCode_original_value]
  change (v.val.val,e.val) ∈ Semantics.entries scopes 0 scopes.length mask ↔ _
  rw [native_original_mem scopes mask 0 scopes.length v.val.val e.val le_rfl e.isLt]
  rw [and_iff_right (free_mem_lowOwners mask v), residual_mem]
  exact Subexp.IncidencePlanSpec.mem_incidentIndices scopes v.val.val e

theorem nativeScope_neutral (scopes : List (List ℕ)) (mask : List Bool)
    (w : uncovered (residualScope scopes mask)) :
    nativeScope scopes mask (factorCodeEquiv scopes mask (Sum.inr w)) = {w.val} := by
  ext v
  rw [mem_nativeScope, factorCode_neutral_value]
  change (v.val.val,scopes.length + (neutralOwners scopes 0 mask).idxOf w.val.val.val) ∈
      Semantics.entries scopes 0 scopes.length mask ↔ v ∈ ({w.val} : Finset (Free mask))
  rw [native_neutral_mem scopes mask 0 scopes.length _ _ le_rfl (Nat.le_add_right _ _)]
  simp only [Finset.mem_singleton]
  constructor
  · rintro ⟨i, hi, he⟩
    have hei : i = neutralIndex scopes mask w := by
      apply Fin.ext
      change i.val = (neutralOwners scopes 0 mask).idxOf w.val.val.val
      omega
    subst i
    have hw := congrArg (fun u : uncovered (residualScope scopes mask) => u.val.val.val)
      ((neutralOwnerEquiv scopes mask).apply_symm_apply w)
    change (neutralOwners scopes 0 mask).get (neutralIndex scopes mask w) = w.val.val.val at hw
    apply Subtype.ext
    apply Fin.ext
    exact hi.symm.trans hw
  · intro hv
    subst v
    refine ⟨neutralIndex scopes mask w, ?_, rfl⟩
    have hw := congrArg (fun u : uncovered (residualScope scopes mask) => u.val.val.val)
      ((neutralOwnerEquiv scopes mask).apply_symm_apply w)
    exact hw

end SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafPackingFiberBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Raw native incidence records have no repeated owner-factor pair. Hence their
index fibers are bounded by the statistics of the actual completed scopes. -/
namespace SubexponentialSAT.SqrtLog.LeafPackingFiberBounds
open PackingIncidenceInput LeafStatisticsSemantics LeafStatisticsProgram

 theorem nativeEntries_nodup (scopes : List (List ℕ)) (mask : List Bool) :
    (Semantics.nativeEntries scopes mask).Nodup := entries_nodup scopes mask 0 scopes.length

 theorem native_get_injective (scopes : List (List ℕ)) (mask : List Bool) :
    Function.Injective (Semantics.nativeEntries scopes mask).get :=
  List.nodup_iff_injective_get.mp (nativeEntries_nodup scopes mask)

 theorem owner_low (scopes : List (List ℕ)) (mask : List Bool)
    (i : Semantics.Incidences scopes mask) :
    ((Semantics.nativeEntries scopes mask).get i).1 ∈ lowOwners 0 mask :=
  entries_owner_low scopes mask 0 scopes.length _ _ (List.get_mem _ i)

 def freeOwner (scopes : List (List ℕ)) (mask : List Bool)
    (i : Semantics.Incidences scopes mask) : Free mask :=
  ⟨⟨((Semantics.nativeEntries scopes mask).get i).1,
    by have h := (lowOwners_bounds 0 _ mask (owner_low scopes mask i)).2; omega⟩,
    by
      obtain ⟨j,hj,hb⟩ := (lowOwners_mem 0 _ mask).mp (owner_low scopes mask i)
      have he : j = ⟨((Semantics.nativeEntries scopes mask).get i).1,
        by have h := (lowOwners_bounds 0 _ mask (owner_low scopes mask i)).2; omega⟩ :=
        Fin.ext (by simpa using hj)
      simp only [mem_highMask]
      rw [← he,hb]
      decide⟩

 theorem freeOwner_mem (scopes : List (List ℕ)) (mask : List Bool) (n : ℕ)
    (hm : mask.length ≤ n) (i : Semantics.Incidences scopes mask) :
    freeOwner scopes mask i ∈ nativeScope scopes mask (Semantics.factor scopes n mask hm i) := by
  rw [mem_nativeScope]
  exact List.get_mem _ i

 theorem free_pair_injective (scopes : List (List ℕ)) (mask : List Bool) (n : ℕ)
    (hm : mask.length ≤ n) (i j : Semantics.Incidences scopes mask)
    (ho : freeOwner scopes mask i = freeOwner scopes mask j)
    (hf : Semantics.factor scopes n mask hm i = Semantics.factor scopes n mask hm j) : i=j := by
  apply native_get_injective scopes mask
  apply Prod.ext
  · exact congrArg (fun v : Free mask => v.val.val) ho
  · exact congrArg Fin.val hf

end SubexponentialSAT.SqrtLog.LeafPackingFiberBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsReadoutProgramState
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed forty-stack workspace for the two runtime readout counters. -/
namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev WideData := State 8 40

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram


/-! Actual stack construction of the sparse key (u,z,empty support), followed
by the paid query cleanup and unary-index increment. -/


/-! One concrete (u,z) coefficient fetch, addition, and index advance. -/


/-! The U loop is driven by a real unary stack. Every visit invokes the
concrete key builder and dictionary scan; no callback is left abstract. -/


/-! Seed one Z accumulator from the cached zero vector and append the
completed coefficient to the output, paying for every copy and reversal. -/


/-! Runtime Z enumeration. Completed fixed-width coefficients are prepended
in reverse and are restored once by the final output transfer. -/


/-! Build the all-false support mask from the actual ambient shape stack.
The loop length is the ambient number of variables, including unused ones. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ProducedQueryRankProvenance
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The rank certificate refers to the packing and word table actually
produced by the native packing caller, with its original incidence order. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.ProducedQueryRank
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open PackingCallerProgram

abbrev packing (p : Problem) (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) :
    PackingData (Fin p.incidences) (UniversalType p.r p.Q 1) :=
  (Problem.spec_dimension p a tail) ▸ (p.spec a tail).suffix.packing

abbrev owner (p : Problem) :=
  PackingIncidenceInput.Semantics.owner p.scopes p.n p.mask p.mask_le

end SubexponentialSAT.SqrtLog.ProducedQueryRank

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ProducedQueryRankInventory
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The literal native incidence list and the actual produced head tables
share the same matrix rank bound, in their emitted order. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.ProducedQueryRank
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open PackingCallerProgram LeafParametersProgram BucketProgram.ProducedRank
open LeafHeadSetupProgram

def addressPair (p : Problem) (i : Fin p.incidences) : ℕ × ℕ :=
  (PackingIncidenceInput.Semantics.nativeEntries p.scopes p.mask).get i

@[simp] theorem addressPair_owner (p : Problem) (i : Fin p.incidences) :
    (addressPair p i).1=(owner p i).val := rfl

 theorem addressPairs_eq (p : Problem) :
    List.ofFn (addressPair p)=PackingIncidenceInput.Semantics.nativeEntries p.scopes p.mask :=
  List.ofFn_get _

end SubexponentialSAT.SqrtLog.ProducedQueryRank

end

end OAI.Algorithms
end


