-- Prove2me | Definitions.Def_OAIQ081S111
-- name    : OAIQ081S111
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:26:46.438907+00:00
-- url     : https://prove2.me/theorems/46f188c3-6343-45b4-8e6f-5cb92dd67b6c
-- title:
--   Definitions bundle OAIQ081S111 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 48 declarations of OpenAI's Lean: 25 definitions, 2 inductive types or structures and 21 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds.Cap`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds.scalarSize`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Parameters`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.lowClearPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramPrefix.state`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceProgram.Install.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceProgram.Install.generate`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingLoaderProgram.finishBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingLoaderProgram.parameterBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Assembly.controllerCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingWeightProgram.Gate.choose`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingWeightProgram.Gate.clear`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingWeightProgram.Gate.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingWeightProgram.Gate.compare`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingWeightProgram.Gate.convert`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingWeightProgram.Gate.copy`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.resetCandidateFlags`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentPairFrontend.moved`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairPreparationProgram.callback`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairPreparationProgram.command`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairPreparationProgram.program`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairPreparationProgram.selectorCall`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairScoreProgram.ValidPair`, `OAI.Algorithms.SubexponentialSAT.Subexp.ScoreBuilderProgram.preparation`, `OAI.Algorithms.SubexponentialSAT.Subexp.SelectorPairProgram.command`, `OAI.Algorithms.SubexponentialSAT.Subexp.SelectorPairProgram.mapProgram`, `OAI.Algorithms.SubexponentialSAT.Subexp.SelectorPairProgram.program`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram`, `SubexponentialSAT_SqrtLog_PackingCallerProgramBasic`, `SubexponentialSAT_SqrtLog_PackingCallerProgramBoundsBasic`, `SubexponentialSAT_SqrtLog_PackingCallerProgramModel`, `SubexponentialSAT_SqrtLog_PackingCallerProgramReplay`, `SubexponentialSAT_SqrtLog_PackingHeadProgramPrefix`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputEmit`, `SubexponentialSAT_SqrtLog_PackingIncidenceProgramInstall`, `SubexponentialSAT_SqrtLog_PackingIncidenceProgramPairs`, `SubexponentialSAT_SqrtLog_PackingLoaderProgramFinish`, `SubexponentialSAT_SqrtLog_PackingLoaderProgramFrame`, `SubexponentialSAT_SqrtLog_PackingLoaderProgramParameters`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyController`, `SubexponentialSAT_SqrtLog_PackingWeightProgramGate`, `SubexponentialSAT_SqrtLog_PackingWeightProgramGateBasic`, `SubexponentialSAT_SubexpNormalizeProgram`, `SubexponentialSAT_SubexpPlanAlphabetEmit`, `SubexponentialSAT_SubexpScopeMembershipProgram`, `SubexponentialSAT_Subexp_AssignmentPairFrontend`, `SubexponentialSAT_Subexp_CandidateScoreRefinement`, `SubexponentialSAT_Subexp_PairPreparationBounds`, `SubexponentialSAT_Subexp_PairPreparationProgram`, `SubexponentialSAT_Subexp_PairScoreProgram`, `SubexponentialSAT_Subexp_ScoreBuilderProgram`, `SubexponentialSAT_Subexp_SelectorPairProgram`, `SubexponentialSAT_Subexp_SequentialStep`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S082`, `OAIQ081S084`, `OAIQ081S088`, `OAIQ081S089`, `OAIQ081S093`, `OAIQ081S095` and `OAIQ081S096` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S131`, `OAIQ081S132`, `OAIQ081S133`, `OAIQ081S134`, `OAIQ081S135` and `OAIQ081S136`; the proofs of `OAI.Algorithms.SubexponentialSAT.ExecCoreChildProgram.program_runsIn`, `OAI.Algorithms.SubexponentialSAT.ExecPetalChildProgram.command_eval`, `OAI.Algorithms.SubexponentialSAT.ExecPetalChildProgram.familyCall_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram.programB_runsIn`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal.readyCommand_bounded`, `OAI.Algorithms.SubexponentialSAT.SubexpNormalizationProgram.absorb_eval`, `OAI.Algorithms.SubexponentialSAT.SubexpNormalizationProgram.prefixCall_eval`, `OAI.Algorithms.SubexponentialSAT.SubexpNormalizationProgram.program_runsIn`, `OAI.Algorithms.SubexponentialSAT.SubexpNormalizationProgram.removeSupersetsCall_eval`, `OAI.Algorithms.SubexponentialSAT.SubexpScopeProducer.command_eval` and `OAI.Algorithms.SubexponentialSAT.SubexpTautologyFilterProgram.filter_eval`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S082
import Definitions.Def_OAIQ081S084
import Definitions.Def_OAIQ081S088
import Definitions.Def_OAIQ081S089
import Definitions.Def_OAIQ081S093
import Definitions.Def_OAIQ081S095
import Definitions.Def_OAIQ081S096

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete components of the sharp clause/core search from Appendix A.
The guard counts actual framed literals and executes the preserving subset tester.
The complete search and its polynomial resource bound are developed separately below. -/


namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls

namespace Selector

def resetCandidateFlags : Code := .seq (atom (.set 21 false)) (atom (.set 22 true))

end Selector

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNormalizeProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Concrete syntax routines for CNF normalization

This module begins the machine implementation of normalization with the
complement-query operation used in tautology testing. `negateProgram` is one
fixed finite instruction table. It scans a unary literal code in pairs and
emits the code with its polarity flipped. Unbounded data stays on the stacks.

The theorems count actual `BitProgram.step` transitions. Full formula
deduplication, tautology filtering, and absorption are separate obligations;
this routine is not presented as the completed normalization algorithm.
-/

namespace SubexponentialSAT.SubexpNormalizeProgram

open BitProgram
open ParserProgram (cfg)

/-! ## Actual record-filter output step

The predicate's result occupies register 2. The following fixed callback
consumes the reversed record on stack 3, prepends its framed representation to
stack 2 exactly when selected, and resets the iterator's flags. Its two other
stacks are preserved. Computing the selection bit is a separate operation.
-/

theorem emitIfSelected_trace (selected : Bool)
    (bits source work output : List Bool) (v p : Bool) :
    Trace emitIfSelectedProgram (emitIfSelectedSteps selected bits + 1)
      ((filterState v p selected source work output bits.reverse).withPC
        (some emitIfSelectedProgram.entry))
      ((filterState false true false source work
        (if selected then true :: (Encoding.frame bits ++ output) else output) []).withPC none) :=
  StructuredCalls.compiled_halt_trace
    (emitIfSelected_eval selected bits source work output v p) 3 2

/-! ## A complete record-order reversal pass

Prepending accepted records reverses their order. This second, unconditional
pass restores the order required by `List.filter` and the executable
sparsifier. It reverses the records, never the bits within a record.
-/

/-! ## Exact-order contract for the full normalization filter

The selection callback in the following theorem is a fixed structured
program with measured executions. No procedure is manufactured from the
mathematical predicate. Once that callback is supplied, the theorem tracks
the output of the actual generic record iterator, including record order.
-/

end SubexponentialSAT.SubexpNormalizeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpPlanAlphabetEmit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical double framing for one vertex-plan alphabet entry. -/
namespace SubexponentialSAT.SubexpPlanAlphabetEmit

open BitProgram StructuredCalls Subexp.TupleProgram

/-- Consume a plan word and prepend a record whose payload is its frame.
Consequently two such payloads concatenate to a pair of framed plans. -/
theorem command_eval (regs : Fin 3 → Bool) (bits out : List Bool) :
    ∃ rf, Eval command (24*bits.length+26) (data regs bits [] out)
      (data rf [] [] (true::Encoding.frame (Encoding.frame bits)++out)) ∧ rf 2 = regs 2 := by
  let a := data regs bits [] out
  let a1 := transferred a
  let a2 := pushedState 0 0 false a1
  let a3 := escapedState innerPorts a2
  let a4 := transferred a3
  let a5 := pushedState 2 0 false a4
  let a6 := escapedState outerPorts a5
  let a7 := pushedState 2 0 true a6
  have h1 := transfer_eval a
  have h2 := pushConst_eval 0 0 false a1
  have h3 := escape_eval_state innerPorts a2
  have h4 := transfer_eval a3
  have h5 := pushConst_eval 2 0 false a4
  have h6 := escape_eval_state outerPorts a5
  have h7 := pushConst_eval 2 0 true a6
  have hinner : a3.stacks 0 = Encoding.frame bits := by
    simp [a3,innerPorts,a2,a1,transferred,
      StackRoutines.transferStacks,a,data,frame_eq_escaped]
  have hempty : a3.stacks 1 = [] := by
    simp [a3,innerPorts]
  have he : a7 = data a7.regs [] [] (true::Encoding.frame (Encoding.frame bits)++out) := by
    apply congrArg (StructuredProgram.State.mk a7.regs)
    funext i
    fin_cases i <;>
      simp [a6,outerPorts,a5,a4,transferred,
        StackRoutines.transferStacks,a3,innerPorts,a2,a1,a,data,
        frame_eq_escaped,List.append_assoc]
  have h := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq h7)))))
  change Eval command _ a a7 at h
  rw [he] at h
  simp only [innerPorts,outerPorts] at h
  have hcost : (3*(a.stacks 0).length+3) +
      (2+((5*(a2.stacks 1).length+3)+
        ((3*(a3.stacks 0).length+3)+(2+((5*(a5.stacks 1).length+3)+2))))) =
      24*bits.length+26 := by
    simp [a5,a4,transferred,StackRoutines.transferStacks,hinner,hempty,
      a2,a1,a,data,Encoding.length_frame]
    omega
  refine ⟨a7.regs,?_,?_⟩
  · rw [hcost] at h
    exact h
  · simp [a7,a6,outerPorts,a5,a4,transferred,
      a3,innerPorts,a2,a1,a,data,readRegs]

theorem program_trace (regs : Fin 3 → Bool) (bits out : List Bool) :
    ∃ rf, Trace program (24*bits.length+27)
      ((data regs bits [] out).withPC (some program.entry))
      ((data rf [] [] (true::Encoding.frame (Encoding.frame bits)++out)).withPC none) := by
  obtain ⟨rf,h,_⟩ := command_eval regs bits out
  exact ⟨rf,by simpa [Nat.add_assoc] using compiled_halt_trace h 0 2⟩

end SubexponentialSAT.SubexpPlanAlphabetEmit

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputEmit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed writer for one double-framed two-address incidence plan. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Emit
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem frame_eval (d : Data) (ht : d.stacks 2 = []) :
    ∃ rf, Eval frame (24*(d.stacks 3).length+27) d (framed d rf (d.stacks 3)) := by
  obtain ⟨rf, h⟩ := SubexpPlanAlphabetEmit.program_trace d.regs (d.stacks 3) (d.stacks 5)
  have ha : embedState id framePorts d
      (SubexpPlanAlphabetEmit.data d.regs (d.stacks 3) [] (d.stacks 5)) = d := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id framePorts_injective
    · intros; rfl
    · intros; rfl
    · intro i; fin_cases i <;> simp [framePorts, SubexpPlanAlphabetEmit.data, ht]
    · intros; rfl
  have hb : embedState id framePorts d
      (SubexpPlanAlphabetEmit.data rf [] []
        (true :: Encoding.frame (Encoding.frame (d.stacks 3)) ++ d.stacks 5)) =
      framed d rf (d.stacks 3) := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id framePorts_injective
    · intros; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [framePorts, SubexpPlanAlphabetEmit.data, framed]
    · intro i hi
      have h2 : i ≠ 2 := fun h => hi ⟨1,h.symm⟩
      have h3 : i ≠ 3 := fun h => hi ⟨0,h.symm⟩
      have h5 : i ≠ 5 := fun h => hi ⟨2,h.symm⟩
      simp [framed, h2, h3, h5]
  have he := eval_call_lifted SubexpPlanAlphabetEmit.program id framePorts d
    Function.injective_id framePorts_injective h
  exact ⟨rf, by simpa only [ha, hb] using he⟩

theorem command_eval (r : Fin 3 → Bool) (h f : ℕ) (out : List Bool) :
    ∃ rf, Eval command (60*(h+f)+173)
      (data r (unary h) (unary f) [] [] [] out)
      (data rf (unary h) (unary f) [] [] []
        (true :: Encoding.frame (Encoding.frame (plan h f)) ++ out)) := by
  let a := data r (unary h) (unary f) [] [] [] out
  let b := TupleProgram.pushedState 3 0 false a
  let c := copied 1 b
  let d := recorded c (unary f)
  let e := copied 0 d
  let g := recorded e (unary h)
  have h1 := TupleProgram.pushConst_eval (3 : Fin 6) (0 : Fin 3) false a
  have h2 := copy_eval 1 (by decide) (by decide) b (by simp [b,a,data])
  have h3 := record_eval c (unary f) (by simp [c,copied,b,a,data,StackRoutines.copyStacks])
  have h4 := copy_eval 0 (by decide) (by decide) d (by simp [d,recorded,c,copied,b,a,data,StackRoutines.copyStacks])
  have h5 := record_eval e (unary h) (by simp [e,copied,d,recorded,c,copied,b,a,data,StackRoutines.copyStacks])
  obtain ⟨rf,h6⟩ := frame_eval g (by simp [g,recorded])
  have hp : g.stacks 3 = plan h f := by
    simp [g,recorded,e,copied,d,c,b,a,data,StackRoutines.copyStacks,
      plan,CollisionStreamProgram.planBytes,ProgramEncoding.encodeRecords,
      Encoding.encodeList, GatherProgram.indexRecords ]
  have he : framed g rf (g.stacks 3) =
      data rf (unary h) (unary f) [] [] []
        (true :: Encoding.frame (Encoding.frame (plan h f)) ++ out) := by
    apply congrArg (StructuredProgram.State.mk rf)
    funext i; fin_cases i <;>
      simp [g,recorded,e,copied,d,c,b,a,data,
        StackRoutines.copyStacks,plan,CollisionStreamProgram.planBytes,
        ProgramEncoding.encodeRecords,Encoding.encodeList,GatherProgram.indexRecords]
  have hc : (plan h f).length = 2*(h+f)+5 := by
    simp [plan,CollisionStreamProgram.planBytes,ProgramEncoding.encodeRecords,
      Encoding.encodeList,Encoding.length_frame,GatherProgram.indexRecords]
    omega
  have hh := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6))))
  rw [he] at hh
  refine ⟨rf, ?_⟩
  convert hh using 1 ;
    simp [c,copied,b,a,data,StackRoutines.copyStacks,
      d,recorded,hp,hc] ; ring
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Emit

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PairScoreProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Aggregating the actual collision streams of all vertex pairs

The fixed program consumes framed pairs of already selected read plans.
Producing those selected plans from original plans and the remaining-index
table is a separate preparation step.  Every pair invokes the actual tuple
generator and collision machine; a final fixed unary tally produces the score.
-/

namespace SubexponentialSAT.Subexp.PairScoreProgram

open BitProgram StackRoutines StructuredCalls

def ValidPair (ctx : Context) (pair : PlanPair) : Prop :=
  (∀ i ∈ pair.1, i < ctx.current.length + ctx.depth.length) ∧
    (∀ i ∈ pair.2, i < ctx.current.length + ctx.depth.length)

theorem pairStream_length (ctx : Context) (pair : PlanPair) (stream : List Bool) :
    (pairStream ctx pair stream).length =
      ctx.alphabet.length ^ ctx.depth.length + stream.length := by
  simp [pairStream, CollisionTupleProgram.streamed_length, TupleProgram.generated_count]

end SubexponentialSAT.Subexp.PairScoreProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_SelectorPairProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!+# Selecting and framing both read plans of a vertex pair

The two selector-map calls share a persistent table. Stack 6 initially holds
the left query records and stack 9 the right query records. Stack 11 is an
existing record accumulator. The result prepends one record whose payload is
`frame leftPlanBytes ++ frame rightPlanBytes`.
-/

namespace SubexponentialSAT.Subexp.SelectorPairProgram

open BitProgram StructuredCalls

abbrev mapProgram : Program 8 12 (size SelectorMapProgram.command + 1) :=
  ProgramLinking.liftProgram SelectorMapProgram.program id stackMap

abbrev command : Cmd 8 12 :=
  .seq (.call mapProgram) (.seq prepareRight (.seq (.call mapProgram) framePair))

abbrev program : Program 8 12 (size command + 1) := compiled command 6 11

end SubexponentialSAT.Subexp.SelectorPairProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PairPreparationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Preparing all selected pair plans once per assignment step

The fixed program preserves the full seed-index records, original pair
records, seed count, and processed counter. It computes the next cutoff,
builds each pair's actual selection table, and emits selected pair records.
The candidate value is not an input to this preparation phase.
-/

namespace SubexponentialSAT.Subexp.PairPreparationProgram

open BitProgram StructuredCalls StackRoutines

abbrev selectorCall : Cmd 16 34 :=
  .call (ProgramLinking.liftProgram SelectorPairProgram.program selectorRegs selectorStacks)

/-- Each operation below is a fixed instruction table or a fixed finite
composition. In particular, the selection table is actually generated. -/
def callback : Cmd 16 34 := sequence [
  PairPlanPreparation.parsePair,
  PairPlanPreparation.buildUnion,
  copy 30 5,
  activeCall,
  clear 6,
  move 11 0,
  copy 32 2,
  resetTable,
  tableCall,
  clear 2,
  PairPlanPreparation.reverseQueries,
  selectorCall,
  clear 3,
  resetInner]

/-- Inputs: 30 seed-index records, 31 raw pair records, 32 unary seed count,
33 unary processed count. Output: 29 selected pair records in input order.
Every source is copied before it is scanned or changed. -/
abbrev command : Cmd 16 34 := sequence [
  copy 31 20,
  copy 33 7,
  TupleProgram.pushConst 7 0 true,
  TupleProgram.pushConst 29 0 false,
  resetAll,
  RecordPrograms.iterate ports callback,
  clear 7,
  TupleProgram.pushConst 28 0 false,
  reverseCall,
  move 28 29,
  resetAll]

abbrev program : Program 16 34 (size command + 1) := compiled command 31 29

end SubexponentialSAT.Subexp.PairPreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PairPreparationBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Uniform polynomial bounds for the actual once-per-step pair preparation
program. The common parameter bounds physical input lengths and record count. -/

namespace SubexponentialSAT.Subexp.PairPreparationBounds

open BitProgram PairPreparationProgram

theorem planBytes_le (plan : List ℕ) (W : ℕ) (h : ∀ n ∈ plan, n ≤ W) :
    (CollisionStreamProgram.planBytes plan).length ≤ 1 + (2 * W + 2) * plan.length := by
  rw [planBytes_eq]
  have he := ProgramEncoding.encodeRecords_length_le (plan.map SelectionTableProgram.unary) W (by
    intro bytes hbytes
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hbytes
    simpa [SelectionTableProgram.unary] using h n hn)
  simpa only [List.length_map] using he

end SubexponentialSAT.Subexp.PairPreparationBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_ScoreBuilderProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# The actual global candidate-score builder

Pair read plans are prepared once for the current processed position. The
candidate loop then executes the local collision enumeration and emits scores
in candidate order. A final fixed routine restores the temporary table ports.
-/

namespace SubexponentialSAT.Subexp.ScoreBuilderProgram

open BitProgram StructuredCalls

abbrev preparation : Cmd 16 48 := .call
  (ProgramLinking.liftProgram PairPreparationProgram.program id preparationPorts)

end SubexponentialSAT.Subexp.ScoreBuilderProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_CandidateScoreRefinement
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Candidate-array and generated-score refinement

The concrete temporary array has the same values as the search decoder after
one candidate is prepended. Generated collision streams may be permuted;
their successful-leaf counts still equal the exact natural evaluator.
-/

namespace SubexponentialSAT.Subexp.CandidateScoreRefinement

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SlotAssignment

/-- Depth-two tuple generation on framed vertex plans produces exactly the
pair payload expected by PairScoreProgram, retaining every multiplicity. -/
theorem generated_pair_payloads (plans : List (List ℕ)) :
    (TupleProgram.powerRows
      (plans.map (fun p => Encoding.frame (CollisionStreamProgram.planBytes p))) 2 [[]]).Perm
      ((plans.product plans).map PairScoreProgram.pairBytes) := by
  have h := SubexpTupleRefinement.powerRows_empty_perm
    (plans.map (fun p => Encoding.frame (CollisionStreamProgram.planBytes p))) 2
  apply h.trans
  apply List.Perm.of_eq
  simp [QuarticSearch.vectors, SubexpTupleRefinement.tuplePayload_cons,
    SubexpTupleRefinement.tuplePayload_zero, PairScoreProgram.pairBytes,
    List.product, List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def,
    ← List.map_eq_flatMap]

theorem generated_pair_payloads_decode (plans : List (List ℕ)) :
    ((TupleProgram.powerRows
      (plans.map (fun p => Encoding.frame (CollisionStreamProgram.planBytes p))) 2 [[]]).map
        PairScoreProgram.readPair).Perm (plans.product plans) := by
  have h := (generated_pair_payloads plans).map PairScoreProgram.readPair
  simpa [List.map_map, Function.comp_def] using h

end SubexponentialSAT.Subexp.CandidateScoreRefinement

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_SequentialStep
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete composition of score selection and packed assignment update. -/

namespace SubexponentialSAT.Subexp.SequentialProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem stepRefines_of_scoreBuilder {A : Type*} (encode : A → List Bool) (a : A)
    (tail : List A) (evaluate : ℕ → List A → ℕ)
    (builder : Cmd 16 48) (scoreCost S total : ℕ)
    (environment : Fin 48 → List Bool)
    (hwidth : ∀ x, (encode x).length = (encode a).length)
    (hscore : ∀ n fixed x, n + 1 + fixed.length ≤ total → x ∈ a :: tail →
      evaluate n (x :: fixed) ≤ S)
    (hbuilder : ScoreBuilderRefines encode a tail evaluate builder scoreCost total environment) :
    StepRefines encode a tail evaluate builder
      (scoreCost + selectionBudget (a :: tail).length S total (encode a).length) total environment := by
  intro n fixed d hsize hm hcounter hcontext
  obtain ⟨t, ht, prepared, hp, hs, hf, hprepared⟩ := hbuilder n fixed d hsize hm hcounter hcontext
  obtain ⟨m, hmb, e, he, hmem, hc, hhigh⟩ := selectAndUpdate_eval encode a tail hwidth
    (fun x => evaluate n (x :: fixed)) S total n fixed
    (fun x hx => hscore n fixed x hsize.le hx) (by omega) d prepared hm hs hf
  refine ⟨t + m, by omega, e, hp.seq he, hmem, ?_, ?_⟩
  · rw [hc]
    exact hcounter
  · intro j hj
    rw [hhigh j hj]
    exact hprepared j hj

end SubexponentialSAT.Subexp.SequentialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceProgramPairs
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual depth-two tuple program builds all raw incidence-pair records.
Its input has one two-address record per incidence, not a quadratic table. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.Subexp

theorem planAlphabet_width (M : ℕ) (plans : List (List ℕ))
    (hlen : ∀ p ∈ plans, p.length ≤ 2) (hindex : ∀ p ∈ plans, ∀ i ∈ p, i < M) :
    ∀ row ∈ planAlphabet plans, row.length ≤ 8*M+11 := by
  intro row hrow
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hrow
  have h := PairPreparationBounds.planBytes_le p M (fun i hi => (hindex p hp i hi).le)
  have hlen' := hlen p hp
  simp only [Encoding.length_frame]
  nlinarith

theorem rawPairProgram_cost (M : ℕ) (plans : List (List ℕ)) (hne : plans ≠ [])
    (hlen : ∀ p ∈ plans, p.length ≤ 2) (hindex : ∀ p ∈ plans, ∀ i ∈ p, i < M) :
    TupleProgram.powerCost (planAlphabet plans) 2 [[]] + 9 ≤
      2400 * plans.length^2 * (24*M+34) + 9 := by
  have hq : 1 ≤ (planAlphabet plans).length := by
    have hpos : 0 < (planAlphabet plans).length := by
      simpa only [planAlphabet, List.length_map] using List.length_pos_iff.mpr hne
    omega
  have h := PairScoreBounds.generated_powerCost_le (planAlphabet plans) 2 (8*M+11)
    hq (planAlphabet_width M plans hlen hindex)
  calc
    _ ≤ 800*(2+1)*(planAlphabet plans).length^2*((2+1)*(8*M+11)+1)+9 :=
      Nat.add_le_add_right h 9
    _ = _ := by simp only [planAlphabet, List.length_map]; ring

end SubexponentialSAT.SqrtLog.PackingIncidenceProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpScopeMembershipProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A concrete scope-membership subroutine for incidence-plan preparation.
The reversed scope record occupies stack 8 and the reversed query stack 2.
Stacks 0,1,3,4 are empty work ports; all remaining stacks are framed.
-/
namespace SubexponentialSAT.SubexpScopeMembershipProgram

open BitProgram StructuredCalls

theorem member_eval (query : List Bool) (records : List (List Bool)) (d : Data)
    (h0 : d.stacks 0 = Encoding.encodeList id records)
    (h1 : d.stacks 1 = []) (h2 : d.stacks 2 = query.reverse)
    (h3 : d.stacks 3 = []) (h4 : d.stacks 4 = []) :
    ∃ (n : ℕ) (e : Data),
      Eval member n d e ∧
      n ≤ (20 * query.length + 30) * (Encoding.encodeList id records).length + 3 ∧
      e.regs 4 = decide (query ∈ records) ∧
      (e.stacks 0).length ≤ (Encoding.encodeList id records).length ∧
      e.stacks 1 = [decide (query ∈ records)] ∧ e.stacks 2 = d.stacks 2 ∧
      e.stacks 3 = [] ∧ e.stacks 4 = [] ∧
      (∀ i : Fin 10, 5 ≤ i.val → e.stacks i = d.stacks i) ∧
      (∀ i : Fin 10, 7 ≤ i.val → e.regs i = d.regs i) := by
  obtain ⟨n, hn, b, he, hflag, hsource, hout, hquery, hcopy, htmp,
      hframe0, hframe2, hframe7, hreg7, hreg8, hreg9⟩ :=
    ExecCNFSubset.memberCall_eval query records (restrict d) h0 h2 h1 h3 h4
  have ht := StructuredCalls.compiled_halt_trace he 3 4
  have hl := eval_call_lifted (StructuredCalls.compiled ExecCNFSubset.memberCall 3 4)
    id stackMap d Function.injective_id stackMap_injective ht
  rw [embed_restrict] at hl
  let e := embedState id stackMap d b
  have hstack (i : Fin 8) : e.stacks (stackMap i) = b.stacks i :=
    embedState_stack id stackMap d b stackMap_injective i
  have hreg (i : Fin 10) : e.regs i = b.regs i :=
    embedState_register id stackMap d b Function.injective_id i
  refine ⟨n + 1, e, hl, by omega, (hreg 4).trans hflag, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← show stackMap (3 : Fin 8) = 0 by decide, hstack 3]
    exact hsource
  · exact (hstack 4).trans hout
  · exact (hstack 1).trans (hquery.trans h2.symm)
  · exact (hstack 5).trans hcopy
  · exact (hstack 6).trans htmp
  · intro i hi
    fin_cases i
    · simp at hi
    · simp at hi
    · simp at hi
    · simp at hi
    · simp at hi
    · exact (hstack 0).trans hframe0
    · exact (hstack 2).trans hframe2
    · exact (hstack 7).trans hframe7
    · exact embedState_stack_frame id stackMap d b 8 (by decide)
    · exact embedState_stack_frame id stackMap d b 9 (by decide)
  · intro i hi
    fin_cases i
    · simp at hi
    · simp at hi
    · simp at hi
    · simp at hi
    · simp at hi
    · simp at hi
    · simp at hi
    · exact (hreg 7).trans hreg7
    · exact (hreg 8).trans hreg8
    · exact (hreg 9).trans hreg9

end SubexponentialSAT.SubexpScopeMembershipProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentPairFrontend
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical raw-pair input for assignment setup

The actual all-vertex pair producer runs in a fixed private bank. Two stack
transfers place its bytes, in their original order, on assignment input 45.
The scope source and private bank are then cleared by actual instructions.
-/

namespace SubexponentialSAT.Subexp.AssignmentPairFrontend

open BitProgram StructuredCalls

def moved (d : Data) : Data :=
  ⟨readRegs (readRegs d.regs 0 1 none) 0 1 none,
    Function.update (Function.update (Function.update d.stacks 0 []) 7 []) 45 (d.stacks 0)⟩

theorem move_eval (d : Data) (h7 : d.stacks 7 = []) (h45 : d.stacks 45 = []) :
    Eval move (6 * (d.stacks 0).length + 6) d (moved d) := by
  let a : Data := ⟨readRegs d.regs 0 1 none, StackRoutines.transferStacks 0 7 d.stacks⟩
  have h1 := TupleProgram.transfer_eval (0 : Fin 48) 7 (0 : Fin 16) 1
    (by decide) (by decide) d
  have h2 := TupleProgram.transfer_eval (7 : Fin 48) 45 (0 : Fin 16) 1
    (by decide) (by decide) a
  have he : (⟨readRegs a.regs 0 1 none,
      StackRoutines.transferStacks 7 45 a.stacks⟩ : Data) = moved d := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      by_cases h0j : j = 0
      · subst j; simp [a, StackRoutines.transferStacks]
      by_cases h7j : j = 7
      · subst j; simp [a, StackRoutines.transferStacks]
      by_cases h45j : j = 45
      · subst j; simp [a, StackRoutines.transferStacks, h7, h45]
      · simp [a, StackRoutines.transferStacks, h0j, h7j, h45j]
  rw [he] at h2
  convert h1.seq h2 using 1 <;>
    simp [move, a, StackRoutines.transferStacks, h7] ; omega

end SubexponentialSAT.Subexp.AssignmentPairFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceProgramInstall
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid generation and installation of raw pairs from a linear plan stream. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceProgram.Install
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

abbrev generate : Cmd 16 48 :=
  .call (ProgramLinking.liftProgram TupleProgram.generateProgram registers ports)
abbrev command : Cmd 16 48 :=
  .seq generate (.seq AssignmentPairFrontend.move (SequentialProgram.clearList bank))
end SubexponentialSAT.SqrtLog.PackingIncidenceProgram.Install

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingLoaderProgramFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Framing and paid parameter serialization for the packing loader. -/
namespace SubexponentialSAT.SqrtLog.PackingLoaderProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem framed_stack (outside : Store) (d : State 16 48) (i : Fin 64) :
    (framed outside d).stacks i =
      if h : i.val < 48 then d.stacks ⟨i.val,h⟩ else outside i := by
  by_cases hi : i.val < 48
  · let j : Fin 48 := ⟨i.val,hi⟩
    have hj : lowPorts j=i := Fin.ext rfl
    rw [← hj,framed_low]
    simp [j,lowPorts,hi]
  · have hn : ¬ ∃ j,lowPorts j=i := by
      rintro ⟨j,hj⟩
      have hval := congrArg Fin.val hj
      have := j.isLt
      change j.val=i.val at hval
      omega
    rw [framed_outside outside d i hn]
    simp [hi]

end SubexponentialSAT.SqrtLog.PackingLoaderProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingLoaderProgramFinish
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Install the packing scorer's depth and binary parameter bank after the
native alphabet/assignment producer has finished using its low workspace. -/
namespace SubexponentialSAT.SqrtLog.PackingLoaderProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage SubexponentialSAT.Subexp
attribute [local simp] Fin.coe_ofNat_eq_mod

def finishBudget (outside : Store) :=
  7*((outside 56).length+(outside 57).length+(outside 58).length+(outside 59).length)+24

end SubexponentialSAT.SqrtLog.PackingLoaderProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingLoaderProgramParameters
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid conversion of the actual binary radius and coordinate parameters. -/
namespace SubexponentialSAT.SqrtLog.PackingLoaderProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

def parameterBudget (outside : Store) :=
  LeafParametersProgram.Serialization.unaryCopyBound (outside 59)+1+
    (LeafParametersProgram.Serialization.unaryCopyBound (outside 55)+1)

end SubexponentialSAT.SqrtLog.PackingLoaderProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Framed local storage for the concrete packing caller. Ports53/54 retain
width/alphabet,55..59 parameters,60 scopes,61 plans,62 words,63 metadata. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
open PackingLoaderProgram

theorem high_not_low (j : Fin 64) (hj : 48 ≤ j.val) :
    ¬ ∃ i, lowPorts i=j := by
  rintro ⟨i,h⟩
  have hv := congrArg Fin.val h
  change i.val=j.val at hv
  have := i.isLt
  omega

def lowClearPorts : List (Fin 64) := (List.finRange 48).map lowPorts

@[simp] theorem mem_lowClearPorts (i : Fin 64) : i∈lowClearPorts ↔ i.val < 48 := by
  simp only [lowClearPorts,List.mem_map,List.mem_finRange,true_and]
  constructor
  · rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    change j.val=i.val at hv
    have := j.isLt
    omega
  · intro hi
    exact ⟨⟨i.val,hi⟩,Fin.ext rfl⟩

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingHeadProgramPrefix
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed counted loop over the existing flattened head prefix. Every
iteration copies the candidate and counts its true bitwise intersections with
one prefix word. No per-coordinate metadata or selected-pair stream is supplied. -/
namespace SubexponentialSAT.SqrtLog.PackingHeadProgramPrefix
open SubexponentialSAT BitProgram StructuredCalls StackRoutines SubexpScanPrimitives

def state (active : Bool) (candidate table work : List Bool) (n : ℕ) (out : List Bool) : Data :=
  ⟨![active,active,false,false,false],![candidate,table,work,[],out,unary n]⟩

end SubexponentialSAT.SqrtLog.PackingHeadProgramPrefix

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingWeightProgramGateBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingWeightProgram.Gate
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def copy (src dst : Fin 7) : Code := .call (StackRoutines.copyProgram src dst 6 0 1)

def clear (j : Fin 7) : Code := .call (StackRoutines.clearProgram j 0 1)
def convert : Code := liftCommand CounterConversions.unaryCmd 0 1 unaryRegisters unaryStacks

def compare : Code := .call (ProgramLinking.liftProgram Subexp.UnaryCompare.program id compareStacks)

end SubexponentialSAT.SqrtLog.PackingWeightProgram.Gate

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingWeightProgramGate
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingWeightProgram.Gate
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def choose : Code := .ite 3 (.base .skip) (copy 1 2)

/-- Binary n on0; arbitrary processed-count word on1. Only output2 changes. -/
def command : Code := .seq (copy 0 3) (.seq convert (.seq (copy 1 5)
  (.seq compare (.seq choose (.seq (clear 4) (clear 5))))))

end SubexponentialSAT.SqrtLog.PackingWeightProgram.Gate

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyController
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The fully instantiated fixed controller computes the original greedy
packing labels using the native reduced-score producer. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.SqrtLog.Packing

section Controller
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
  (ivar : I → V) (factor : I → E) {r Q : ℕ} [NeZero r]

def controllerCost (a : Word r Q) (tail : List (Word r Q)) (pairs : List (I × I))
    (vertices : List V) (factors : List E) (raw : List PairScoreProgram.PlanPair)
    (s M : ℕ) (nb sb mb rb : List Bool) : ℕ :=
  let indices := headsFirstIndices vertices factors
  let cost := uniformBudget indices.length pairs.length raw.length (a::tail).length
    (ReadPlan.wordWidth r Q) vertices.length (magnitude vertices.length s M r) (parameterBits nb sb mb rb)
  indices.length*(cost+SequentialProgram.selectionBudget (a::tail).length
    (scoreBound (a::tail) pairs indices vertices.length s M) indices.length
    (ReadPlan.encodeWord a).length+3)+3

end Controller
end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open PackingLoaderProgram PackingIncidenceInput

structure Parameters (outside : Store) (p : Problem) : Prop where
  ambient : SubexponentialSAT.BinaryArithmetic.toNat (outside 56)=p.n
  radius : SubexponentialSAT.BinaryArithmetic.toNat (outside 59)=p.r
  coordinate : SubexponentialSAT.BinaryArithmetic.toNat (outside 55)=p.Q
  epsilon : SubexponentialSAT.BinaryArithmetic.toNat (outside 57)=p.s
  incidence : SubexponentialSAT.BinaryArithmetic.toNat (outside 58)=p.incidences

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramBoundsBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open PackingLoaderProgram PackingIncidenceInput

/-- Literal input sizes and the two actually generated alphabets. -/
def scalarSize (outside : Store) (p : Problem) : ℕ :=
  p.n+p.factors+p.incidences+p.r+p.Q+p.s+p.r^p.Q+p.r^(2*p.Q)+
  (Scan.scopeBits p.scopes).length+p.mask.length+
  (outside 55).length+(outside 56).length+(outside 57).length+
  (outside 58).length+(outside 59).length+1

structure Cap (outside : Store) (p : Problem) (S : ℕ) : Prop where
  pos : 1 ≤ S
  n : p.n ≤ S
  factors : p.factors ≤ S
  incidences : p.incidences ≤ S
  r : p.r ≤ S
  Q : p.Q ≤ S
  s : p.s ≤ S
  alphabet : p.r^p.Q ≤ S
  types : p.r^(2*p.Q) ≤ S
  scopes : (Scan.scopeBits p.scopes).length ≤ S
  mask : p.mask.length ≤ S
  l55 : (outside 55).length ≤ S
  l56 : (outside 56).length ≤ S
  l57 : (outside 57).length ≤ S
  l58 : (outside 58).length ≤ S
  l59 : (outside 59).length ≤ S

theorem scalarSize_cap (outside : Store) (p : Problem) : Cap outside p (scalarSize outside p) := by
  constructor <;> dsimp [scalarSize] <;> omega

theorem width_le {outside : Store} {p : Problem} {S : ℕ} (h : Cap outside p S) :
    p.Q*p.r ≤ S^2 := by simpa [pow_two] using Nat.mul_le_mul h.Q h.r

theorem pairs_length (p : Problem) :
    (PackingProgram.Assembly.Scope.pairs p.scopes p.mask).length=p.incidences^2 := by
  unfold PackingProgram.Assembly.Scope.pairs
  have hp := List.length_product (Finished.incidenceList p.scopes p.mask)
    (Finished.incidenceList p.scopes p.mask)
  simpa [SProd.sprod,List.instSProd,Finished.incidenceList,Problem.incidences,pow_two] using hp

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramReplay
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The native packing caller neither reads nor writes the outer carried
tapes. Their contents therefore do not affect its exact running time. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Replay
open SubexponentialSAT BitProgram StructuredCalls ProgramTapeReplay
open LeafProgram.OuterCarried
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem park_avoids : AvoidsCmd LeafProgram.OuterCarried.hidden LeafProgram.LayoutMasters.parkLocal := by
  constructor
  · apply avoids_copyMany LeafProgram.OuterCarried.hidden 684 LeafProgram.LayoutMasters.parkPairs (away _ (by norm_num))
    intro p hp
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
    exact ⟨low_away i,high_away i⟩
  · apply avoids_clearMany
    intro p hp
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
    exact low_away i

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Replay

end OAI.Algorithms
end


