-- Prove2me | Definitions.Def_OAIQ081S148
-- name    : OAIQ081S148
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:53:08.466859+00:00
-- url     : https://prove2.me/theorems/c3239cc4-64aa-40c2-9fd6-b413ecc2d3a2
-- title:
--   Definitions bundle OAIQ081S148 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 28 declarations of OpenAI's Lean: 8 definitions and 20 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates.baseState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates.boundary`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates.effect`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates.inputState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates.invariant`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates.scored`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Assembly.Scope.env`, `OAI.Algorithms.SubexponentialSAT.Subexp.BasisTransposePlanProgram.DownSpec`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_PackingHeadProgramCandidates`, `SubexponentialSAT_SqrtLog_PackingHeadProgramCandidatesLift`, `SubexponentialSAT_SqrtLog_PackingHeadProgramCandidatesRun`, `SubexponentialSAT_SqrtLog_PackingHeadProgramPreserve`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputEntry`, `SubexponentialSAT_SqrtLog_PackingIncidenceProgramInstall`, `SubexponentialSAT_SqrtLog_PackingIncidenceProgramPairs`, `SubexponentialSAT_SqrtLog_PackingPrefixProgramRun`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyOrder`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyScope`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyScore`, `SubexponentialSAT_SqrtLog_PackingProgramEmit`, `SubexponentialSAT_Subexp_BasisTransposePlanProgram`, `SubexponentialSAT_Subexp_CandidateScoreBounds`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S116`, `OAIQ081S124`, `OAIQ081S125`, `OAIQ081S130`, `OAIQ081S131`, `OAIQ081S132`, `OAIQ081S133` and `OAIQ081S134` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S161`, `OAIQ081S162` and `OAIQ081S163`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S116
import Definitions.Def_OAIQ081S124
import Definitions.Def_OAIQ081S125
import Definitions.Def_OAIQ081S130
import Definitions.Def_OAIQ081S131
import Definitions.Def_OAIQ081S132
import Definitions.Def_OAIQ081S133
import Definitions.Def_OAIQ081S134

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingHeadProgramPreserve
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A source-preserving wrapper for the actual prefix scan. The only input
streams are one candidate, the flattened prior words, and their unary count. -/
namespace SubexponentialSAT.SqrtLog.PackingHeadProgramPreserve
open SubexponentialSAT BitProgram StructuredCalls StackRoutines SubexpScanPrimitives
open scoped BigOperators

theorem program_run (candidate : List Bool) (rows : List (List Bool)) (out : List Bool)
    (hlen : ∀ row ∈ rows,row.length=candidate.length) :
    RunsIn program (rows.length*(21*candidate.length+20)+14)
      ((state candidate rows.flatten rows.length out).withPC (some program.entry))
      ((state candidate rows.flatten rows.length
        (List.replicate (PackingHeadProgramPrefix.score candidate rows) false++out)).withPC none) := by
  refine ⟨_,?_,compiled_halt_trace (command_eval candidate rows out hlen) 0 4⟩
  have h := PackingHeadProgramPrefix.loopCost_le candidate rows hlen
  rw [flatten_length candidate rows hlen]
  nlinarith

end SubexponentialSAT.SqrtLog.PackingHeadProgramPreserve

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramEmit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed serialization primitives for weighted candidate-score streams. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Streams
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

 theorem writeEscaped_eval (d : Data) :
    Eval writeEscaped (4*(d.stacks 4).length+4) d
      (embedState reg writerStack d (writerLocal d)) := by
  have h := CandidateScoreProgram.reverseEscape_trace (d.stacks 4) (d.stacks 9)
    (d.regs (reg 0)) (d.regs (reg 1)) (d.regs (reg 2))
  apply eval_call_from_state _ reg writerStack d reg_injective writerStack_injective
  have hp : projectState reg writerStack d = CandidateScoreProgram.writerData
      (d.regs (reg 0)) (d.regs (reg 1)) (d.regs (reg 2)) (d.stacks 4) (d.stacks 9) := by
    apply SubexponentialSAT.CounterForPrograms.data_ext <;> funext j <;> fin_cases j <;> rfl
  rw [hp]
  exact h

 theorem emit_eval (d : Data) :
    ∃ e : Data, Eval emit (4*(d.stacks 4).length+8) d e ∧
      e.stacks 4 = [] ∧
      e.stacks 9 = CandidateScoreProgram.reverseRecord (d.stacks 4) (d.stacks 9) ∧
      (∀ j, j ≠ 4 → j ≠ 9 → e.stacks j = d.stacks j) := by
  let a := TupleProgram.pushedState 9 0 true d
  let b := embedState reg writerStack a (writerLocal a)
  let e := TupleProgram.pushedState 9 0 false b
  have hrun := (TupleProgram.pushConst_eval 9 0 true d).seq
    ((writeEscaped_eval a).seq (TupleProgram.pushConst_eval 9 0 false b))
  have hb4 : b.stacks 4 = [] :=
    embedState_stack reg writerStack a (writerLocal a) writerStack_injective 0
  have hb9 : b.stacks 9 = (TupleProgram.escaped (d.stacks 4)).reverse ++ true :: d.stacks 9 := by
    exact embedState_stack reg writerStack a (writerLocal a) writerStack_injective 1
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · convert hrun using 1 <;> simp [a, emit ] ; omega
  · simpa [e, TupleProgram.pushedState] using hb4
  · simp [e, hb9, CandidateScoreProgram.reverseRecord,
      TupleProgram.frame_eq_escaped, List.reverse_append, List.append_assoc]
  · intro j hj4 hj9
    have hj : ¬∃ i, writerStack i = j := by
      rintro ⟨i, rfl⟩
      fin_cases i <;> simp [writerStack] at hj4 hj9
    have h := embedState_stack_frame reg writerStack a (writerLocal a) j hj
    simpa [e, b, a, TupleProgram.pushedState, hj9] using h

end SubexponentialSAT.SqrtLog.PackingProgram.Streams

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingHeadProgramCandidates
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed producer of all incremental head scores from the candidate alphabet
and actual flattened prior-head table. No selected pair records are inputs. -/
namespace SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates
open SubexponentialSAT BitProgram StructuredCalls StackRoutines SubexpScanPrimitives
open Subexp

def baseState (rows : List (List Bool)) (acc : List Bool) : Data :=
  ⟨fun i => decide (i=6),![[],rows.flatten,[],[],[],List.replicate rows.length true,[],[],[],acc,[],[]]⟩
def boundary (rows : List (List Bool)) (acc tail candidate : List Bool) : Data :=
  RecordPrograms.state ports (baseState rows acc) false true false tail candidate

theorem reverse_eval (rows : List (List Bool)) (acc tail candidate : List Bool) :
    Eval reverse (9*candidate.length+7) (boundary rows acc tail candidate.reverse)
      (boundary rows acc tail candidate) := by
  have h := SubexpScanPrimitives.reverse_eval (boundary rows acc tail candidate.reverse)
    0 2 3 0 1 (by decide) (by decide) (by decide) (by decide)
    (by simp [boundary,RecordPrograms.state,ports,baseState])
    (by simp [boundary,RecordPrograms.state,ports,baseState])
  have hz : afterReverse (boundary rows acc tail candidate.reverse) 0 0 1 =
      boundary rows acc tail candidate := by
    apply state_ext <;> funext i <;> fin_cases i <;>
      simp [afterReverse,reverseStacks,boundary,RecordPrograms.state,ports,baseState,readRegs]
  rw [hz] at h
  simpa [reverse,boundary,RecordPrograms.state,ports] using h

def scored (rows : List (List Bool)) (acc tail candidate : List Bool) : Data :=
  let d := boundary rows acc tail candidate
  ⟨d.regs,Function.update d.stacks 4
    (List.replicate (PackingHeadProgramPrefix.score candidate rows) false)⟩

theorem score_eval (rows : List (List Bool)) (acc tail candidate : List Bool)
    (hlen : ∀ row ∈ rows,row.length=candidate.length) :
    ∃ n ≤ rows.length*(21*candidate.length+20)+14,
      Eval score n (boundary rows acc tail candidate) (scored rows acc tail candidate) := by
  let d := boundary rows acc tail candidate
  let a := PackingHeadProgramPreserve.state candidate rows.flatten rows.length []
  let b := PackingHeadProgramPreserve.state candidate rows.flatten rows.length
    (List.replicate (PackingHeadProgramPrefix.score candidate rows) false)
  have ha : embedState reg low d a=d := by
    apply embedState_eq_of_ports reg low d d a reg_injective low_injective
    · intro i; fin_cases i <;> simp [a,d,PackingHeadProgramPreserve.state,boundary,RecordPrograms.state,ports,baseState,reg]
    · intros; rfl
    · intro i; fin_cases i <;> simp [a,d,PackingHeadProgramPreserve.state,boundary,RecordPrograms.state,ports,baseState,low]
    · intros; rfl
  have hb : embedState reg low d b=scored rows acc tail candidate := by
    apply embedState_eq_of_ports reg low d _ b reg_injective low_injective
    · intro i; fin_cases i <;> simp [b,scored,PackingHeadProgramPreserve.state,boundary,RecordPrograms.state,ports,baseState,reg]
    · intros; rfl
    · intro i; fin_cases i <;> simp [b,scored,PackingHeadProgramPreserve.state,boundary,RecordPrograms.state,ports,baseState,low]
    · intro i hi
      have h4 : i ≠ 4 := fun h => hi ⟨4,by simpa [low] using h.symm⟩
      simp [scored,d,h4]
  obtain ⟨n,hn,ht⟩ := PackingHeadProgramPreserve.program_run candidate rows [] hlen
  simp only [List.append_nil] at ht
  have he := eval_call_lifted PackingHeadProgramPreserve.program reg low d
    reg_injective low_injective (a:=a) (b:=b) ht
  exact ⟨n,hn,by simpa only [ha,hb,score] using he⟩

theorem reset_eval (d : Data) : Eval reset 9 d (resetState d) := by
  have h := (RegisterResetProgram.all_eval d).seq
    (Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.set (6 : Fin 8) true)
      (RegisterResetProgram.zeroed d)))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply state_ext
  · funext i; fin_cases i <;> simp [resetState,StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,execInstr]
  · rfl

end SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingHeadProgramCandidatesRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates
open SubexponentialSAT BitProgram StructuredCalls StackRoutines SubexpScanPrimitives Subexp

def invariant (rows : List (List Bool)) (d : Data) : Prop := ∃ acc, d=baseState rows acc

def effect (rows : List (List Bool)) (bits : List Bool) (a b : Data) : Prop :=
  b.stacks 9 = CandidateScoreProgram.reverseRecord (scoreBits rows bits) (a.stacks 9)

def inputState (rows candidates : List (List Bool)) : Data :=
  RecordPrograms.state ports (baseState rows []) false false false
    (ProgramEncoding.encodeRecords candidates) []

theorem finish_eval (rows candidates : List (List Bool)) :
    Eval finish (9*((TupleProgram.appendEncoded (scoreRecords rows candidates) []).length+1)+9)
      (baseState rows (TupleProgram.appendEncoded (scoreRecords rows candidates) []).reverse)
      (baseState rows (ProgramEncoding.encodeRecords (scoreRecords rows candidates))) := by
  let a := baseState rows (TupleProgram.appendEncoded (scoreRecords rows candidates) []).reverse
  let b := TupleProgram.pushedState 9 0 false a
  have hp := TupleProgram.pushConst_eval 9 0 false a
  have hr := SubexpScanPrimitives.reverse_eval b 9 2 3 0 1
    (by decide) (by decide) (by decide) (by decide)
    (by simp [b,a,baseState])
    (by simp [b,a,baseState])
  have hz : afterReverse b 9 0 1 =
      baseState rows (ProgramEncoding.encodeRecords (scoreRecords rows candidates)) := by
    apply state_ext
    · funext i; fin_cases i <;> simp [afterReverse,b,a,baseState,readRegs]
    · funext i; fin_cases i <;>
        simp [afterReverse,reverseStacks,b,a,baseState,
          finish_bytes]
  rw [hz] at hr
  convert hp.seq hr using 1 ;
    simp [b,a,baseState] ; omega

end SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingHeadProgramCandidatesLift
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Caller-state interface for the fixed all-candidate head score producer. -/
namespace SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates
open SubexponentialSAT BitProgram StructuredCalls StackRoutines SubexpScanPrimitives Subexp

theorem final_stacks (rows candidates : List (List Bool)) :
    (baseState rows (ProgramEncoding.encodeRecords (scoreRecords rows candidates))).stacks =
    Function.update (Function.update (inputState rows candidates).stacks 8 []) 9
      (ProgramEncoding.encodeRecords (scoreRecords rows candidates)) := by
  funext i; fin_cases i <;> simp [baseState,inputState,RecordPrograms.state,ports]

end SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_CandidateScoreBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! # Polynomial overhead of the actual candidate-scoring loop -/

namespace SubexponentialSAT.Subexp.CandidateScoreBounds

open BitProgram CandidateScoreProgram

theorem candidateScore_le (ctx : Context) (candidate : List Bool) :
    candidateScore ctx candidate ≤ ctx.pairs.length * ctx.alphabet.length ^ ctx.depth.length :=
  PairScoreProgram.score_le_leafCount (pairContext ctx candidate) ctx.pairs

end SubexponentialSAT.Subexp.CandidateScoreBounds

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

theorem generatedRawPairs_bytes (plans : List (List ℕ)) :
    ProgramEncoding.encodeRecords (TupleProgram.powerRows (planAlphabet plans) 2 [[]]) =
      PairScoreProgram.pairRecords (generatedRawPairs plans) := by
  apply congrArg ProgramEncoding.encodeRecords
  unfold generatedRawPairs
  rw [List.map_map]
  let rows := TupleProgram.powerRows (planAlphabet plans) 2 [[]]
  change rows = rows.map (fun x => PairScoreProgram.pairBytes (PairScoreProgram.readPair x))
  calc
    rows = rows.map id := (List.map_id _).symm
    _ = _ := by
      apply List.map_congr_left
      intro row hrow
      have hh := (CandidateScoreRefinement.generated_pair_payloads plans).mem_iff.mp hrow
      obtain ⟨pair, _, rfl⟩ := List.mem_map.mp hh
      simp

end SubexponentialSAT.SqrtLog.PackingIncidenceProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceProgramInstall
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid generation and installation of raw pairs from a linear plan stream. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceProgram.Install
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem generate_eval (plans : List (List ℕ)) (d : Data) (hd : Input plans d) :
    ∃ t ≤ TupleProgram.powerCost (planAlphabet plans) 2 [[]] + 9,
      ∃ e : Data, Eval generate t d e ∧
      e.stacks 0 = PairScoreProgram.pairRecords (generatedRawPairs plans) ∧
      (∀ j, j ≠ 0 → j ∉ bank → e.stacks j = d.stacks j) := by
  let a : State 10 9 := ⟨d.regs ∘ registers, d.stacks ∘ ports⟩
  have ha : ∀ i, a.stacks i = (pairInput plans).stacks i := hd.1
  have hready : TupleProgram.outerInvariant (planAlphabet plans) [true,true]
      (a.regs 9) a := by
    simp only [TupleProgram.outerInvariant, ha]
    simp [pairInput]
  obtain ⟨b, hb, t, ht, htrace⟩ := TupleProgram.generateProgram_runsIn
    (planAlphabet plans) [true,true] (a.regs 9) a hready
    (by rw [ha]; simp [pairInput]) (by rw [ha]; simp [pairInput])
    (by rw [ha]; simp [pairInput])
  let e := embedState registers ports d b
  have hin : embedState registers ports d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ registers_injective ports_injective
    all_goals intros; rfl
  have he := eval_call_lifted TupleProgram.generateProgram registers ports d
    registers_injective ports_injective htrace
  rw [hin] at he
  refine ⟨t, ht, e, he, ?_, ?_⟩
  · exact (embedState_stack registers ports d b ports_injective 0).trans
      (hb.2.1.trans (generatedRawPairs_bytes plans))
  · intro j h0 hj
    apply embedState_stack_frame
    rintro ⟨i, hi⟩
    subst j
    fin_cases i <;> first | exact h0 rfl | exact hj (by decide)

/-- The input plan stream is consumed, output 45 holds its actual pair table,
and every stack outside the fixed work bank is preserved. -/
theorem command_eval (plans : List (List ℕ)) (d : Data) (hd : Input plans d) :
    ∃ t, t+1 ≤ budget plans ∧ ∃ e : Data,
      Eval command t d e ∧
      e.stacks 45 = PairScoreProgram.pairRecords (generatedRawPairs plans) ∧
      (∀ j, j = 0 ∨ j = 7 ∨ j ∈ bank → e.stacks j = []) ∧
      (∀ j, j ≠ 0 → j ≠ 7 → j ≠ 45 → j ∉ bank → e.stacks j = d.stacks j) := by
  obtain ⟨t, ht, b, hb, hout, hf⟩ := generate_eval plans d hd
  have h7 : b.stacks 7 = [] := (hf 7 (by decide) (by decide)).trans hd.2.1
  have h45 : b.stacks 45 = [] := (hf 45 (by decide) (by decide)).trans hd.2.2
  have hg (j : Fin 48) : (b.stacks j).length ≤ (d.stacks j).length + t + 1 := by
    have h := SequentialProgram.trace_stack_length_le (compiled_halt_trace hb 20 0) j
    simpa only [StructuredProgram.State.withPC, Nat.add_assoc] using h
  have h0 : d.stacks 0 = [] := by simpa [ports, pairInput] using hd.1 0
  have hlen : (b.stacks 0).length ≤ t+1 := by simpa [h0] using hg 0
  let L := (ProgramEncoding.encodeRecords (planAlphabet plans)).length
  have hstart (j : Fin 48) (hj : j ∈ bank) : (d.stacks j).length ≤ L+2 := by
    have h20 := hd.1 1
    have h21 := hd.1 2
    have h22 := hd.1 3
    have h23 := hd.1 4
    have h24 := hd.1 5
    have h25 := hd.1 6
    have h26 := hd.1 7
    have h27 := hd.1 8
    simp [ports, pairInput] at h20 h21 h22 h23 h24 h25 h26 h27
    simp only [bank, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [L]
  have hclean (j : Fin 48) (hj : j ∈ bank) :
      ((AssignmentPairFrontend.moved b).stacks j).length ≤ L+t+3 := by
    have hj0 : j ≠ 0 := by rintro rfl; exact (by decide : (0 : Fin 48) ∉ bank) hj
    have hj7 : j ≠ 7 := by rintro rfl; exact (by decide : (7 : Fin 48) ∉ bank) hj
    have hj45 : j ≠ 45 := by rintro rfl; exact (by decide : (45 : Fin 48) ∉ bank) hj
    simp only [AssignmentPairFrontend.moved, Function.update_of_ne hj45,
      Function.update_of_ne hj7, Function.update_of_ne hj0]
    have h := hg j
    have hi := hstart j hj
    omega
  obtain ⟨m, hm, e, he, hs⟩ := SequentialProgram.clearList_eval bank
    (AssignmentPairFrontend.moved b) (L+t+3) hclean
  have htrace := hb.seq ((AssignmentPairFrontend.move_eval b h7 h45).seq he)
  refine ⟨t+(6*(b.stacks 0).length+6+m), ?_, e, htrace, ?_, ?_, ?_⟩
  · change m ≤ 8*(2*(L+t+3)+3) at hm
    dsimp [budget, L] at *
    omega
  · rw [hs]
    simpa [bank, AssignmentPairFrontend.moved] using hout
  · intro j hj
    rw [hs]
    rcases hj with rfl | rfl | hj
    · simp [bank, AssignmentPairFrontend.moved]
    · simp [bank, AssignmentPairFrontend.moved]
    · simp [hj]
  · intro j h0j h7j h45j hj
    rw [hs]
    simp only [hj, ite_false, AssignmentPairFrontend.moved,
      Function.update_of_ne h45j, Function.update_of_ne h7j, Function.update_of_ne h0j]
    exact hf j h0j hj

end SubexponentialSAT.SqrtLog.PackingIncidenceProgram.Install

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputEntry
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Entry from the actual descending high mask produced by the high-variable pass. -/


/-! Raw scopes and the computed mask feed the actual incidence-pair producer. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Finished
open SubexponentialSAT.BitProgram SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp

theorem generated_pairs (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (hm : mask.length ≤ n) :
    (PackingIncidenceProgram.generatedRawPairs (Install.plans scopes n mask)).Perm
      (PackingIncidenceProgram.rawPairs (Semantics.owner scopes n mask hm)
        (Semantics.factor scopes n mask hm)
        (Semantics.seedIndices n (Semantics.factorCount scopes mask))
        (incidenceList scopes mask)) := by
  rw [Install.plans, ← Semantics.incidencePlans_eq scopes n mask hm]
  exact PackingIncidenceProgram.generatedIncidencePairs_perm _ _ _ _

end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Finished

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

/-- This specification contains a real evaluation of the fixed body for
each remaining counter value. It is instantiated below by copying and
framing programs, never by an opaque arithmetic callback. -/
def DownSpec (body : Code) (counter output : Fin 7)
    (step : ℕ → List Bool → List Bool) (cost : ℕ → ℕ) (base : Data) : Prop :=
  ∀ n d, LoopFrame base counter output d → d.stacks counter = unary n →
    ∃ t e, t ≤ cost n ∧ Eval body t d e ∧
      e.stacks = Function.update d.stacks output (step n (d.stacks output))

theorem down_visits (body : Code) (counter output : Fin 7) (hco : counter ≠ output)
    (step : ℕ → List Bool → List Bool) (cost : ℕ → ℕ) (base : Data)
    (spec : DownSpec body counter output step cost base) (n : ℕ) :
    ∀ d : Data, LoopFrame base counter output d → d.stacks counter = unary n →
      ∃ costs t e, UnaryForPrograms.Visits (ports counter) body costs t d e ∧
        t ≤ downBudget cost n ∧
        e.stacks = Function.update (Function.update d.stacks counter []) output
          (downOutput step n (d.stacks output)) := by
  induction n with
  | zero =>
    intro d hf hc
    refine ⟨[], 2, UnaryForPrograms.popped (ports counter) d,
      .done d hc, le_rfl, ?_⟩
    funext i
    by_cases hic : i = counter
    · subst i
      simp [UnaryForPrograms.popped, ports, downOutput, hc, unary, hco]
    by_cases hio : i = output
    · subst i
      simp [UnaryForPrograms.popped, ports, downOutput, hco.symm]
    · simp [UnaryForPrograms.popped, ports, downOutput, hic, hio]
  | succ n ih =>
    intro d hf hc
    let p := UnaryForPrograms.popped (ports counter) d
    have hp : p.stacks counter = unary n := by
      simp [p, UnaryForPrograms.popped, ports, hc, unary, List.replicate_succ]
    have hpf : LoopFrame base counter output p := by
      intro i hic hio
      simpa [p, UnaryForPrograms.popped, ports, hic] using hf i hic hio
    obtain ⟨nb, e, hnb, he, hes⟩ := spec n p hpf hp
    have hec : e.stacks counter = unary n := by simp [hes, hco, hp]
    have hef : LoopFrame base counter output e := by
      intro i hic hio
      simpa [hes, hio] using hpf i hic hio
    obtain ⟨costs, nt, f, hv, hnt, hfs⟩ := ih e hef hec
    have hcounter : e.stacks (ports counter).counter = p.stacks (ports counter).counter := by
      simp [hes, ports, hco]
    refine ⟨nb :: costs, nb + nt + 2, f,
      .step (by simp [ports, hc, unary]) he hcounter hv, ?_, ?_⟩
    · simp only [downBudget]
      omega
    · funext i
      by_cases hic : i = counter
      · subst i
        simp [hfs, hco]
      by_cases hio : i = output
      · subst i
        simp [hfs, hes, downOutput, p, UnaryForPrograms.popped, ports, hco.symm]
      · simp [hfs, hes, p, UnaryForPrograms.popped, ports, hic, hio]

theorem copied_stacks (src dst : Fin 7) (d : Data) :
    (copied src dst d).stacks =
      Function.update d.stacks dst (d.stacks src ++ d.stacks dst) := rfl

end SubexponentialSAT.Subexp.BasisTransposePlanProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingPrefixProgramRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingPrefixProgram

open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.Subexp

theorem copy_eval (source target : Fin 11) (a : Data)
    (hsd : source ≠ target) (hs7 : source ≠ 7) (ht7 : target ≠ 7)
    (ht : a.stacks 7 = []) :
    Eval (copy source target) (7 * (a.stacks source).length + 5) a (copied source target a) :=
  TupleProgram.copy_eval source target 7 0 1 hsd hs7 ht7.symm (by decide) a ht

theorem clear_eval (stack : Fin 11) (a : Data) :
    Eval (clear stack) (2 * (a.stacks stack).length + 3) a (cleared stack a) :=
  TupleProgram.clear_eval stack 0 1 a

end SubexponentialSAT.SqrtLog.PackingPrefixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyScore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact values and uniform bounds for the two physically produced streams. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp

section Scores
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
  (ivar : I → V) (factor : I → E) {r Q : ℕ}

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem evaluate_bound (alphabet : List (Word r Q)) (pairs : List (I × I))
    (indices : List (V ⊕ E)) (default : Word r Q) (heads s M n : ℕ)
    (fixed : List (Word r Q)) (candidate : Word r Q) (hsize : n+1+fixed.length ≤ indices.length) :
    evaluate ivar factor alphabet pairs indices default heads s M n (candidate::fixed) ≤
      scoreBound alphabet pairs indices heads s M :=
  candidateScore_bound ivar factor alphabet pairs indices default heads s M n fixed candidate (by omega)

end Scores
end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyOrder
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Equality of all candidate comparisons with the original rational score. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp SubexponentialSAT.SqrtLog.Packing

section Ordering
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
  (ivar : I → V) (factor : I → E) {r Q : ℕ} [NeZero r]

omit [Fintype I] [Fintype E] [DecidableEq I] in
theorem candidateScore_order (alphabet : List (Word r Q)) (haN : alphabet.Nodup)
    (haC : ∀ z,z∈alphabet) (hq : 0 < alphabet.length)
    (pairs : List (I × I)) (vertices : List V) (factors : List E)
    (hvN : vertices.Nodup) (hvC : ∀ v,v∈vertices)
    (w : Weights) (s M : ℕ)
    (hi : w.incidence=vertices.length^2*(s*alphabet.length^2)^2)
    (hh : w.head=M^2*(2*r)^2)
    (default : Word r Q) (remaining : ℕ) (fixed : List (Word r Q))
    (hsize : remaining+1+fixed.length=(headsFirstIndices vertices factors).length)
    (x y : Word r Q) :
    candidateScore ivar factor alphabet pairs (headsFirstIndices vertices factors) default
      vertices.length s M remaining fixed x ≤
    candidateScore ivar factor alphabet pairs (headsFirstIndices vertices factors) default
      vertices.length s M remaining fixed y ↔
    sequentialNumerator ivar factor alphabet
      (pairs.map Sum.inl++PackingHeadIncremental.headTerms (I:=I) (Q:=Q) vertices)
      (headsFirstIndices vertices factors) w default remaining (x::fixed) ≤
    sequentialNumerator ivar factor alphabet
      (pairs.map Sum.inl++PackingHeadIncremental.headTerms (I:=I) (Q:=Q) vertices)
      (headsFirstIndices vertices factors) w default remaining (y::fixed) := by
  rw [PackingHeadIncremental.sequentialNumerator_order_physical ivar factor alphabet haN haC
    pairs vertices factors hvN hvC w default remaining fixed hsize x y]
  rw [hi,hh,sequentialIncidenceCount_eq,sequentialIncidenceCount_eq]
  unfold candidateScore
  rw [← overlap_eq_physical,← overlap_eq_physical]
  exact (reducedScore_scaled_order vertices.length s M r alphabet.length _ _ _ _ hq).symm

end Ordering
end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyScope
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native-scope specialization of the fixed weighted packing selector. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly.Scope
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.SqrtLog.Packing

def env (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    {r Q : ℕ} (a : Word r Q) (tail : List (Word r Q)) (nb sb mb rb : List Bool) :=
  Assembly.environment (ScoreBuilderRawInput.environment 1 (a::tail)
    (n+PackingIncidenceInput.Semantics.factorCount scopes mask) (raw scopes n mask)) nb sb mb rb

theorem generated_pairs (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (hmask : mask.length ≤ n) :
    (raw scopes n mask).Perm ((pairs scopes mask).map
      (PackingIncidenceProgram.incidencePair (PackingIncidenceInput.Semantics.owner scopes n mask hmask)
        (PackingIncidenceInput.Semantics.factor scopes n mask hmask) (PackingIncidenceInput.Semantics.seedIndices n (PackingIncidenceInput.Semantics.factorCount scopes mask)))) := by
  exact PackingIncidenceInput.Finished.generated_pairs scopes n mask hmask

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly.Scope

end OAI.Algorithms
end


