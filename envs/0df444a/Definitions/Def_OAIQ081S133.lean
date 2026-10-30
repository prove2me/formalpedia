-- Prove2me | Definitions.Def_OAIQ081S133
-- name    : OAIQ081S133
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:42:56.076515+00:00
-- url     : https://prove2.me/theorems/cd20d308-a594-4773-b231-2c069fe273b8
-- title:
--   Definitions bundle OAIQ081S133 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 32 declarations of OpenAI's Lean: 14 definitions and 18 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramPrefix.entry`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Assembly.HeadReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Assembly.headsBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Assembly.parameterLength`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Assembly.runBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Assembly.scorePairs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Streams.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Streams.writerLocal`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.HeadSelect.Code`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.HeadSelect.pop`, `OAI.Algorithms.SubexponentialSAT.Subexp.BasisTransposePlanProgram.LoopFrame`, `OAI.Algorithms.SubexponentialSAT.Subexp.BasisTransposePlanProgram.copied`, `OAI.Algorithms.SubexponentialSAT.Subexp.CandidateScoreProgram.inputState`, `OAI.Algorithms.SubexponentialSAT.Subexp.CandidateScoreProgram.writerData`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_HighQueryAdapter`, `SubexponentialSAT_SqrtLog_PackingHeadIncrementalPhysical`, `SubexponentialSAT_SqrtLog_PackingHeadProgramCandidatesBounds`, `SubexponentialSAT_SqrtLog_PackingHeadProgramCandidatesRun`, `SubexponentialSAT_SqrtLog_PackingHeadProgramPrefix`, `SubexponentialSAT_SqrtLog_PackingHeadProgramPreserve`, `SubexponentialSAT_SqrtLog_PackingIncidenceProgramSize`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyBounds`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyHeads`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyMetadata`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyRun`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyScore`, `SubexponentialSAT_SqrtLog_PackingProgramEmit`, `SubexponentialSAT_SqrtLog_PackingProgramStreamLoop`, `SubexponentialSAT_Subexp_BasisTransposePlanProgram`, `SubexponentialSAT_Subexp_CandidateScoreProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S100`, `OAIQ081S102`, `OAIQ081S111`, `OAIQ081S112` and `OAIQ081S113` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S148`, `OAIQ081S149`, `OAIQ081S150` and `OAIQ081S152`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S100
import Definitions.Def_OAIQ081S102
import Definitions.Def_OAIQ081S111
import Definitions.Def_OAIQ081S112
import Definitions.Def_OAIQ081S113

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

namespace HeadSelect
open OAI.Algorithms.SubexponentialSAT.StackRoutines

abbrev Code := Cmd 4 5

def pop : Code := .base (.atom (.pop 0 0 1))

end HeadSelect

open OAI.Algorithms.SubexponentialSAT.StackRoutines


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter
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

theorem guard_eval (candidate table : List Bool) (n : ℕ) (out : List Bool) :
    Eval guard 1 (state false candidate table [] n out)
      (state (flag n) candidate table [] (n-1) out) := by
  have h := StructuredProgram.Eval.atom (StructuredProgram.Atom.pop (5 : Fin 6) (0 : Fin 5) 1)
    (state false candidate table [] n out)
  apply Eval.base
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  cases n <;>
    apply state_ext <;> funext i <;> fin_cases i <;>
    simp [state,flag,unary,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg,execInstr,readRegs,List.replicate_succ]

theorem copy_eval (candidate table : List Bool) (n : ℕ) (out : List Bool) :
    Eval copy (7*candidate.length+5) (state true candidate table [] n out)
      (state false candidate table candidate n out) := by
  have h := SubexpScanPrimitives.copy_eval (state true candidate table [] n out)
    0 2 3 0 1 (by decide) (by decide) (by decide) (by decide) (by simp [state])
  have hz : afterCopy (state true candidate table [] n out) 0 2 0 1 =
      state false candidate table candidate n out := by
    apply state_ext <;> funext i <;> fin_cases i <;> simp [state,afterCopy,copyStacks,readRegs]
  rw [hz] at h
  simpa [copy,state] using h

theorem zip_eval (candidate word tail : List Bool) (n : ℕ) (out : List Bool)
    (hlen : candidate.length=word.length) :
    Eval zip (PackingHeadProgramAnd.steps candidate word)
      (state false candidate (word++tail) candidate n out)
      (state false candidate tail [] n
        (List.replicate (PackingHeadProgramAnd.jointTrue candidate word) false++out)) := by
  let d := state false candidate (word++tail) candidate n out
  let a : State 5 3 := ⟨fun _ => false,PackingHeadProgramAnd.stackData candidate (word++tail) out⟩
  let b : State 5 3 := ⟨fun _ => false,PackingHeadProgramAnd.stackData [] tail
    (List.replicate (PackingHeadProgramAnd.jointTrue candidate word) false++out)⟩
  have ha : embedState id zipPorts d a=d := by
    apply embedState_eq_of_ports id zipPorts d d a Function.injective_id zipPorts_injective
    · intro i; fin_cases i <;> simp [a,d,state]
    · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
    · intro i; fin_cases i <;> simp [a,d,state,zipPorts,PackingHeadProgramAnd.stackData]
    · intros; rfl
  have hb : embedState id zipPorts d b = state false candidate tail [] n
      (List.replicate (PackingHeadProgramAnd.jointTrue candidate word) false++out) := by
    apply embedState_eq_of_ports id zipPorts d _ _ Function.injective_id zipPorts_injective
    · intro i; fin_cases i <;> simp [b,state]
    · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
    · intro i; fin_cases i <;> simp [b,state,zipPorts,PackingHeadProgramAnd.stackData]
    · intro i hi
      have h1 : i ≠ 1 := fun h => hi ⟨1,by simpa [zipPorts] using h.symm⟩
      have h2 : i ≠ 2 := fun h => hi ⟨0,by simpa [zipPorts] using h.symm⟩
      have h4 : i ≠ 4 := fun h => hi ⟨2,by simpa [zipPorts] using h.symm⟩
      fin_cases i <;> simp_all [d,state]
  have ht := PackingHeadProgramAnd.trace (fun _ => false) candidate word tail out hlen
  have he := eval_call_lifted PackingHeadProgramAnd.program id zipPorts d
    Function.injective_id zipPorts_injective (a:=a) (b:=b) ht
  simpa only [ha,hb,zip] using he

def entry (candidate : List Bool) (rows : List (List Bool)) (out : List Bool) : Data :=
  state (flag rows.length) candidate rows.flatten [] (rows.length-1) out

theorem body_eval (candidate word : List Bool) (rows : List (List Bool)) (out : List Bool)
    (hlen : candidate.length=word.length) :
    Eval body (7*candidate.length+6+PackingHeadProgramAnd.steps candidate word)
      (entry candidate (word::rows) out)
      (entry candidate rows (List.replicate (PackingHeadProgramAnd.jointTrue candidate word) false++out)) := by
  have hc := copy_eval candidate (word++rows.flatten) rows.length out
  have hz := zip_eval candidate word rows.flatten rows.length out hlen
  have hg := guard_eval candidate rows.flatten rows.length
    (List.replicate (PackingHeadProgramAnd.jointTrue candidate word) false++out)
  have h := hc.seq (hz.seq hg)
  convert h using 1 <;> first | rfl | omega

theorem loop_eval (candidate : List Bool) (rows : List (List Bool)) (out : List Bool)
    (hlen : ∀ row ∈ rows,row.length=candidate.length) :
    Eval loop (loopCost candidate rows) (entry candidate rows out)
      (state false candidate [] [] 0 (List.replicate (score candidate rows) false++out)) := by
  induction rows generalizing out with
  | nil => simpa [loop,loopCost,entry,flag,score] using
      (Eval.while_false (test:=1) (body:=body) (a:=entry candidate [] out) (by simp [entry,state,flag]))
  | cons word rows ih =>
    have hb := body_eval candidate word rows out (hlen word (by simp)).symm
    have hi := ih (List.replicate (PackingHeadProgramAnd.jointTrue candidate word) false++out)
      (by intro row hr; exact hlen row (by simp [hr]))
    have h := Eval.while_true (test:=1) (body:=body) (by simp [entry,state,flag]) hb hi
    convert h using 1
    · simp only [loopCost]; omega
    · congr 1
      rw [show score candidate (word::rows) = score candidate rows +
        PackingHeadProgramAnd.jointTrue candidate word by simp [score,Nat.add_comm],
        List.replicate_add,List.append_assoc]

/-- Existing candidate bytes and flattened prefix bytes are the real inputs.
The unary prefix length is consumed; the candidate is preserved. -/
theorem command_eval (candidate : List Bool) (rows : List (List Bool)) (out : List Bool)
    (hlen : ∀ row ∈ rows,row.length=candidate.length) :
    Eval command (1+loopCost candidate rows)
      (state false candidate rows.flatten [] rows.length out)
      (state false candidate [] [] 0 (List.replicate (score candidate rows) false++out)) :=
  (guard_eval candidate rows.flatten rows.length out).seq (loop_eval candidate rows out hlen)

end SubexponentialSAT.SqrtLog.PackingHeadProgramPrefix

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingHeadIncrementalPhysical
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The exact score returned by the physical one-hot overlap loop, including
its heads-first phase gate, preserves the original selector ordering. -/
namespace SubexponentialSAT.SqrtLog.PackingHeadIncremental
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.LocalExpectation SubexponentialSAT.Subexp.LocalExpectation
open SubexponentialSAT.SqrtLog.Packing
open scoped BigOperators

variable {r Q : ℕ}

section Ordering
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E] [NeZero r]
variable (ivar : I → V) (factor : I → E)

omit [Fintype I] [Fintype E] [DecidableEq I] in
theorem sequentialNumerator_order_physical
    (alphabet : List (Word r Q)) (haN : alphabet.Nodup) (haC : ∀ z, z ∈ alphabet)
    (pairs : List (I × I)) (vertices : List V) (factors : List E)
    (hvN : vertices.Nodup) (hvC : ∀ v, v ∈ vertices)
    (w : PackingProgram.Weights) (default : Word r Q) (n : ℕ)
    (fixed : List (Word r Q))
    (hsize : n + 1 + fixed.length = (headsFirstIndices vertices factors).length)
    (x y : Word r Q) :
    PackingProgram.sequentialNumerator ivar factor alphabet
      (pairs.map Sum.inl ++ headTerms (I := I) (Q := Q) vertices)
      (headsFirstIndices vertices factors) w default n (x :: fixed) ≤
    PackingProgram.sequentialNumerator ivar factor alphabet
      (pairs.map Sum.inl ++ headTerms (I := I) (Q := Q) vertices)
      (headsFirstIndices vertices factors) w default n (y :: fixed) ↔
      w.incidence * sequentialIncidenceCount ivar factor alphabet pairs vertices factors default n (x :: fixed) +
        (2 * alphabet.length^4 * w.head) * physicalOverlap vertices.length x fixed ≤
      w.incidence * sequentialIncidenceCount ivar factor alphabet pairs vertices factors default n (y :: fixed) +
        (2 * alphabet.length^4 * w.head) * physicalOverlap vertices.length y fixed := by
  by_cases h : fixed.length < vertices.length
  · simpa only [physicalOverlap, ite_eq_left h, score_encode_prefix] using
      sequentialNumerator_order_head ivar factor alphabet haN haC pairs vertices factors hvN hvC
        w default n fixed hsize h x y
  · have hf : vertices.length ≤ fixed.length := Nat.le_of_not_gt h
    simpa only [physicalOverlap, ite_eq_right h, mul_zero, add_zero] using
      sequentialNumerator_order_factor ivar factor alphabet haN haC pairs vertices factors hvN hvC
        w default n fixed hf x y
end Ordering
end SubexponentialSAT.SqrtLog.PackingHeadIncremental

end OAI.Algorithms
end

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

theorem scan_eval (candidate : List Bool) (rows : List (List Bool)) (out : List Bool)
    (hlen : ∀ row ∈ rows,row.length=candidate.length) :
    Eval scan (1+PackingHeadProgramPrefix.loopCost candidate rows+1)
      (state candidate rows.flatten rows.length out rows.flatten (List.replicate rows.length true))
      (state candidate rows.flatten rows.length
        (List.replicate (PackingHeadProgramPrefix.score candidate rows) false++out)) := by
  let d := state candidate rows.flatten rows.length out rows.flatten (List.replicate rows.length true)
  let a := PackingHeadProgramPrefix.state false candidate rows.flatten [] rows.length out
  let b := PackingHeadProgramPrefix.state false candidate [] [] 0
    (List.replicate (PackingHeadProgramPrefix.score candidate rows) false++out)
  have ha : embedState id ports d a = d := by
    apply embedState_eq_of_ports id ports d d a Function.injective_id ports_injective
    · intro i; fin_cases i <;> simp [a,d,state,PackingHeadProgramPrefix.state]
    · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
    · intro i; fin_cases i <;> simp [a,d,state,ports,PackingHeadProgramPrefix.state,PackingHeadProgramPrefix.unary]
    · intros; rfl
  have hb : embedState id ports d b = state candidate rows.flatten rows.length
      (List.replicate (PackingHeadProgramPrefix.score candidate rows) false++out) := by
    apply embedState_eq_of_ports id ports d _ b Function.injective_id ports_injective
    · intro i; fin_cases i <;> simp [b,state,PackingHeadProgramPrefix.state]
    · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
    · intro i; fin_cases i <;> simp [b,state,ports,PackingHeadProgramPrefix.state,PackingHeadProgramPrefix.unary]
    · intro i hi
      have h4 : i ≠ 4 := fun h => hi ⟨4,by simpa [ports] using h.symm⟩
      have h6 : i ≠ 6 := fun h => hi ⟨1,by simpa [ports] using h.symm⟩
      have h7 : i ≠ 7 := fun h => hi ⟨5,by simpa [ports] using h.symm⟩
      fin_cases i <;> simp_all [d,state,ports]
  have ht := compiled_halt_trace (PackingHeadProgramPrefix.command_eval candidate rows out hlen) 0 4
  have he := eval_call_lifted PackingHeadProgramPrefix.program id ports d
    Function.injective_id ports_injective (a:=a) (b:=b) ht
  simpa only [ha,hb,scan] using he

theorem command_eval (candidate : List Bool) (rows : List (List Bool)) (out : List Bool)
    (hlen : ∀ row ∈ rows,row.length=candidate.length) :
    Eval command (7*rows.flatten.length+7*rows.length+PackingHeadProgramPrefix.loopCost candidate rows+12)
      (state candidate rows.flatten rows.length out)
      (state candidate rows.flatten rows.length
        (List.replicate (PackingHeadProgramPrefix.score candidate rows) false++out)) := by
  have h := (copyTable_eval candidate rows.flatten rows.length out).seq
    ((copyCount_eval candidate rows.flatten rows.length out).seq (scan_eval candidate rows out hlen))
  convert h using 1 <;> first | rfl | omega

end SubexponentialSAT.SqrtLog.PackingHeadProgramPreserve

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_CandidateScoreProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control candidate scoring

Score records are accumulated as reversed serialized bytes and reversed once
at the end, so output score order agrees with the input candidate order.
-/

namespace SubexponentialSAT.Subexp.CandidateScoreProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def writerData (v pr tag : Bool) (input output : List Bool) : State 3 2 :=
  ⟨![v,pr,tag],ParserProgram.pair input output⟩

def inputState (ctx : Context) (regs : Fin 16 → Bool) : State 16 36 := baseState ctx regs []

end SubexponentialSAT.Subexp.CandidateScoreProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramEmit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed serialization primitives for weighted candidate-score streams. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Streams
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

abbrev Data := State 8 12

def writerLocal (d : Data) : State 3 2 :=
  CandidateScoreProgram.writerData false false true []
    ((TupleProgram.escaped (d.stacks 4)).reverse ++ d.stacks 9)

end SubexponentialSAT.SqrtLog.PackingProgram.Streams

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

theorem finish_bytes (records : List (List Bool)) :
    TupleProgram.appendEncoded records [] ++ [false] = ProgramEncoding.encodeRecords records := by
  simpa only [List.reverse_cons,List.reverse_reverse] using CandidateScoreProgram.reverseRecord_finish records

end SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingHeadProgramCandidatesBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates
open SubexponentialSAT BitProgram StructuredCalls StackRoutines SubexpScanPrimitives Subexp
open scoped BigOperators

theorem output_length_le (rows candidates : List (List Bool)) (W : ℕ)
    (hlen : ∀ candidate ∈ candidates,candidate.length=W) :
    (ProgramEncoding.encodeRecords (scoreRecords rows candidates)).length ≤
      1+(2*(rows.length*W)+2)*candidates.length := by
  have h := ProgramEncoding.encodeRecords_length_le (scoreRecords rows candidates) (rows.length*W) ?_
  · simpa [scoreRecords] using h
  · intro payload hp
    obtain ⟨candidate,hc,rfl⟩ := List.mem_map.mp hp
    simp only [scoreBits,List.length_replicate]
    simpa [hlen candidate hc] using score_le candidate rows

theorem budget_le (rows candidates : List (List Bool)) (W : ℕ)
    (hlen : ∀ candidate ∈ candidates,candidate.length=W) :
    budget rows candidates ≤
      candidates.length*(43*rows.length*W+20*rows.length+17*W+66)+22 := by
  have hr := recordBudget_le rows candidates W hlen
  have ho := output_length_le rows candidates W hlen
  have he : (TupleProgram.appendEncoded (scoreRecords rows candidates) []).length+1 =
      (ProgramEncoding.encodeRecords (scoreRecords rows candidates)).length := by
    have h := congrArg List.length (CandidateScoreProgram.reverseRecord_finish (scoreRecords rows candidates))
    simpa using h
  unfold budget
  rw [he]
  nlinarith

end SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceProgramSize
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Input size, produced table size, and binary size of the exact numerator. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.MulticolorTypes SubexponentialSAT.LocalExpectation SubexponentialSAT.Subexp
open SubexponentialSAT.Subexp.LocalExpectation SubexponentialSAT.SqrtLog.Packing SubexponentialSAT.SqrtLog.PackingProgram

section Sizes
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
  (ivar : I → V) (factor : I → E) {r Q : ℕ}

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem incidenceNumerator_le (alphabet : List (Word r Q)) (pairs : List (I × I))
    (indices : List (V ⊕ E)) (default : Word r Q) (n : ℕ) (fixed : List (Word r Q)) :
    incidenceNumerator ivar factor alphabet pairs indices default n fixed ≤
      pairs.length * alphabet.length^4 := by
  simpa only [incidenceNumerator, List.length_map] using
    incidenceCount_le ivar factor alphabet (pairs.map Sum.inl) indices
      (List.range' fixed.length n) List.nodup_range' (decode default fixed)

end Sizes
end SubexponentialSAT.SqrtLog.PackingIncidenceProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramStreamLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The real dynamic loop over paired candidate counts. The pair list occurs
only in the input specification; the finite program reads runtime list tags. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Streams
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

 theorem resultBody_records (wi wh : List Bool) (ps : List (ℕ × ℕ)) :
    resultBody wi wh ps ++ [false] = SubexponentialSAT.ProgramEncoding.encodeRecords (scores wi wh ps) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [resultBody,scores,List.map_cons,SubexponentialSAT.ProgramEncoding.encodeRecords,
      SubexponentialSAT.Encoding.encodeList,List.cons_append,List.append_assoc] at *
    rw [ih]
    rfl

end SubexponentialSAT.SqrtLog.PackingProgram.Streams

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

def LoopFrame (base : Data) (counter output : Fin 7) (d : Data) : Prop :=
  ∀ i, i ≠ counter → i ≠ output → d.stacks i = base.stacks i

abbrev copied (src dst : Fin 7) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.copyStacks src dst d.stacks⟩

end SubexponentialSAT.Subexp.BasisTransposePlanProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyHeads
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual head-score production from the controller table and alphabet. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

def HeadReady (d : Data) : Prop := ∀ j : Fin 48,
  j ∈ ({1,2,3,4,5,6,7,12,13,14,15,16,17,18} : Finset (Fin 48)) → d.stacks j=[]

def headsBudget {r Q : ℕ} (d : Data) (headCount : ℕ) (fixed alphabet : List (Word r Q)) : ℕ :=
  PackingWeightProgram.Gate.budget (projectState gateRegisters gatePorts d)+1+
  PackingPrefixProgram.budget (Assembly.headCount headCount fixed) (ReadPlan.wordWidth r Q)+1+
  (7*(d.stacks 30).length+5)+16+
  PackingHeadProgramCandidates.budget (headRows headCount fixed) (alphabet.map ReadPlan.encodeWord)+
  3*(2*(Assembly.headCount headCount fixed*ReadPlan.wordWidth r Q+Assembly.headCount headCount fixed)+3)

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyMetadata
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid parking of four runtime integer parameters around the incidence scorer. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

def parameterLength (d : Data) : ℕ :=
  (d.stacks 20).length+(d.stacks 21).length+(d.stacks 22).length+(d.stacks 23).length

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

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

def scorePairs (alphabet : List (Word r Q)) (pairs : List (I × I))
    (indices : List (V ⊕ E)) (default : Word r Q) (heads n : ℕ)
    (fixed : List (Word r Q)) : List (ℕ × ℕ) :=
  alphabet.map (fun candidate =>
    (PackingIncidenceProgram.incidenceNumerator ivar factor alphabet pairs indices default n (candidate::fixed),
     overlap heads fixed candidate))

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem candidateScore_bound (alphabet : List (Word r Q)) (pairs : List (I × I))
    (indices : List (V ⊕ E)) (default : Word r Q) (heads s M n : ℕ)
    (fixed : List (Word r Q)) (candidate : Word r Q) (hsize : fixed.length ≤ indices.length) :
    candidateScore ivar factor alphabet pairs indices default heads s M n fixed candidate ≤
      scoreBound alphabet pairs indices heads s M := by
  apply reducedScore_bound
  · exact PackingIncidenceProgram.incidenceNumerator_le ivar factor alphabet pairs indices default n _
  · exact (overlap_le heads fixed candidate).trans (Nat.mul_le_mul_right _ hsize)

end Scores
end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete execution of the complete weighted-score producer from memory. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

section Run
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
  (ivar : I → V) (factor : I → E) {r Q : ℕ}

def runBudget (a : Word r Q) (tail fixed : List (Word r Q))
    (pairs : List (I × I)) (indices : List (V ⊕ E)) (raw : List PairScoreProgram.PlanPair)
    (heads remaining : ℕ) (d : Data) (wi wh : List Bool) : ℕ :=
  let ps := scorePairs ivar factor (a::tail) pairs indices a heads remaining fixed
  PackingIncidenceProgram.runtimeBound indices.length raw.length (a::tail).length (ReadPlan.wordWidth r Q)+
  12*parameterLength d+48+headsBudget d heads fixed (a::tail)+
  500*(2*dataLength d+4)^2+1+Zip.budget wi wh ps+
  6*(ProgramEncoding.encodeRecords (Streams.scores wi wh ps)).length+2*wi.length+2*wh.length+14

end Run
end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Numerical closure for the fixed packing scorer.  Every argument of the
bound is an input size or a numeric weight; no running-time oracle occurs. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

theorem dataLength_eq_parameterLength (d : Data) : dataLength d=parameterLength d := by
  simp [dataLength,parameterLength,PackingWeightProgram.inputLength,projectState,weightPorts]

theorem headsBudget_le {r Q : ℕ} (d : Data) (heads total : ℕ)
    (fixed alphabet : List (Word r Q))
    (hh : SubexponentialSAT.CounterPrograms.value (d.stacks 20)=heads)
    (hp : (d.stacks 19).length ≤ total) (hf : fixed.length ≤ total)
    (ha : d.stacks 30=ProgramEncoding.encodeRecords (alphabet.map ReadPlan.encodeWord)) :
    headsBudget d heads fixed alphabet ≤
      headBudgetBound total alphabet.length (ReadPlan.wordWidth r Q) heads (parameterLength d) := by
  have hn : (d.stacks 20).length ≤ parameterLength d := by unfold parameterLength; omega
  have hc : headCount heads fixed ≤ total := (headCount_le heads fixed).trans hf
  have hg := PackingWeightProgram.Gate.budget_le (projectState gateRegisters gatePorts d)
  change PackingWeightProgram.Gate.budget (projectState gateRegisters gatePorts d) ≤
    80*(SubexponentialSAT.CounterPrograms.value (d.stacks 20)+(d.stacks 19).length+
      (d.stacks 20).length+1)^2 at hg
  rw [hh] at hg
  have hg' : PackingWeightProgram.Gate.budget (projectState gateRegisters gatePorts d) ≤
      80*(heads+total+parameterLength d+1)^2 := by
    exact hg.trans (by gcongr)
  have ha' : (d.stacks 30).length ≤ 1+(2*ReadPlan.wordWidth r Q+2)*alphabet.length := by
    rw [ha]
    have h := ProgramEncoding.encodeRecords_length_le
      (alphabet.map ReadPlan.encodeWord) (ReadPlan.wordWidth r Q) (by
        intro x hx
        obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hx
        exact (ReadPlan.encodeWord_length w).le)
    simpa using h
  have hb := PackingHeadProgramCandidates.budget_le (headRows heads fixed)
    (alphabet.map ReadPlan.encodeWord) (ReadPlan.wordWidth r Q) (by
      intro x hx
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hx
      exact ReadPlan.encodeWord_length w)
  simp only [List.length_map,headRows_length] at hb
  have hb' : PackingHeadProgramCandidates.budget (headRows heads fixed)
      (alphabet.map ReadPlan.encodeWord) ≤
      alphabet.length*(43*total*ReadPlan.wordWidth r Q+20*total+
        17*ReadPlan.wordWidth r Q+66)+22 := hb.trans (by gcongr)
  unfold headsBudget headBudgetBound PackingPrefixProgram.budget
  gcongr

section Run
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
  (ivar : I → V) (factor : I → E) {r Q : ℕ}

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem runBudget_le (a : Word r Q) (tail fixed : List (Word r Q))
    (pairs : List (I × I)) (indices : List (V ⊕ E)) (raw : List PairScoreProgram.PlanPair)
    (heads remaining W : ℕ) (d : Data) (wi wh : List Bool)
    (hh : SubexponentialSAT.CounterPrograms.value (d.stacks 20)=heads)
    (hp : (d.stacks 19).length ≤ indices.length) (hf : fixed.length ≤ indices.length)
    (ha : d.stacks 30=ProgramEncoding.encodeRecords ((a::tail).map ReadPlan.encodeWord))
    (hbi : wi.length ≤ 2*parameterLength d+6) (hbh : wh.length ≤ 2*parameterLength d+6)
    (hi : SubexponentialSAT.CounterPrograms.value wi ≤ W) (hw : SubexponentialSAT.CounterPrograms.value wh ≤ W) :
    runBudget ivar factor a tail fixed pairs indices raw heads remaining d wi wh ≤
      uniformBudget indices.length pairs.length raw.length (a::tail).length
        (ReadPlan.wordWidth r Q) heads W (parameterLength d) := by
  let ps := scorePairs ivar factor (a::tail) pairs indices a heads remaining fixed
  let C := pairs.length*(a::tail).length^4+indices.length*ReadPlan.wordWidth r Q
  have hlen : ps.length=(a::tail).length := by simp [ps,scorePairs]
  have hc : ∀ p∈ps,p.1 ≤ C ∧ p.2 ≤ C := by
    intro p hmem
    obtain ⟨candidate,hcan,rfl⟩ := List.mem_map.mp hmem
    have hinc := PackingIncidenceProgram.incidenceNumerator_le ivar factor
      (a::tail) pairs indices a remaining (candidate::fixed)
    have hov := (overlap_le heads fixed candidate).trans (Nat.mul_le_mul_right _ hf)
    dsimp [C]
    exact ⟨hinc.trans (Nat.le_add_right _ _),hov.trans (Nat.le_add_left _ _)⟩
  have hz := Zip.budget_bound wi wh ps (2*parameterLength d+6) W C hbi hbh hi hw hc
  have ho := Streams.resultBody_length_bound wi wh ps W C hi hw hc
  have ho' : (ProgramEncoding.encodeRecords (Streams.scores wi wh ps)).length ≤
      (a::tail).length*(4*W*C+2)+1 := by
    rw [← Streams.resultBody_records,List.length_append,List.length_singleton]
    simpa only [hlen] using Nat.add_le_add_right ho 1
  have hh' := headsBudget_le d heads indices.length fixed (a::tail) hh hp hf ha
  rw [hlen] at hz
  unfold runBudget uniformBudget
  rw [dataLength_eq_parameterLength]
  change PackingIncidenceProgram.runtimeBound _ _ _ _ + _ + _ + _ + _ + _ +
    Zip.budget wi wh ps + _ + _ + _ + _ ≤ _
  unfold PackingIncidenceProgram.runtimeBound PackingIncidenceProgram.inputBound
    ScoreBuilderBounds.runtimeBound
  dsimp only [C,ps] at *
  simp only [List.length_cons] at *
  omega

end Run
end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
end


