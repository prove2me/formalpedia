-- Prove2me | Definitions.Def_OAIQ081S096
-- name    : OAIQ081S096
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:16:26.36636+00:00
-- url     : https://prove2.me/theorems/6039a9bd-51f6-400c-9356-e85d50013954
-- title:
--   Definitions bundle OAIQ081S096 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 74 declarations of OpenAI's Lean: 64 definitions and 10 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates.callback`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates.clear`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates.finish`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates.lifted`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates.loop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates.reset`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates.reverse`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates.score`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramPrefix.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Loop.recordPrefix`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceProgram.planAlphabet`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingLoaderProgram.Code`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingLoaderProgram.capture`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Assembly.clearWeight`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Assembly.finishMerged`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Assembly.merge`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Assembly.scoreBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Assembly.weightAndMerge`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Assembly.weights`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Streams.clear`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Streams.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Streams.emit`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Streams.finish`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Streams.loop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Streams.pairCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Streams.readFields`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Streams.readTag`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Streams.weighted`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Streams.writeEscaped`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Zip.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Zip.pair`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Zip.weight`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.combineCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.headIndicator`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.incidenceIndicator`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.scaleClear`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.scaleCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.scaleCopy` and 24 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram`, `SubexponentialSAT_SqrtLog_PackingHeadIdentity`, `SubexponentialSAT_SqrtLog_PackingHeadProgramCandidates`, `SubexponentialSAT_SqrtLog_PackingHeadProgramCandidatesLift`, `SubexponentialSAT_SqrtLog_PackingHeadProgramCandidatesRun`, `SubexponentialSAT_SqrtLog_PackingHeadProgramPrefix`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputAddress`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputEmit`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputNative`, `SubexponentialSAT_SqrtLog_PackingIncidenceProgramPairs`, `SubexponentialSAT_SqrtLog_PackingLoaderProgramCapture`, `SubexponentialSAT_SqrtLog_PackingLoaderProgramFrame`, `SubexponentialSAT_SqrtLog_PackingPrefixScore`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyFinalize`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyMerge`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyScore`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyWeights`, `SubexponentialSAT_SqrtLog_PackingProgramCombine`, `SubexponentialSAT_SqrtLog_PackingProgramCounts`, `SubexponentialSAT_SqrtLog_PackingProgramEmit`, `SubexponentialSAT_SqrtLog_PackingProgramScale`, `SubexponentialSAT_SqrtLog_PackingProgramStreamLoop`, `SubexponentialSAT_SqrtLog_PackingProgramStreams`, `SubexponentialSAT_SqrtLog_PackingProgramZip`, `SubexponentialSAT_SubexpScopeCountSetup`, `SubexponentialSAT_Subexp_ActivePlanProgram`, `SubexponentialSAT_Subexp_AssignmentInputCall`, `SubexponentialSAT_Subexp_CollisionGenerateProgram`, `SubexponentialSAT_Subexp_CollisionStreamProgram`, `SubexponentialSAT_Subexp_CollisionTupleProgram`, `SubexponentialSAT_Subexp_PairPlanPreparation`, `SubexponentialSAT_Subexp_PairPreparationProgram`, `SubexponentialSAT_Subexp_SequentialProgram`, `SubexponentialSAT_Subexp_SequentialStep`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S066`, `OAIQ081S067`, `OAIQ081S069`, `OAIQ081S071`, `OAIQ081S072`, `OAIQ081S073` and `OAIQ081S078` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S110`, `OAIQ081S111`, `OAIQ081S112`, `OAIQ081S113`, `OAIQ081S114` and `OAIQ081S115`; the proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.clauseCount_eval`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S066
import Definitions.Def_OAIQ081S067
import Definitions.Def_OAIQ081S069
import Definitions.Def_OAIQ081S071
import Definitions.Def_OAIQ081S072
import Definitions.Def_OAIQ081S073
import Definitions.Def_OAIQ081S078

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

abbrev Data := State 24 24

end Selector

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingHeadIdentity
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One-hot word overlap is exactly the number of equal head coordinates. -/
namespace SubexponentialSAT.SqrtLog.Packing
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes

theorem headColorBits_and_count {r Q : ℕ} (u v : Word r Q) (t : Fin Q) :
    (List.zipWith (· && ·) (headColorBits u t) (headColorBits v t)).count true =
      if u t = v t then 1 else 0 := by
  rw [headColorBits, headColorBits, zipWith_ofFn', count_true_ofFn]
  by_cases h : u t = v t
  · simp [h]
  · apply (Finset.sum_eq_zero fun c _ => ?_).trans (ite_eq_right h).symm
    by_cases hu : u t = c
    · have hv : v t ≠ c := by intro hv; exact h (hu.trans hv.symm)
      simp [hu, hv]
    · simp [hu]

theorem encodeWord_and_count {r Q : ℕ} (u v : Word r Q) :
    (List.zipWith (· && ·) (SubexponentialSAT.Subexp.ReadPlan.encodeWord u)
      (SubexponentialSAT.Subexp.ReadPlan.encodeWord v)).count true =
      ∑ t : Fin Q, if u t = v t then 1 else 0 := by
  induction Q with
  | zero => simp [SubexponentialSAT.Subexp.ReadPlan.encodeWord]
  | succ Q ih =>
    have split (w : Word r (Q+1)) : SubexponentialSAT.Subexp.ReadPlan.encodeWord w =
        headColorBits w 0 ++ SubexponentialSAT.Subexp.ReadPlan.encodeWord (fun t => w t.succ) := by
      simp only [SubexponentialSAT.Subexp.ReadPlan.encodeWord, headColorBits, List.ofFn_succ,
        List.flatten_cons]
    rw [split u, split v, List.zipWith_append (by simp), List.count_append,
      headColorBits_and_count, ih, Fin.sum_univ_succ]

end SubexponentialSAT.SqrtLog.Packing

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

abbrev Data := State 5 6

end SubexponentialSAT.SqrtLog.PackingHeadProgramPrefix

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_CollisionStreamProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed collision callback with a persistent output stream

The runtime ABI reserves stack 0 for a packed row table, stack 3 for its unary
word width, stacks 8 and 10 for the two read plans, and stack 11 for the output
stream. Stacks 1 and 12 hold the two gathered type encodings. The remaining
stacks are gathering scratch. All sizes, plans, and encoded words are data.

The equality stage below uses the existing fixed equality program, clears its
possibly unconsumed input suffixes, and pushes one collision bit. In particular,
an early mismatch cannot leave stale type bytes in the next callback's scratch.
-/

namespace SubexponentialSAT.Subexp.CollisionStreamProgram

open BitProgram StackRoutines StructuredCalls

abbrev leftGather : Cmd 5 13 :=
  .call (ProgramLinking.liftProgram GatherProgram.program gatherRegs leftPorts)

abbrev rightGather : Cmd 5 13 :=
  .call (ProgramLinking.liftProgram GatherProgram.program gatherRegs rightPorts)

abbrev command : Cmd 5 13 := .seq leftGather (.seq rightGather sealCommand)

abbrev program : Program 5 13 (StructuredCalls.size command + 1) :=
  StructuredCalls.compiled command 0 11

end SubexponentialSAT.Subexp.CollisionStreamProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_CollisionTupleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Streaming collisions from framed runtime tuples

The current word array and selected read plans are preserved. Each parsed
tuple is appended to the current array by actual transfer/copy routines, then
the fixed collision callback gathers the two types and emits one bit.
-/

namespace SubexponentialSAT.Subexp.CollisionTupleProgram

open BitProgram StackRoutines StructuredCalls

abbrev collision : Cmd 8 18 := .call (ProgramLinking.liftProgram
  CollisionStreamProgram.program lowRegs lowStacks)

abbrev callback : Cmd 8 18 :=
  .seq (.call (transferProgram 17 0 0 1))
    (.seq (.call (copyProgram 13 0 4 0 1))
      (.seq (.call (copyProgram 14 8 4 0 1))
        (.seq (.call (copyProgram 15 10 4 0 1))
          (.seq collision (.call (clearProgram 0 0 1))))))

abbrev command : Cmd 8 18 := RecordPrograms.iterate ports callback

abbrev program : Program 8 18 (StructuredCalls.size command + 1) :=
  StructuredCalls.compiled command 16 11

end SubexponentialSAT.Subexp.CollisionTupleProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_CollisionGenerateProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Generating and evaluating collision tuples with fixed control

The alphabet and unary tuple depth are input data. The generator and collision
stream are linked through actual stack ports. The current word table and the
two selected read plans remain runtime inputs and are preserved.
-/

namespace SubexponentialSAT.Subexp.CollisionGenerateProgram

open BitProgram StackRoutines StructuredCalls

abbrev streamCommand : Cmd 10 20 :=
  .call (ProgramLinking.liftProgram CollisionTupleProgram.program streamRegs streamPorts)

end SubexponentialSAT.Subexp.CollisionGenerateProgram

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

abbrev writeEscaped : Cmd 8 12 := .call
  (SubexponentialSAT.ProgramLinking.liftProgram CandidateScoreProgram.reverseEscapeProgram reg writerStack)

 def emit : Cmd 8 12 := .seq (TupleProgram.pushConst 9 0 true)
  (.seq writeEscaped (TupleProgram.pushConst 9 0 false))

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

abbrev reverse : Cmd 8 12 := .call (reverseProgram 0 2 3 0 1)

abbrev score : Cmd 8 12 := .call
  (ProgramLinking.liftProgram PackingHeadProgramPreserve.program reg low)

abbrev reset : Cmd 8 12 := .seq RegisterResetProgram.all (.base (.atom (.set 6 true)))

abbrev clear : Cmd 8 12 := .call (clearProgram 0 0 1)
abbrev callback : Cmd 8 12 := .seq reverse (.seq score (.seq PackingProgram.Streams.emit (.seq clear reset)))

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

abbrev loop : Cmd 8 12 := RecordPrograms.iterate ports callback

abbrev finish : Cmd 8 12 := .seq (TupleProgram.pushConst 9 0 false)
  (.call (reverseProgram 9 2 3 0 1))

abbrev command : Cmd 8 12 := .seq loop finish
abbrev program : Program 8 12 (size command+1) := compiled command 8 9

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

abbrev lifted {R S : ℕ} (reg : Fin 8 → Fin R) (stack : Fin 12 → Fin S) : Cmd R S :=
  .call (ProgramLinking.liftProgram program reg stack)

end SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates

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

theorem record_eval (d : Data) (bits : List Bool) (hp : d.stacks 2 = bits.reverse) :
    Eval record (5*bits.length+7) d (recorded d bits) := by
  let a := SubexpNormalizeProgram.filterState (d.regs 0) (d.regs 1) (d.regs 2)
    (d.stacks 0) (d.stacks 4) (d.stacks 3) bits.reverse
  let b := SubexpNormalizeProgram.filterState true false (d.regs 2)
    (d.stacks 0) (d.stacks 4) (true :: (Encoding.frame bits ++ d.stacks 3)) []
  have ha : embedState id recordPorts d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id recordPorts_injective
    · intro i; fin_cases i <;> rfl
    · intros; rfl
    · intro i; fin_cases i <;> simp [a, recordPorts, SubexpNormalizeProgram.filterState,
        SubexpPostfixControl.quadruple, hp]
    · intros; rfl
  have hb : embedState id recordPorts d b = recorded d bits := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id recordPorts_injective
    · intro i; fin_cases i <;> rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [b, recordPorts, recorded,
        SubexpNormalizeProgram.filterState, SubexpPostfixControl.quadruple]
    · intro i hi
      have h2 : i ≠ 2 := fun h => hi ⟨3,h.symm⟩
      have h3 : i ≠ 3 := fun h => hi ⟨2,h.symm⟩
      simp [recorded, h2, h3]
  have h := eval_call_lifted SubexpNormalizeProgram.emitRecordProgram id recordPorts d
    Function.injective_id recordPorts_injective
    (SubexpNormalizeProgram.emitRecord_trace bits (d.stacks 0) (d.stacks 4)
      (d.stacks 3) (d.regs 0) (d.regs 1) (d.regs 2))
  change Eval record _ (embedState id recordPorts d a) (embedState id recordPorts d b) at h
  rw [ha,hb] at h
  exact h

end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Emit

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_ActivePlanProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Computing the active completion positions

A fixed program filters a runtime list of unary seed positions. It retains a
position precisely when it is at least the runtime threshold and belongs to
the runtime pair read plan. The plan and threshold are preserved. Applying the
program to the complete ascending seed list gives a duplicate-free completion
plan in ascending order.
-/

namespace SubexponentialSAT.Subexp.ActivePlanProgram

open BitProgram StructuredCalls StackRoutines

abbrev emit : Cmd 10 12 :=
  .call (ProgramLinking.liftProgram SubexpNormalizeProgram.emitIfSelectedProgram emitRegs emitStack)

abbrev callback : Cmd 10 12 :=
  .seq member (.seq compare (.seq (RecordPrograms.atom (.band 9 4 3)) emit))

abbrev reverseCall : Cmd 10 12 :=
  .call (ProgramLinking.liftProgram SubexpNormalizeProgram.reverseRecordsProgram emitRegs reverseStack)

abbrev command : Cmd 10 12 :=
  .seq initAccumulator (.seq (RecordPrograms.iterate ports callback) (.seq initializeOutput reverseCall))

abbrev program : Program 10 12 (size command + 1) := compiled command 5 11

end SubexponentialSAT.Subexp.ActivePlanProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PairPlanPreparation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual parsing and record-order preparation of the two plans in a pair
payload. Registers 0, 1, and 2 are scratch; all other registers are framed. -/

namespace SubexponentialSAT.Subexp.PairPlanPreparation

open BitProgram StackRoutines StructuredCalls

abbrev reverseRecords (src dst : Fin 34) : Cmd 16 34 :=
  .call (ProgramLinking.liftProgram SubexpNormalizeProgram.reverseRecordsProgram
    smallRegs (reversePorts src dst))

/-- Prepare the concatenated union of the two vertex plans for filtering. -/
abbrev buildUnion : Cmd 16 34 :=
  .seq (copy 25 6) (.seq (copy 24 0) (reverseRecords 0 6))

/-- Produce the reversed query-record lists required by the selector mapper.
Existing union/filter data in stacks 6 and 9 is explicitly cleared first. -/
abbrev reverseQueries : Cmd 16 34 :=
  .seq (clear 6) (.seq (clear 9) (.seq seedOutputs
    (.seq (reverseRecords 24 6) (reverseRecords 25 9))))

end SubexponentialSAT.Subexp.PairPlanPreparation

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

abbrev activeCall : Cmd 16 34 :=
  .call (ProgramLinking.liftProgram ActivePlanProgram.program activeRegs activeStacks)

abbrev reverseCall : Cmd 16 34 :=
  .call (ProgramLinking.liftProgram SubexpNormalizeProgram.reverseRecordsProgram
    tableRegs reverseStacks)

end SubexponentialSAT.Subexp.PairPreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_SequentialProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed sequential assignment control

The loop counter, processed index, word width, alphabet, and assignment are
runtime stack data. A fixed score-building command is composed with the
verified minimum selector and preserving packed-array operations.
-/

namespace SubexponentialSAT.Subexp.SequentialProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem minimum_eval {A : Type*} (score : A → ℕ) (a : A) (tail : List A)
    (d : Data)
    (hr : ∀ i, d.regs (minimumRegisters i) = false)
    (hs : d.stacks 0 = ProgramEncoding.encodeRecords
      ((a :: tail).map (fun x => UnaryCompare.encode (score x))))
    (he : ∀ i : Fin 8, i ≠ 0 → d.stacks (minimumStacks i) = []) :
    ∃ t ≤ 500 * (score a + (tail.map score).sum + tail.length + 1) ^ 2,
      ∃ e : Data, ∃ k < (a :: tail).length,
        Eval (.call minimumProgram) t d e ∧
        (e.stacks 7).length = k ∧
        (a :: tail)[k]? = some (NaturalAssignment.chooseMinNat score a tail) ∧
        (∀ j : Fin 48, 8 ≤ j.val → e.stacks j = d.stacks j) ∧
        (∀ j : Fin 16, 9 ≤ j.val → e.regs j = d.regs j) ∧
        (∀ j : Fin 48, j.val < 8 → (e.stacks j).length ≤
          (d.stacks 0).length + 500 * (score a + (tail.map score).sum + tail.length + 1) ^ 2) := by
  obtain ⟨small, k, hk, ⟨t, ht, htrace⟩, hout, hlookup⟩ :=
    MinimumProgram.program_candidates score a tail
  let initialSmall := MinimumProgram.inputState
    ((a :: tail).map (fun x => UnaryCompare.encode (score x)))
  have hi : (⟨fun i => d.regs (minimumRegisters i),
      fun i => d.stacks (minimumStacks i)⟩ : State 9 8) = initialSmall := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext j
      simp [ MinimumProgram.emptyData, MinimumProgram.ports, hr]
    · funext j
      by_cases hj : j = 0
      · subst j
        simpa [initialSmall, MinimumProgram.inputState, RecordPrograms.state,
          MinimumProgram.ports, minimumStacks] using hs
      ·
        rw [he j hj]
        by_cases hj1 : j = 1 <;>
          simp [ MinimumProgram.emptyData, MinimumProgram.ports, hj, hj1, Function.update_apply]
  have hi' : embedState minimumRegisters minimumStacks d initialSmall = d := by
    rw [← hi]
    exact embed_restrict d
  let e := embedState minimumRegisters minimumStacks d small
  have hcall := eval_call_lifted MinimumProgram.program minimumRegisters minimumStacks d
    minimumRegisters_injective minimumStacks_injective htrace
  refine ⟨t, ht, e, k, hk, ?_, ?_, hlookup, ?_, ?_, ?_⟩
  · change Eval (.call (ProgramLinking.liftProgram MinimumProgram.program
      minimumRegisters minimumStacks)) t
      (embedState minimumRegisters minimumStacks d initialSmall)
      (embedState minimumRegisters minimumStacks d small) at hcall
    simpa only [hi', minimumProgram] using hcall
  · change ((embedState minimumRegisters minimumStacks d small).stacks (minimumStacks 7)).length = k
    rw [embedState_stack _ _ _ _ minimumStacks_injective]
    exact hout
  · intro j hj
    apply embedState_stack_frame
    rintro ⟨i, h⟩
    have hv := congrArg Fin.val h
    change i.val = j.val at hv
    omega

  · intro j hj
    apply embedState_register_frame
    rintro ⟨i, h⟩
    have hv := congrArg Fin.val h
    change i.val = j.val at hv
    omega
  · intro j hj
    let i : Fin 8 := ⟨j.val, hj⟩
    have hji : minimumStacks i = j := Fin.ext rfl
    rw [← hji]
    change ((embedState minimumRegisters minimumStacks d small).stacks (minimumStacks i)).length ≤ _
    rw [embedState_stack _ _ _ _ minimumStacks_injective]
    have hg := trace_stack_length_le htrace i
    change (small.stacks i).length ≤ (initialSmall.stacks i).length + t at hg
    have hlen : (initialSmall.stacks i).length ≤ (d.stacks 0).length := by
      rw [← hi]
      by_cases hz : i = 0
      · rw [hz]; exact le_rfl
      · simp [he i hz]
    omega

/-- A preserving alphabet lookup followed by a preserving assignment write.
All indices and widths are runtime unary stacks. -/
theorem wordUpdate_eval (d : Data) (before assigned : List (List Bool))
    (new old after rest : List Bool)
    (hcandidates : d.stacks 9 = before.flatten ++ (new ++ after))
    (hassignment : d.stacks 8 = assigned.flatten ++ (old ++ rest))
    (hindex : (d.stacks 7).length = before.length)
    (hprocessed : (d.stacks 19).length = assigned.length)
    (hbefore : ∀ row ∈ before, row.length = (d.stacks 10).length)
    (hassigned : ∀ row ∈ assigned, row.length = (d.stacks 10).length)
    (hnew : new.length = (d.stacks 10).length)
    (hold : old.length = (d.stacks 10).length)
    (h12 : d.stacks 12 = []) (h13 : d.stacks 13 = []) (h14 : d.stacks 14 = [])
    (h15 : d.stacks 15 = []) (h16 : d.stacks 16 = []) (h17 : d.stacks 17 = [])
    (h18 : d.stacks 18 = []) :
    Eval wordUpdate
      ((before.length * (14 * (d.stacks 10).length + 10) + 15 * (d.stacks 10).length + 16) +
        ((7 * assigned.length + 5) +
          (assigned.length * (14 * (d.stacks 10).length + 10) +
            20 * (d.stacks 10).length + 21)))
      d (afterWordUpdate d assigned new rest) := by
  let r : Data := ⟨readRegs d.regs 9 8 none,
    ArrayUpdateLifted.readStacksAt readEmbedding new d.stacks⟩
  have hr : Eval (.call readProgram)
      (before.length * (14 * (d.stacks 10).length + 10) +
        15 * (d.stacks 10).length + 16) d r :=
    ArrayUpdateLifted.readProgramAt_eval readEmbedding 9 8 (by decide)
      before new after (d.stacks 10) (d.stacks 7) d.regs d.stacks
      hcandidates rfl rfl hindex hbefore hnew h13 h14 h15 h16
  let c : Data := ⟨readRegs r.regs 9 8 none, copyStacks 19 17 r.stacks⟩
  have hc : Eval (.call (copyProgram (19 : Fin 48) 17 18 (9 : Fin 16) 8))
      (7 * assigned.length + 5) r c := by
    have h := ListRegisterProgram.copy_run (19 : Fin 48) 17 18 (9 : Fin 16) 8
      (by decide) (by decide) (by decide) (by decide) r.regs r.stacks
      (by simpa [r, ArrayUpdateLifted.readStacksAt, readEmbedding, readPorts] using h18)
    have hc' : Eval (.call (copyProgram (19 : Fin 48) 17 18 (9 : Fin 16) 8))
        (7 * (r.stacks 19).length + 5) r c := .call _ h
    convert hc' using 1
    all_goals try with_reducible_and_instances rfl
    simp [r, ArrayUpdateLifted.readStacksAt, readEmbedding, readPorts, hprocessed]
  let e : Data := ⟨readRegs c.regs 9 8 none,
    ArrayUpdateLifted.replaceStacksAt replaceEmbedding assigned new rest c.stacks⟩
  have hrpl : Eval (.call replaceProgram)
      (assigned.length * (14 * (d.stacks 10).length + 10) +
        20 * (d.stacks 10).length + 21) c e := by
    apply ArrayUpdateLifted.replaceProgramAt_eval replaceEmbedding 9 8 (by decide)
      assigned old new rest (d.stacks 10) (d.stacks 19) c.regs c.stacks
    all_goals try simp [c, r, ArrayUpdateLifted.readStacksAt, copyStacks,
      readEmbedding, readPorts, replaceEmbedding, replacePorts,
      h12, h17, hassignment, hprocessed, hold, hnew, h13, h14, h15, h16]
    exact hassigned
  have heq : e = afterWordUpdate d assigned new rest := by
    apply congrArg₂ StructuredProgram.State.mk
    · simp [ c, r, readRegs_reset]
    · funext j
      simp only [ c, r, ArrayUpdateLifted.replaceStacksAt,
        ArrayUpdateLifted.readStacksAt, copyStacks, readEmbedding, readPorts,
        replaceEmbedding, replacePorts]
      by_cases h7 : j = 7 <;> by_cases h12j : j = 12 <;>
        by_cases h17j : j = 17 <;> by_cases h8 : j = 8 <;>
        subst_vars <;> simp_all []
  rw [← heq]
  exact hr.seq (hc.seq hrpl)

end SubexponentialSAT.Subexp.SequentialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_SequentialStep
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete composition of score selection and packed assignment update. -/

namespace SubexponentialSAT.Subexp.SequentialProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

/-- The concrete selection/update code needs only a prepared score stream;
every following operation is an actual fixed machine subroutine. -/
theorem selectAndUpdate_eval {A : Type*} (encode : A → List Bool) (a : A) (tail : List A)
    (hwidth : ∀ x, (encode x).length = (encode a).length)
    (score : A → ℕ) (S total n : ℕ) (fixed : List A)
    (hscore : ∀ x ∈ a :: tail, score x ≤ S) (hfixed : fixed.length ≤ total)
    (base d : Data) (hm : Memory encode a tail (n + 1) fixed base.stacks)
    (hs : d.stacks 0 = ProgramEncoding.encodeRecords
      ((a :: tail).map (fun x => UnaryCompare.encode (score x))))
    (hf : ∀ j : Fin 48, j.val < 20 → j ≠ 0 → d.stacks j = base.stacks j) :
    ∃ t ≤ selectionBudget (a :: tail).length S total (encode a).length,
      ∃ e : Data,
        Eval selectAndUpdate t d e ∧
        Memory encode a tail n
          (NaturalAssignment.chooseMinNat score a tail :: fixed) e.stacks ∧
        e.stacks 11 = base.stacks 11 ∧
        (∀ j : Fin 48, 20 ≤ j.val → e.stacks j = d.stacks j) := by
  let q := (a :: tail).length
  let w := (encode a).length
  let chosen := NaturalAssignment.chooseMinNat score a tail
  let assigned := fixed.reverse.map encode
  let rest := (List.replicate n (encode a)).flatten
  have hsum := sum_scores_le tail score S (fun x hx => hscore x (by simp [hx]))
  have hhead := hscore a (by simp)
  have hminBound : 500 * (score a + (tail.map score).sum + tail.length + 1) ^ 2 ≤
      minimumBudget q S := by
    unfold minimumBudget q
    gcongr
    simp only [List.length_cons]
    nlinarith
  have hrecord : (d.stacks 0).length ≤ recordBudget q S := by
    rw [hs, ProgramEncoding.encodeRecords_length]
    simp only [List.map_map, Function.comp_def, UnaryCompare.encode_length,
      List.map_cons, List.sum_cons, List.length_map, List.length_cons]
    unfold recordBudget q
    simp only [List.length_cons]
    nlinarith
  obtain ⟨r, hr, hrs, hrr⟩ := resetRegisters_eval d
  have hrinput : r.stacks 0 = d.stacks 0 := congrFun hrs 0
  have hrsmall (i : Fin 8) (hi : i ≠ 0) : r.stacks (minimumStacks i) = [] := by
    rw [hrs, hf (minimumStacks i) (by change i.val < 20; omega)
      (by
        intro h
        have hv := congrArg (fun j : Fin 48 => j.val) h
        exact hi (Fin.ext hv))]
    exact hm.scratch _ (by
      fin_cases i <;> simp_all [minimumStacks, scratchPorts])
  obtain ⟨m, hmb, middle, k, hk, hmin, hki, hlookup, hframe, _, hsmall⟩ :=
    minimum_eval score a tail r hrr (hrinput.trans hs) hrsmall
  have hmiddle (j : Fin 48) (hj : 8 ≤ j.val) (hj20 : j.val < 20) :
      middle.stacks j = base.stacks j := by
    rw [hframe j hj, hrs, hf j hj20 (by intro h; subst j; omega)]
  obtain ⟨before, after, hsplit, hbeforelen⟩ := lookup_split (a :: tail) k chosen hlookup
  have hwidth' (x : A) : (encode x).length = (middle.stacks 10).length := by
    rw [hmiddle 10 (by decide) (by decide), hm.width, hwidth]
  have hbefore : ∀ row ∈ before.map encode, row.length = (middle.stacks 10).length := by
    intro row hrow
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hrow
    exact hwidth' x
  have hassigned : ∀ row ∈ assigned, row.length = (middle.stacks 10).length := by
    intro row hrow
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hrow
    exact hwidth' x
  have hcandidate : middle.stacks 9 =
      (before.map encode).flatten ++ (encode chosen ++ (after.map encode).flatten) := by
    rw [hmiddle 9 (by decide) (by decide), hm.alphabet, hsplit]
    simp [List.map_append, List.flatten_append, List.flatten_cons]
  have hassign : middle.stacks 8 = assigned.flatten ++ (encode a ++ rest) := by
    rw [hmiddle 8 (by decide) (by decide), hm.assignment]
    simp [assigned, rest, List.replicate_succ, List.flatten_append, List.flatten_cons]
  have hc (j : Fin 48) (hj : j ∈ scratchPorts) (hlo : 8 ≤ j.val) (hhi : j.val < 20) :
      middle.stacks j = [] := by
    rw [hmiddle j hlo hhi]
    exact hm.scratch j hj
  have hup := wordUpdate_eval middle (before.map encode) assigned (encode chosen) (encode a)
    (after.map encode).flatten rest hcandidate hassign
    (by simpa [hbeforelen] using hki)
    (by simpa [hmiddle 19 (by decide) (by decide), assigned] using hm.processed)
    hbefore hassigned (hwidth' chosen) (hwidth' a)
    (hc 12 (by decide) (by decide) (by decide))
    (hc 13 (by decide) (by decide) (by decide))
    (hc 14 (by decide) (by decide) (by decide))
    (hc 15 (by decide) (by decide) (by decide))
    (hc 16 (by decide) (by decide) (by decide))
    (hc 17 (by decide) (by decide) (by decide))
    (hc 18 (by decide) (by decide) (by decide))
  let updated := afterWordUpdate middle assigned (encode chosen) rest
  let cb := recordBudget q S + minimumBudget q S + w
  have hcleanBound : ∀ j ∈ cleanPorts, (updated.stacks j).length ≤ cb := by
    intro j hj
    have hcases : j.val < 8 ∨ j = 12 :=
      (show ∀ j : Fin 48, j ∈ cleanPorts → j.val < 8 ∨ j = 12 by decide) j hj
    rcases hcases with hj | rfl
    · by_cases h7 : j = 7
      · simp [updated, h7, cb]
      · have hj12 : j ≠ 12 := by intro h; subst j; omega
        have hj8 : j ≠ 8 := by intro h; subst j; omega
        have hh := hsmall j hj
        rw [hrinput] at hh
        simp only [updated, Function.update_of_ne hj8,
          Function.update_of_ne hj12, Function.update_of_ne h7]
        unfold cb
        omega
    · simp [updated, cb, w, hwidth]
  obtain ⟨c, hcb, cleaned, hclean, hcleaned⟩ := cleanAuxiliary_eval updated cb hcleanBound
  let final := afterProcessed cleaned
  have hfinal : Memory encode a tail n (chosen :: fixed) final.stacks := by
    constructor
    · rw [show final.stacks 8 = cleaned.stacks 8 by simp [final, afterProcessed]]
      rw [hcleaned]
      simp [ updated, assigned, rest, List.reverse_cons,
        List.map_append, List.flatten_append, List.flatten_cons, List.append_assoc]
    · rw [show final.stacks 9 = cleaned.stacks 9 by simp [final, afterProcessed], hcleaned]
      simpa [cleanPorts, updated, afterWordUpdate, hmiddle 9 (by decide) (by decide)]
        using hm.alphabet
    · rw [show final.stacks 10 = cleaned.stacks 10 by simp [final, afterProcessed], hcleaned]
      simpa [cleanPorts, updated, afterWordUpdate, hmiddle 10 (by decide) (by decide)]
        using hm.width
    · simp [final, afterProcessed, hcleaned, updated,
        hmiddle 19 (by decide) (by decide), hm.processed]
    · intro j hj
      rcases scratch_partition j hj with hjclean | hjhigh
      · have hj19 : j ≠ 19 := by
          intro heq
          subst j
          simp [cleanPorts] at hjclean
        simp only [final, afterProcessed, Function.update_of_ne hj19, hcleaned]
        exact ite_eq_left hjclean
      · have hj19 : j ≠ 19 := by intro heq; subst j; omega
        have hj7 : j ≠ 7 := by intro heq; subst j; omega
        have hj8 : j ≠ 8 := by intro heq; subst j; omega
        have hj12 : j ≠ 12 := by intro heq; subst j; omega
        simp only [final, afterProcessed, Function.update_of_ne hj19, hcleaned]
        split
        · rfl
        · simp only [updated, Function.update_of_ne hj8,
            Function.update_of_ne hj12, Function.update_of_ne hj7]
          rw [hmiddle j (by omega) (by omega)]
          exact hm.scratch j hj
  have hcounter : final.stacks 11 = base.stacks 11 := by
    simp [final, afterProcessed, hcleaned, updated,
      hmiddle 11 (by decide) (by decide)]
  have hhigh : ∀ j : Fin 48, 20 ≤ j.val → final.stacks j = d.stacks j := by
    intro j hj
    have hj19 : j ≠ 19 := by intro heq; subst j; omega
    have hj12 : j ≠ 12 := by intro heq; subst j; omega
    have hj8 : j ≠ 8 := by intro heq; subst j; omega
    have hj7 : j ≠ 7 := by intro heq; subst j; omega
    have hnot : j ∉ cleanPorts := by
      intro hm
      have hc := (show ∀ j : Fin 48, j ∈ cleanPorts → j.val < 13 by decide) j hm
      omega
    change j ∉ ([0, 1, 2, 3, 4, 5, 6, 7, 12] : List (Fin 48)) at hnot
    simp only [final, afterProcessed, Function.update_of_ne hj19, hcleaned, ite_eq_right hnot,
      updated, Function.update_of_ne hj8,
      Function.update_of_ne hj12, Function.update_of_ne hj7]
    rw [hframe j (by omega), hrs]
  let updateTime := (before.map encode).length * (14 * (middle.stacks 10).length + 10) +
          15 * (middle.stacks 10).length + 16 +
        (7 * assigned.length + 5 +
          (assigned.length * (14 * (middle.stacks 10).length + 10) +
            20 * (middle.stacks 10).length + 21))
  have hupdateBound : updateTime ≤ updateBudget q total w := by
    have hbeforeq : before.length ≤ q := by
      rw [hbeforelen]
      exact Nat.le_of_lt hk
    simp only [updateTime, List.length_map, assigned, List.length_reverse]
    rw [hmiddle 10 (by decide) (by decide), hm.width]
    unfold updateBudget w
    gcongr
  refine ⟨9 + (m + (updateTime + (c + 2))), ?_, final, ?_, hfinal, hcounter, hhigh⟩
  · change 9 + (m + (updateTime + (c + 2))) ≤ selectionBudget q S total w
    unfold selectionBudget
    change c ≤ 9 * (2 * (recordBudget q S + minimumBudget q S + w) + 3) at hcb
    omega
  · exact hr.seq (hmin.seq (hup.seq (hclean.seq (incrementProcessed_eval cleaned))))

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

def planAlphabet (plans : List (List ℕ)) : List (List Bool) :=
  plans.map (fun p => Encoding.frame (CollisionStreamProgram.planBytes p))

end SubexponentialSAT.SqrtLog.PackingIncidenceProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpScopeCountSetup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual preserving scope-record count and assignment-fuel setup.
The scope and base remain on stacks 1 and 0. The program returns unary arity,
binary exponent, and binary base^arity on stacks 2, 3, and 4. -/

namespace SubexponentialSAT.SubexpScopeCountSetup

open BitProgram StructuredCalls

def counterState (value present : Bool) (input output : List Bool) : State 2 2 :=
  ⟨ParserProgram.pair value present, ParserProgram.pair input output⟩

theorem counter_trace (records : List (List Bool)) (value present : Bool) :
    Trace counterProgram (SubexpSunflowerProgram.CountRecords.loopSteps records)
      ((counterState value present (Encoding.encodeList id records) []).withPC (some counterProgram.entry))
      ((counterState false false [] (List.replicate records.length true)).withPC none) := by
  have h := SubexpSunflowerProgram.CountRecords.loop_trace records [] [] value present
  simpa [counterProgram, counterState, SubexpSunflowerProgram.CountRecords.cfg] using h

end SubexponentialSAT.SubexpScopeCountSetup

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


/-! One native low-variable step, including its uncovered neutral factor. -/


/-! Runtime high-mask loop for the original-address incidence stream. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Loop
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
def recordPrefix (ps : List (List ℕ)) : List Bool :=
  ps.flatMap fun p => true :: Encoding.frame (Encoding.frame (CollisionStreamProgram.planBytes p))

theorem row_prefix (scopes : List (List ℕ)) (n v z : ℕ) :
    recordPrefix (rowPlans scopes n v z) = Rows.prefixes v n (Step.factors scopes v z) := by
  simp only [recordPrefix,rowPlans,Rows.prefixes,List.flatMap_map]
  rfl

end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Loop


/-! Count the physical scope stream before constructing native incidence plans. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramCounts
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Splitting all weighted completions into two unweighted integer counts. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram
open SubexponentialSAT.LocalExpectation SubexponentialSAT.Subexp.LocalExpectation
open SubexponentialSAT.SqrtLog.Packing SubexponentialSAT.MulticolorTypes

section Scores
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ}

def incidenceIndicator : ScoreTerm I V Q → WordAssignment V E r Q → ℕ
  | .inl (i,j), ω => if incidenceType ivar factor ω i = incidenceType ivar factor ω j then 1 else 0
  | .inr _, _ => 0

def headIndicator : ScoreTerm I V Q → WordAssignment V E r Q → ℕ
  | .inl _, _ => 0
  | .inr (t,v,u), ω => if ω (.inl v) t = ω (.inl u) t then 1 else 0

def unweightedCounts (alphabet : List (Word r Q)) (terms : List (ScoreTerm I V Q))
    (indices : List (V ⊕ E)) (remaining : List ℕ) (ω : ℕ → Word r Q) : ℕ × ℕ :=
  (commonNumerator alphabet terms
    (fun z η => incidenceIndicator ivar factor z (fun i => η (indexCode indices i)))
    (numberedScoreSupport ivar factor indices) 4 remaining ω,
   commonNumerator alphabet terms
    (fun z η => headIndicator z (fun i => η (indexCode indices i)))
    (numberedScoreSupport ivar factor indices) 4 remaining ω)

end Scores
end SubexponentialSAT.SqrtLog.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputAddress
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The saved native plan stream is exactly the layout's typed word-address
stream, in the native incidence enumeration order. No conversion is required. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Address
open SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

variable {r Q : ℕ}

/-- Equality in the actual native list order, including repeated plans. -/
theorem labelPlans_eq (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (hm : mask.length ≤ n) (words : List (Word r Q))
    (hw : words.length = n + Semantics.factorCount scopes mask) :
    LayoutProgram.labelPlans words (address scopes n mask hm words hw) =
      Install.plans scopes n mask := by
  change LayoutProgram.labelPlans words (address scopes n mask hm words hw) =
    Loop.plans scopes n 0 scopes.length mask
  rw [← Semantics.incidencePlans_eq scopes n mask hm]
  unfold LayoutProgram.labelPlans PackingIncidenceProgram.incidencePlans
  apply List.map_congr_left
  intro i _
  rw [Semantics.incidencePlan_eq]
  rfl

end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Address

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
abbrev Code := Cmd 16 64

end SubexponentialSAT.SqrtLog.PackingLoaderProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingLoaderProgramCapture
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Consume the incidence installer's transient metadata while preserving an
explicit raw-scope master outside the selector's48-stack bank. -/
namespace SubexponentialSAT.SqrtLog.PackingLoaderProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
attribute [local simp] Fin.coe_ofNat_eq_mod

def capture : Code := .seq (copyMany 31 captureCopies) (clearMany captureClears)

end SubexponentialSAT.SqrtLog.PackingLoaderProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingPrefixScore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact head-term enumeration and physical prefix overlap. -/
namespace SubexponentialSAT.SqrtLog.Packing
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.LocalExpectation

section Prior
variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
variable {r Q : ℕ}

theorem priorHeadOverlap_eq_prefix (vertices : List V) (factors : List E)
    (hvn : vertices.Nodup) (hv : ∀ v, v ∈ vertices)
    (default z : Word r Q) (fixed : List (Word r Q)) (n : ℕ)
    (hsize : n + 1 + fixed.length = (headsFirstIndices vertices factors).length)
    (hprefix : fixed.length ≤ vertices.length) :
    (∑ t : Fin Q, ∑ v : V,
      if indexCode (headsFirstIndices vertices factors) (.inl v) = fixed.length ∨
        indexCode (headsFirstIndices vertices factors) (.inl v) ∈
          List.range' (fixed.length+1) n then 0
      else if z t = decode default fixed
        (indexCode (headsFirstIndices vertices factors) (.inl v)) t then (1 : ℕ) else 0) =
      (fixed.map (fun w => ∑ t : Fin Q, if z t = w t then (1 : ℕ) else 0)).sum := by
  have ht (t : Fin Q) : (∑ v : V,
      if indexCode (headsFirstIndices vertices factors) (.inl v) = fixed.length ∨
        indexCode (headsFirstIndices vertices factors) (.inl v) ∈
          List.range' (fixed.length+1) n then 0
      else if z t = decode default fixed
        (indexCode (headsFirstIndices vertices factors) (.inl v)) t then (1 : ℕ) else 0) =
      (fixed.map (fun w => if z t = w t then (1 : ℕ) else 0)).sum := by
    rw [← headsFirst_prefix_sum vertices factors hvn hv default fixed hprefix
      (fun w => if z t = w t then (1 : ℕ) else 0)]
    apply Finset.sum_congr rfl
    intro v _
    have hp := headsFirst_prior_iff vertices factors hv fixed.length n hsize v
    by_cases h : indexCode (headsFirstIndices vertices factors) (.inl v) = fixed.length ∨
      indexCode (headsFirstIndices vertices factors) (.inl v) ∈ List.range' (fixed.length+1) n
    · have hh : ¬ indexCode (headsFirstIndices vertices factors) (.inl v) < fixed.length := by
        intro hh; exact (hp.mpr hh) h
      simp only [ite_eq_left h, ite_eq_right hh]
    · simp only [ite_eq_right h, ite_eq_left (hp.mp h)]
  simp_rw [ht]
  have exchange (xs : List (Word r Q)) :
      (∑ t : Fin Q, (xs.map (fun w => if z t = w t then (1 : ℕ) else 0)).sum) =
        (xs.map (fun w => ∑ t : Fin Q, if z t = w t then (1 : ℕ) else 0)).sum := by
    induction xs with
    | nil => simp
    | cons w xs ih => simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]
  exact exchange fixed
end Prior
end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramScale
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed binary-counted copier scales a unary score, preserving both inputs.
The loop count is read from the multiplier stack and every copied bit is paid. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def scalePorts : SubexponentialSAT.CounterForPrograms.Ports 3 6 where
  register := Function.Embedding.refl _
  counter := 3
  scratch := 4
  counter_ne_scratch := by decide

abbrev scaleCopy (src dst : Fin 6) : Cmd 3 6 :=
  .call (SubexponentialSAT.StackRoutines.copyProgram src dst 5 0 1)
abbrev scaleClear : Cmd 3 6 := .call (SubexponentialSAT.StackRoutines.clearProgram 3 0 1)
abbrev scaleCommand : Cmd 3 6 :=
  .seq (scaleCopy 0 3)
    (.seq (SubexponentialSAT.CounterForPrograms.forCmd scalePorts (scaleCopy 1 2)) scaleClear)
end SubexponentialSAT.SqrtLog.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramCombine
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed two-call score combiner. Inputs are binary weights and canonical
false-unary collision counts. The only modified port is the score accumulator. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev combineCommand : Cmd 3 8 :=
  .seq (liftCommand scaleCommand 0 2 id incidenceScaleStacks)
    (liftCommand scaleCommand 0 2 id headScaleStacks)
end SubexponentialSAT.SqrtLog.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramStreams
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingProgram.Streams
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

 def weighted : Cmd 8 12 := liftCommand combineCommand 0 4 reg low
 def clear (j : Fin 12) : Cmd 8 12 := .call (SubexponentialSAT.StackRoutines.clearProgram j 0 1)


 def readFields : Cmd 8 12 :=
  .seq (SubexponentialSAT.SubexpInputFrames.readField 8 1 (by decide))
    (SubexponentialSAT.SubexpInputFrames.readField 8 3 (by decide))

 def pairCommand : Cmd 8 12 :=
  .seq readFields (.seq weighted (.seq (.seq (clear 1) (clear 3)) emit))

end SubexponentialSAT.SqrtLog.PackingProgram.Streams

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

 def readTag : Cmd 8 12 := SubexponentialSAT.SubexpInputFrames.readTag 8
 def loop : Cmd 8 12 := .while 7 (.seq pairCommand readTag)

 def finish : Cmd 8 12 := .seq (TupleProgram.pushConst 9 0 false)
  (.call (SubexponentialSAT.StackRoutines.transferProgram 9 10 0 1))
 def command : Cmd 8 12 := .seq readTag (.seq loop finish)
end SubexponentialSAT.SqrtLog.PackingProgram.Streams

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramZip
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual pairing and weighting of two candidate-ordered unary score streams.
This is one fixed finite program; no precomputed pair list is an input premise. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Zip
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

 def pair : Cmd 8 14 := .call
  (SubexponentialSAT.ProgramLinking.liftProgram SubexponentialSAT.SubexpInputZip.program id zipPorts)
 def weight : Cmd 8 14 := liftCommand Streams.command 8 10 id scorePorts
 def command : Cmd 8 14 := .seq pair weight
end SubexponentialSAT.SqrtLog.PackingProgram.Zip

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyMerge
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Relocation of the concrete stream merger into the sequential controller ABI. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

abbrev merge : Cmd 16 48 := liftCommand Zip.command 0 8 mergeRegisters mergePorts

abbrev finishMerged : Cmd 16 48 := move 7 0 1

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyWeights
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual native coefficient construction followed by stream weighting. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

abbrev weights : Cmd 16 48 :=
  liftCommand PackingWeightProgram.command 0 4 mergeRegisters weightPorts

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyFinalize
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! End-to-end native weighting, serialization, and scratch cleanup. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

abbrev clearWeight (i : Fin 48) : Cmd 16 48 := .call (SubexponentialSAT.StackRoutines.clearProgram i 0 1)
abbrev weightAndMerge : Cmd 16 48 := .seq weights (.seq (.seq merge finishMerged)
  (.seq (clearWeight 15) (clearWeight 16)))

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

def scoreBound (alphabet : List (Word r Q)) (pairs : List (I × I))
    (indices : List (V ⊕ E)) (heads s M : ℕ) : ℕ :=
  (heads*s)^2*(pairs.length*alphabet.length^4)+8*(M*r)^2*(indices.length*ReadPlan.wordWidth r Q)

end Scores
end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentInputCall
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One-output physical calls in the assignment-input workspace. -/

namespace SubexponentialSAT.Subexp.AssignmentInputCall

open BitProgram StructuredCalls SubexpSetupStorage

abbrev call {r s l : ℕ} (p : Program r s l) (hr : r ≤ 16) (hs : s ≤ 10)
    (inputs : List (Fin 48 × Fin 48)) (q : Fin s) (dst : Fin 48) : Code :=
  isolated p (register hr) (stack hs) 31 work inputs [(stack hs q, dst)]

end SubexponentialSAT.Subexp.AssignmentInputCall

end OAI.Algorithms
end


