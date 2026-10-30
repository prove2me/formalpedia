-- Prove2me | Definitions.Def_OAIQ081S108
-- name    : OAIQ081S108
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:24:46.666101+00:00
-- url     : https://prove2.me/theorems/06b0c8dc-83f0-40f0-bc16-430d1a4b2600
-- title:
--   Definitions bundle OAIQ081S108 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 49 declarations of OpenAI's Lean: 33 definitions, 1 inductive type or structure and 15 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.countCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.countResult`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.prepared`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.retainCache`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.retainCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.retainedState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.returned`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.scatterCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.scatterResult`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.scatterSupport`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.stage`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.stageCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.support`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.trueCount`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.tupleInitialized`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeCacheProgram.cacheTapes`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeCacheProgram.constantResult`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeCacheProgram.finalState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeCacheProgram.localBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterNative.References.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.Metadata`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.WorkerEmpty`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank.unaryPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute.guardedWords`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.ClauseCount.caller`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.ClauseCount.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.ClauseCount.count`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.ClauseCount.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.addressedIndex`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryRank.rows`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.Index.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.Index.emitCurrent`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.Index.loop`, `OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterProgram.seq`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_LeafHeadSetupProgramRetain`, `SubexponentialSAT_SqrtLog_LeafHeadSetupProgramStorage`, `SubexponentialSAT_SqrtLog_LeafHeadSetupProgramSupport`, `SubexponentialSAT_SqrtLog_LeafHeadSetupProgramTuples`, `SubexponentialSAT_SqrtLog_LeafNodeCacheProgram`, `SubexponentialSAT_SqrtLog_LeafNodeCacheProgramFrames`, `SubexponentialSAT_SqrtLog_LeafOuterNativeReferences`, `SubexponentialSAT_SqrtLog_LeafOuterProgramParameters`, `SubexponentialSAT_SqrtLog_LeafParameterArithmeticSearch`, `SubexponentialSAT_SqrtLog_LeafParametersProgramBank`, `SubexponentialSAT_SqrtLog_LeafParametersProgramBankUnaryCopy`, `SubexponentialSAT_SqrtLog_LeafParametersProgramBanked`, `SubexponentialSAT_SqrtLog_LeafProgramClauseCount`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputAddressed`, `SubexponentialSAT_SqrtLog_ProducedQueryRankProvenance`, `SubexponentialSAT_SqrtLog_RowSelectionProgramIndex`, `SubexponentialSAT_SqrtLog_SetupCleanup`, `SubexponentialSAT_SqrtLog_SetupSearch`, `SubexponentialSAT_SubexpCRTOuterControl`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S083`, `OAIQ081S084`, `OAIQ081S085`, `OAIQ081S087`, `OAIQ081S089`, `OAIQ081S090`, `OAIQ081S091` and `OAIQ081S092` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S125`, `OAIQ081S126`, `OAIQ081S127`, `OAIQ081S136` and `OAIQ081S137`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.stageCost_linear`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeCacheProgram.local_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.clauseCount_eval`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.stageCost_linear`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeCacheProgram.local_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.clauseCount_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Interval.at_eval`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S083
import Definitions.Def_OAIQ081S084
import Definitions.Def_OAIQ081S085
import Definitions.Def_OAIQ081S087
import Definitions.Def_OAIQ081S089
import Definitions.Def_OAIQ081S090
import Definitions.Def_OAIQ081S091
import Definitions.Def_OAIQ081S092

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramStorage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid, isolated service calls in the leaf head-builder's reserved bank.
The entire local service bank is moved to340..627. In particular a matrix
entry bank cannot overwrite the persistent ring tables below340. -/
noncomputable section

namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage

abbrev stage {r s l : ℕ} (p : Program r s l) (reg : Fin r → Fin 16)
    (hs : s ≤ 288) (ins : List (Fin 768 × Fin s)) (outs : List (Fin s × Fin 768)) : Code :=
  isolated p reg (workPort hs) temporary (workPorts hs) (inputCopies hs ins) (outputCopies hs outs)

def prepared {s : ℕ} (hs : s ≤ 288) (ins : List (Fin 768 × Fin s)) (a : Data) : Data :=
  prepareState temporary (workPorts hs) (inputCopies hs ins) a
def returned {r s : ℕ} (reg : Fin r → Fin 16) (hs : s ≤ 288)
    (ins : List (Fin 768 × Fin s)) (outs : List (Fin s × Fin 768))
    (a : Data) (b : State r s) : Data :=
  finishState (workPorts hs) (outputCopies hs outs)
    (embedState reg (workPort hs) (prepared hs ins a) b)
def stageCost {r s : ℕ} (reg : Fin r → Fin 16) (hs : s ≤ 288)
    (ins : List (Fin 768 × Fin s)) (outs : List (Fin s × Fin 768))
    (a : Data) (b : State r s) (t : ℕ) : ℕ :=
  prepareCost temporary (workPorts hs) (inputCopies hs ins) a +
    (t + finishCost (workPorts hs) (outputCopies hs outs)
      (embedState reg (workPort hs) (prepared hs ins a) b))

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramRetain
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Preserve the paid interpolation cache for the later source-polynomial
worker. These three copies are charged before the private head bank is cleared. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage

def retainCache : Code := .seq (clearMany retainedPorts) (copyMany temporary retainedCopies)
def retainedState (a : Data) : Data := copyManyState retainedCopies (clearManyState retainedPorts a)
def retainCost (a : Data) : ℕ := clearManyCost retainedPorts a +
  copyManyCost retainedCopies (clearManyState retainedPorts a)

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramSupport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Construct the full ambient head-support mask from the IDs actually
selected. A low-variable mask alone is not a head-support mask. -/
noncomputable section

namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def trueCount : Code := stage PackingHeadProgramPrepareCount.program countRegs (by decide)
  countInputs countOutputs

def countResult (a : Data) : Data := returned countRegs (by decide) countInputs countOutputs a
  (PackingHeadProgramPrepareCount.state (fun _ => false) [] (List.replicate (a.stacks 651).length true))
def countCost (a : Data) : ℕ := stageCost countRegs (by decide) countInputs countOutputs a
  (PackingHeadProgramPrepareCount.state (fun _ => false) [] (List.replicate (a.stacks 651).length true))
  (4*(a.stacks 651).length+4)

def scatterSupport : Code := stage HeadScatterProgram.program scatterRegs (by decide)
  scatterInputs scatterOutputs

def scatterResult (a : Data) (regs : Fin 8 → Bool) (n : ℕ) (js : List ℕ) : Data :=
  returned scatterRegs (by decide) scatterInputs scatterOutputs a
    (HeadScatterProgram.result regs js (List.replicate js.length true) n)
def scatterCost (a : Data) (regs : Fin 8 → Bool) (n : ℕ) (js : List ℕ) : ℕ :=
  stageCost scatterRegs (by decide) scatterInputs scatterOutputs a
    (HeadScatterProgram.result regs js (List.replicate js.length true) n)
    (100*(n+1)*(js.length+1))

def support : Code := .seq trueCount scatterSupport

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramTuples
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The attained-bucket Cartesian table is a physical persistent stream.
Each append and the final nested moments serialization is a real paid call. -/
noncomputable section

namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def tupleInitialized (a : Data) : Data :=
  ⟨Function.update a.regs 0 false,
    Function.update (Function.update a.stacks 660 ([true,false,false]++a.stacks 660))
      665 (false::a.stacks 665)⟩

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafNodeCacheProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical staging of node-local cached ring words. The ambient source tapes
and ring masters are copied, never consumed. The two raw-one caches are built
by the checked sparse-constant program, rather than supplied semantically. -/
namespace SubexponentialSAT.SqrtLog.LeafNodeCacheProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage
attribute [local simp] Fin.coe_ofNat_eq_mod

noncomputable def constantResult (a : LocalData) (rr : Fin 8 → Bool) (word : List Bool) : LocalData :=
  ⟨Function.extend constantRegisters rr a.regs,constantTapes a.stacks word⟩

noncomputable def finalState (a : LocalData) (rr : Fin 8 → Bool) (word : List Bool) : LocalData :=
  clearState 345 (copyManyState [(345,69),(345,167)] (constantResult a rr word))

def localBudget (a : LocalData) := copyManyCost copies a +
  (8*(a.stacks 128).length+7*(a.stacks 207).length+31) + 16*(rawOne a.stacks).length+13


end SubexponentialSAT.SqrtLog.LeafNodeCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafNodeCacheProgramFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafNodeCacheProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage
attribute [local simp] Fin.coe_ofNat_eq_mod

def cacheTapes (a : LocalData) : Fin 768 → List Bool :=
  Function.update (Function.update (copyManyState directCopies a).stacks 69 (rawOne a.stacks))
    167 (rawOne a.stacks)

end SubexponentialSAT.SqrtLog.LeafNodeCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RowSelectionProgramIndex
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime, self-delimiting natural-index alphabet. The range control is the
existing unary loop, with one delimiter inserted in each emitted payload. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgram.Index
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpIncidencePlanPrimitives

abbrev emitCurrent : Cmd 10 10 :=
  .seq (copy 5 1 3)
    (.seq (Subexp.TupleProgram.pushConst 1 0 false)
      (.seq SubexpUnaryRangeProgram.setSelected (.seq emit (increment 5))))

abbrev loop : Cmd 10 10 := .while 9
  (.seq SubexpUnaryRangeProgram.pop (.seq emitCurrent SubexpUnaryRangeProgram.peek))
abbrev command : Cmd 10 10 := .seq SubexpUnaryRangeProgram.peek loop

end SubexponentialSAT.SqrtLog.RowSelectionProgram.Index

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafOuterNativeReferences
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The marked-reference stream is generated by a fixed program from the binary
clause count. Both binary-to-unary expansion and the quadratic framed stream
emission are part of the measured run. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterNative.References
open SubexponentialSAT BitProgram StructuredCalls

abbrev command : Cmd 10 10 := .seq expand
  (.seq (Subexp.TupleProgram.pushConst 7 0 false)
    (.seq RowSelectionProgram.Index.command (.call (StackRoutines.clearProgram 5 0 1))))

end SubexponentialSAT.SqrtLog.LeafOuterNative.References

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SetupSearch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Setup.Search

open BitProgram StructuredCalls
open CounterPrograms (value ripple)

/-- The guard is an actual finite subroutine call; all caller stacks are framed. -/
theorem guard_eval (d : Data)
    (hempty : ∀ i : Fin 12, 3 ≤ i.val → d.stacks (guardPorts i) = []) :
    ∃ t e, Eval guard t d e ∧ e.stacks = d.stacks ∧
      (e.regs 0 = true ↔ value (d.stacks 0)^2 * value (d.stacks 1) ≤
        value (d.stacks 2)) ∧
      t ≤ 10001 * ((d.stacks 0).length + (d.stacks 1).length +
        (d.stacks 2).length + 1)^2 := by
  let a := projectState id guardPorts d
  obtain ⟨t,b,he,hs,hf,ht⟩ := Guard.command_eval a hempty
  let e := embedState id guardPorts d b
  have hh := eval_call_lifted (compiled Guard.command 0 0) id guardPorts d
    Function.injective_id guardPorts.injective (compiled_halt_trace he 0 0)
  rw [embedState_project id guardPorts d Function.injective_id guardPorts.injective] at hh
  refine ⟨t+1,e,hh,?_,?_,?_⟩
  · funext i
    by_cases hi : ∃ j, guardPorts j = i
    · obtain ⟨j,rfl⟩ := hi
      rw [show e.stacks (guardPorts j) = b.stacks j from
        embedState_stack id guardPorts d b guardPorts.injective j, hs]
      rfl
    · exact embedState_stack_frame id guardPorts d b i hi
  · change (embedState id guardPorts d b).regs 0 = true ↔ _
    rw [show (embedState id guardPorts d b).regs 0 = b.regs 0 from
      embedState_register id guardPorts d b Function.injective_id 0]
    change b.regs 0 = true ↔
      BinaryArithmetic.toNat (d.stacks (guardPorts 0))^2 *
        BinaryArithmetic.toNat (d.stacks (guardPorts 1)) ≤
          BinaryArithmetic.toNat (d.stacks (guardPorts 2)) at hf
    have h0 : guardPorts 0 = 0 := rfl
    have h1 : guardPorts 1 = 1 := rfl
    have h2 : guardPorts 2 = 2 := rfl
    simpa only [h0, h1, h2, SubexpParameterProgram.value_eq_toNat] using hf
  · change t ≤ 10000 * ((d.stacks 0).length + (d.stacks 1).length +
        (d.stacks 2).length + 1)^2 at ht
    have hp : 0 < ((d.stacks 0).length + (d.stacks 1).length +
        (d.stacks 2).length + 1)^2 := Nat.pow_pos (by omega)
    omega

/-- Saving the current candidate overwrites only the answer port. -/
theorem save_eval (d : Data) (hs : d.stacks 11 = []) :
    ∃ e, Eval save (2*(d.stacks 12).length + 3 + (7*(d.stacks 0).length+5)) d e ∧
      e.stacks = Function.update d.stacks 12 (d.stacks 0) := by
  let a : Data := ⟨readRegs d.regs 0 1 none, Function.update d.stacks 12 []⟩
  have h1 := ArithmeticExpressionSupport.clear_eval 12 d
  change Eval _ _ d a at h1
  have h2 := ArithmeticCalls.copyAt_eval (0 : Fin 15) 12 11 a
    (by decide) (by decide) (by decide) (by simp [a]) (by simp [a,hs])
  refine ⟨ArithmeticCalls.afterCopy 0 12 a, h1.seq (by simpa [a] using h2), ?_⟩
  simp [ArithmeticCalls.afterCopy, a]

/-- One real callback performs one candidate test. -/
theorem body_eval (d : Data)
    (hempty : ∀ i : Fin 12, 3 ≤ i.val → d.stacks (guardPorts i) = []) :
    ∃ t e, Eval body t d e ∧
      e.stacks 0 = ripple true (d.stacks 0) ∧
      e.stacks 12 = (if (value (d.stacks 0)+1)^2 * value (d.stacks 1) ≤
        value (d.stacks 2) then ripple true (d.stacks 0) else d.stacks 12) ∧
      (∀ i : Fin 15, i ≠ 0 → i ≠ 12 → e.stacks i = d.stacks i) ∧
      t ≤ 20000 * ((d.stacks 0).length + (d.stacks 1).length +
        (d.stacks 2).length + (d.stacks 12).length + 2)^2 := by
  have hs : d.stacks 11 = [] := hempty 11 (by decide)
  let a := CeilingDivisionPrograms.incrementResult incrementPorts d
  have h1 : Eval _ _ d a := CeilingDivisionPrograms.increment_eval incrementPorts d hs
  have ha : a.stacks 0 = ripple true (d.stacks 0) :=
    CeilingDivisionPrograms.increment_counter incrementPorts d
  have haf : ∀ i : Fin 15, i ≠ 0 → a.stacks i = d.stacks i := by
    intro i hi
    exact CeilingDivisionPrograms.increment_other incrementPorts d hs i hi
  have hea : ∀ i : Fin 12, 3 ≤ i.val → a.stacks (guardPorts i) = [] := by
    intro i hi
    rw [haf (guardPorts i) (by
      intro h
      have hv := congrArg Fin.val h
      change i.val = 0 at hv
      omega)]
    exact hempty i hi
  obtain ⟨tg,b,hg,hbs,hbf,hgt⟩ := guard_eval a hea
  have hb0 : b.stacks 0 = ripple true (d.stacks 0) := by rw [hbs,ha]
  have hb12 : b.stacks 12 = d.stacks 12 := by rw [hbs,haf 12 (by decide)]
  have hbf' : b.regs 0 = true ↔ (value (d.stacks 0)+1)^2 * value (d.stacks 1) ≤
      value (d.stacks 2) := by
    simpa [ha, haf 1 (by decide), haf 2 (by decide), CounterPrograms.value_increment] using hbf
  have hlen := CounterPrograms.ripple_length_le true (d.stacks 0)
  have hrip := CounterPrograms.rippleCost_le true (d.stacks 0)
  have hgt' : tg ≤ 10001 * ((ripple true (d.stacks 0)).length +
      (d.stacks 1).length + (d.stacks 2).length + 1)^2 := by
    simpa [ha, haf 1 (by decide), haf 2 (by decide)] using hgt
  set B := (d.stacks 0).length + (d.stacks 1).length +
    (d.stacks 2).length + (d.stacks 12).length + 2
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hb2 : B ≤ B^2 := by nlinarith
  have hgtCommon : tg ≤ 10001*B^2 := by
    apply hgt'.trans
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    dsimp [B]
    omega
  by_cases hc : (value (d.stacks 0)+1)^2 * value (d.stacks 1) ≤ value (d.stacks 2)
  · obtain ⟨e,he,hes⟩ := save_eval b (by rw [hbs,haf 11 (by decide)]; exact hs)
    refine ⟨_,e,h1.seq (hg.seq (.ite_true (hbf'.2 hc) he)),?_,?_,?_,?_⟩
    · simp [hes,hb0]
    · simp [hes,hb0,hc]
    · intro i hi0 hi12
      simp only [hes, Function.update_of_ne hi12, hbs]
      exact haf i hi0
    · simp only [hb0,hb12]
      omega
  · have hf : b.regs 0 = false := by
      cases h : b.regs 0 <;> simp_all
    refine ⟨_,b,h1.seq (hg.seq (.ite_false hf (.base (.skip _)))),hb0,?_,?_,?_⟩
    · simp [hc,hb12]
    · intro i hi0 _; rw [hbs]; exact haf i hi0
    · simp only []
      omega

end SubexponentialSAT.SqrtLog.Setup.Search

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParameterArithmeticSearch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Generic correctness for the actual tested square-times-coefficient search.
The command is exactly `Setup.Search.command`; there is no arithmetic oracle. -/
namespace SubexponentialSAT.SqrtLog.LeafParameterArithmetic.Search

open BitProgram StructuredCalls
open CounterPrograms (value)
open Setup.Search (Data guardPorts loopPorts body command iterationBound)

theorem invariant_stable (target : ℕ) (initial : _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Setup.Search.Data) :
    CounterForPrograms.FrameStable loopPorts (Invariant target initial) := by
  intro i a b hab hi
  rcases hi with ⟨hv,hs,hl,hl',hf⟩
  have hb0 := hab 0 (by decide) (by decide)
  have hb12 := hab 12 (by decide) (by decide)
  refine ⟨by simpa [← hb0] using hv, by simpa [← hb12] using hs,
    by simpa [← hb0] using hl, by simpa [← hb12] using hl', ?_⟩
  intro j h0 h12 h13 h14
  rw [← hab j h13 h14]
  exact hf j h0 h12 h13 h14

theorem body_spec (target : ℕ) (initial : _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Setup.Search.Data)
    (htarget : ∀ a, a ≤ target ↔
      a^2 * value (initial.stacks 1) ≤ value (initial.stacks 2))
    (hempty : ∀ i : Fin 12, 3 ≤ i.val → initial.stacks (guardPorts i) = []) :
    CounterForPrograms.BodySpec loopPorts body (Invariant target initial)
      (iterationBound initial) := by
  intro i d hi hscratch _
  rcases hi with ⟨hv,hs,hl,hl',hf⟩
  have hframe1 := hf 1 (by decide) (by decide) (by decide) (by decide)
  have hframe2 := hf 2 (by decide) (by decide) (by decide) (by decide)
  have hdempty : ∀ j : Fin 12, 3 ≤ j.val → d.stacks (guardPorts j) = [] := by
    intro j hj
    rw [hf (guardPorts j)]
    · exact hempty j hj
    · intro h
      have hv := congrArg Fin.val h
      change j.val = 0 at hv
      omega
    · intro h
      have hv := congrArg Fin.val h
      change j.val = 12 at hv
      omega
    · intro h
      have hv := congrArg Fin.val h
      change j.val = 13 at hv
      omega
    · intro h
      have hv := congrArg Fin.val h
      change j.val = 14 at hv
      omega
  obtain ⟨t,e,he,he0,he12,hef,ht⟩ := Setup.Search.body_eval d hdempty
  refine ⟨t,e,?_,he,hef 13 (by decide) (by decide),?_,?_⟩
  · dsimp [iterationBound]
    rw [hframe1,hframe2] at ht
    have harg : (d.stacks 0).length + (initial.stacks 1).length +
        (initial.stacks 2).length + (d.stacks 12).length + 2 ≤
        i + (initial.stacks 1).length + (initial.stacks 2).length + i + 2 := by omega
    exact ht.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left harg 2))
  · exact (hef 14 (by decide) (by decide)).trans hscratch
  · refine ⟨by rw [he0,CounterPrograms.value_increment,hv],?_,?_,?_,?_⟩
    · rw [he12,hv,hframe1,hframe2]
      by_cases h : i+1 ≤ target
      · rw [ite_eq_left ((htarget (i+1)).1 h)]
        rw [CounterPrograms.value_increment,hv,Nat.min_eq_left h]
      · rw [ite_eq_right (fun hh => h ((htarget (i+1)).2 hh)),hs]
        omega
    · rw [he0]
      exact (CounterPrograms.ripple_length_le true (d.stacks 0)).trans (by omega)
    · rw [he12]
      split
      · exact (CounterPrograms.ripple_length_le true (d.stacks 0)).trans (by omega)
      · omega
    · intro j h0 h12 h13 h14
      exact (hef j h0 h12).trans (hf j h0 h12 h13 h14)

/-- Fully concrete arithmetic search: input 1 is a positive coefficient,
input 2 the bound, 13 the counted fuel. Every tested candidate is charged. -/
theorem command_eval (d : _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Setup.Search.Data)
    (hc : 0 < value (d.stacks 1))
    (hfuel : root (value (d.stacks 1)) (value (d.stacks 2)) ≤ value (d.stacks 13))
    (hzero : d.stacks 0 = []) (hanswer : d.stacks 12 = [])
    (hscratch : d.stacks 14 = [])
    (hempty : ∀ i : Fin 12, 3 ≤ i.val → d.stacks (guardPorts i) = []) :
    ∃ t e, Eval command t d e ∧
      value (e.stacks 12) = root (value (d.stacks 1)) (value (d.stacks 2)) ∧
      (e.stacks 0).length ≤ value (d.stacks 13) ∧
      (e.stacks 12).length ≤ value (d.stacks 13) ∧
      (e.stacks 13).length = (d.stacks 13).length ∧ e.stacks 14 = [] ∧
      (∀ j : Fin 15, j ≠ 0 → j ≠ 12 → j ≠ 13 → j ≠ 14 → e.stacks j = d.stacks j) ∧
      t ≤ value (d.stacks 13) * iterationBound d (value (d.stacks 13)) +
        (value (d.stacks 13)+1) * (16*(d.stacks 13).length+16) := by
  let target := root (value (d.stacks 1)) (value (d.stacks 2))
  have hi : Invariant target d 0 d := by
    refine ⟨by simp [hzero],by simp [hanswer],
      by simp [hzero],by simp [hanswer],?_⟩
    intro j _ _ _ _; rfl
  obtain ⟨t,e,he,hei,_,hlen,hsc,ht⟩ := CounterForPrograms.for_correct loopPorts body
    (Invariant target d) (iterationBound d) (invariant_stable target d)
    (body_spec target d (fun a => le_root_iff _ _ a hc) hempty) d hscratch hi
  change Invariant target d (value (d.stacks 13)) e at hei
  change t ≤ CounterForPrograms.budgetSum (iterationBound d) 0 (value (d.stacks 13)) +
    (value (d.stacks 13)+1)*(16*(d.stacks 13).length+16) at ht
  rcases hei with ⟨_,hv,hl0,hl12,hframe⟩
  refine ⟨t,e,he,?_,hl0,hl12,hlen,hsc,hframe,?_⟩
  · dsimp [target] at hv
    simpa only [Nat.min_eq_right hfuel] using hv
  · apply ht.trans
    apply Nat.add_le_add_right
    apply CounterForPrograms.budgetSum_le
    intro i _ hil
    dsimp [iterationBound]
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    omega

end SubexponentialSAT.SqrtLog.LeafParameterArithmetic.Search

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SetupCleanup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Setup.Cleanup

open BitProgram StructuredCalls

theorem clearMany_eval {S : ℕ} (ports : List (Fin S)) (d : Data S) (B : ℕ)
    (hb : ∀ i, (d.stacks i).length ≤ B) :
    ∃ t e, Eval (clearMany ports) t d e ∧
      (∀ i, e.stacks i = if i ∈ ports then [] else d.stacks i) ∧
      t ≤ ports.length*(2*B+3) := by
  induction ports generalizing d with
  | nil => exact ⟨0,d,.base (.skip _),by simp,by simp⟩
  | cons p ps ih =>
    let a : Data S := ⟨readRegs d.regs 0 1 none,Function.update d.stacks p []⟩
    have h1 : Eval (ArithmeticExpressionSupport.clearCmd p) (2*(d.stacks p).length+3) d a :=
      ArithmeticExpressionSupport.clear_eval p d
    have ha : ∀ i, (a.stacks i).length ≤ B := by
      intro i; by_cases hi : i=p
      · subst i; simp [a]
      · simpa [a,hi] using hb i
    obtain ⟨t,e,he,hs,ht⟩ := ih a ha
    refine ⟨_,e,h1.seq he,?_,?_⟩
    · intro i
      rw [hs]
      by_cases hip : i=p
      · subst i; by_cases his : p∈ps <;> simp [his,a]
      · by_cases his : i∈ps <;> simp [hip,his,a]
    · have hp := hb p
      simp only [List.length_cons]
      nlinarith

end SubexponentialSAT.SqrtLog.Setup.Cleanup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramBank
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank

open BitProgram StructuredCalls BinaryArithmetic

theorem state_work (r : Regs) (w : Words) (i : Fin 77) (hi : 64 ≤ i.val) :
    (state r w).stacks i = [] := by simp [state, show ¬ i.val < 64 by omega]

theorem state_update (r rf : Regs) (w : Words) (i : Fin 64) (word : List Bool) :
    (⟨rf, Function.update (state r w).stacks (port i) word⟩ : Data) =
      state rf (Function.update w i word) := by
  apply CounterForPrograms.data_ext <;> try rfl
  funext j
  by_cases hj : j.val < 64
  · simp [state, Function.update_apply, port, hj, Fin.ext_iff]
  · have hji : j ≠ port i := by
      intro he
      have he' : j.val = i.val := congrArg (fun x : Fin 77 => x.val) he
      have hi := i.isLt
      omega
    simp [state, Function.update_apply, hj, hji]


end SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafOuterProgramParameters
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual outer-leaf parameter stage: input copies, native arithmetic,
output copies, and complete worker cleanup, with every command charged. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram
open SubexponentialSAT BitProgram StructuredCalls BinaryArithmetic
open LeafParametersProgram.Bank

/-- All 768 reusable worker stacks are empty. -/
def WorkerEmpty (a : Data) : Prop := ∀ i : Fin 768, a.stacks (workerStack i) = []

/-- Persisted search metadata. The seven indexed values are D,t,tD,d,r,rD,N. -/
structure Metadata (m B : ℕ) (a : Data) : Prop where
  q : BinaryArithmetic.toNat (a.stacks 800) = SparseCode.gapDenom m B
  binary : ∀ j, BinaryArithmetic.toNat (a.stacks (binaryMetadataPort j)) = CodeParametersProgram.parameterValues m B j
  unary : ∀ j, a.stacks (unaryMetadataPort j) =
    List.replicate (CodeParametersProgram.parameterValues m B j) true

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramBankUnaryCopy
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank

open BitProgram StructuredCalls BinaryArithmetic

attribute [local simp] Fin.coe_ofNat_eq_mod

def unaryPorts (a o : Fin 64) : Fin 14 → Fin 77 :=
  ![port a,port o,64,65,66,67,68,69,70,71,72,73,74,75]

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramBanked
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute


open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

def guardedWords (w : Words) : Words := fun a => if a.val < 44 then w a else []

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramClauseCount
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Count the clauses in the actual emitted leaf. Both the preserving record
scan and unary-to-binary conversion are fixed native programs. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.ClauseCount

open SubexponentialSAT BitProgram StructuredCalls

abbrev count : Cmd 8 16 := liftCommand SubexpScopeCountSetup.countCommand 1 2 id (Fin.castAdd 1)
abbrev command : Cmd 8 16 := .seq count convert

def program := compiled command 1 15

abbrev caller : Cmd 40 896 :=
  .call (ProgramLinking.liftProgram program callerRegisters callerStacks)

end SubexponentialSAT.SqrtLog.LeafProgram.ClauseCount

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputAddressed
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The saved stream contains word addresses, so its second component is the
ambient-offset factor address. Incidence positions and owner fibers are unchanged. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput
open SubexponentialSAT.Subexp

@[simp] theorem addressedEntries_length (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :
    (addressedEntries scopes n mask).length = (Semantics.nativeEntries scopes mask).length := by
  simp [addressedEntries]

/-- Equality transport of incidence positions preserves their numeric indices. -/
def addressedIndex (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :
    Fin (addressedEntries scopes n mask).length ≃ Semantics.Incidences scopes mask where
  toFun i := ⟨i.val,by simpa only [addressedEntries_length] using i.isLt⟩
  invFun i := ⟨i.val,by simpa only [addressedEntries_length] using i.isLt⟩
  left_inv i := Fin.ext rfl
  right_inv i := Fin.ext rfl

@[simp] theorem addressedIndex_val (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (i : Fin (addressedEntries scopes n mask).length) :
    (addressedIndex scopes n mask i).val = i.val := rfl

@[simp] theorem addressedEntries_get (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (i : Fin (addressedEntries scopes n mask).length) :
    (addressedEntries scopes n mask).get i =
      (let p := (Semantics.nativeEntries scopes mask).get (addressedIndex scopes n mask i)
       (p.1,n+p.2)) := by
  change
    (List.map (fun p => (p.1,n+p.2)) (Semantics.nativeEntries scopes mask))[i.val] =
      (let p := (Semantics.nativeEntries scopes mask)[(addressedIndex scopes n mask i).val]
       (p.1,n+p.2))
  rw [List.getElem_map]
  rfl

@[simp] theorem addressedEntries_owners (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :
    (addressedEntries scopes n mask).map Prod.fst =
      (Semantics.nativeEntries scopes mask).map Prod.fst := by
  simp [addressedEntries,List.map_map]

theorem fiberIndices_shift (ps : List (ℕ × ℕ)) (n query start : ℕ) :
    LayoutOwnerFiberProgram.fiberIndices query start (ps.map (fun p => (p.1,n+p.2))) =
      LayoutOwnerFiberProgram.fiberIndices query start ps := by
  induction ps generalizing start with
  | nil => rfl
  | cons p ps ih => simp [LayoutOwnerFiberProgram.fiberIndices,ih]

theorem addressedEntries_fibers (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (query start : ℕ) :
    LayoutOwnerFiberProgram.fiberIndices query start (addressedEntries scopes n mask) =
      LayoutOwnerFiberProgram.fiberIndices query start (Semantics.nativeEntries scopes mask) :=
  fiberIndices_shift _ n query start

end SubexponentialSAT.SqrtLog.PackingIncidenceInput

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

def rows (p : Problem) (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) :=
  (p.words a tail).map SubexponentialSAT.Subexp.ReadPlan.encodeWord

end SubexponentialSAT.SqrtLog.ProducedQueryRank

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpCRTOuterControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete tape operations and traversal assertions for the outer CRT.
All operations in this module are fixed finite programs. Arithmetic is supplied
by the separately defined concrete CRT service commands. -/

namespace SubexponentialSAT.SubexpCRTOuterProgram

open BitProgram StructuredCalls SubexpScanPrimitives

abbrev seq (a b : Code) : Code := .seq a b

end SubexponentialSAT.SubexpCRTOuterProgram

end OAI.Algorithms
end


