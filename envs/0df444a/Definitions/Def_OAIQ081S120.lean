-- Prove2me | Definitions.Def_OAIQ081S120
-- name    : OAIQ081S120
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:32:21.567015+00:00
-- url     : https://prove2.me/theorems/3df2c76d-5cfa-4e8f-9583-8f2fb48bac5d
-- title:
--   Definitions bundle OAIQ081S120 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 36 declarations of OpenAI's Lean: 23 definitions and 13 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar.baseCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar.initializeAll`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar.initializePool`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scan.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scan.copyAndScan`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scan.ports`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scan.tableCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.boot`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.finishCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.modulusCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.nativeTable`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IntegerRingLiftProgram.ModelCode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IntegerRingLiftProgram.bitPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IntegerRingLiftProgram.bitStep`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IntegerRingLiftProgram.modelTable`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.saved`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Field.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Field.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.NativeOverlay.Code`, `OAI.Algorithms.SubexponentialSAT.SubexpBlockParameterProgram.powerCmd`, `OAI.Algorithms.SubexponentialSAT.SubexpBlockParameterProgram.powerPorts`, `OAI.Algorithms.SubexponentialSAT.UnaryForPrograms.BodySpec`, `OAI.Algorithms.SubexponentialSAT.UnaryForPrograms.FrameStable`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_HighQueryAdapter`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramArrayStage`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramArrays`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramBoot`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramEncoded`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramFinish`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramModulus`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalar`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarBase`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarInit`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScan`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramTableRun`, `SubexponentialSAT_SqrtLog_IdempotentProgramCanonical`, `SubexponentialSAT_SqrtLog_IdempotentProgramConstants`, `SubexponentialSAT_SqrtLog_IntegerRingLiftProgram`, `SubexponentialSAT_SqrtLog_IntegerRingLiftProgramModel`, `SubexponentialSAT_SqrtLog_LayoutBinomialProgramCell`, `SubexponentialSAT_SqrtLog_LeafParametersProgramField`, `SubexponentialSAT_SubexpBlockParameterProgram`, `SubexponentialSAT_UnaryForPrograms`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S100`, `OAIQ081S101`, `OAIQ081S102`, `OAIQ081S103` and `OAIQ081S104` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S140`, `OAIQ081S141`, `OAIQ081S142`, `OAIQ081S143`, `OAIQ081S144` and `OAIQ081S151`; the proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.Execution.HashParameters.command_eval`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S100
import Definitions.Def_OAIQ081S101
import Definitions.Def_OAIQ081S102
import Definitions.Def_OAIQ081S103
import Definitions.Def_OAIQ081S104

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_UnaryForPrograms
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control unary-counted callbacks

The counter is a Boolean stack whose length is the iteration count. Its bits
are ignored. The controller pops before each callback and tests the presence
flag; callbacks preserve the remaining counter tail and may clobber all
registers. Every observation contains an actual callback evaluation.
-/

namespace SubexponentialSAT.UnaryForPrograms

open BitProgram StructuredProgram
open CounterForPrograms (budgetSum)

variable {R S : ℕ}

theorem popped_other (p : Ports R S) (d : Data R S) (j : Fin S) (hj : j ≠ p.counter) :
    (popped p d).stacks j = d.stacks j := by simp [popped, hj]

def FrameStable (p : Ports R S) (I : ℕ → Data R S → Prop) : Prop :=
  ∀ i a b, (∀ j, j ≠ p.counter → a.stacks j = b.stacks j) → I i a → I i b

abbrev BodySpec (p : Ports R S) (body : StructuredCalls.Cmd R S)
    (I : ℕ → Data R S → Prop) (cost : ℕ → ℕ) : Prop :=
  ∀ i d, I i d → ∃ n e, n ≤ cost i ∧ StructuredCalls.Eval body n d e ∧
    e.stacks p.counter = d.stacks p.counter ∧ I (i + 1) e

end SubexponentialSAT.UnaryForPrograms

end OAI.Algorithms
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

open OAI.Algorithms.SubexponentialSAT.StackRoutines

namespace NativeOverlay
open OAI.Algorithms.SubexponentialSAT.StackRoutines

abbrev Code := Cmd 40 896

end NativeOverlay


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramArrays
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Real allocation of the padded Newton arrays. Prefix coefficient words are
computed scalar cache entries; the zero suffix is generated by native copying
from one zero word and a runtime unary dimension. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

open BitProgram StructuredCalls SubexpScanPrimitives

theorem initialArray_eval (d : Data) (n : ℕ)
    (hd : d.stacks 37 = List.replicate (n+3) true)
    (h1 : d.stacks 1 = []) (h2 : d.stacks 2 = []) (h32 : d.stacks 32 = []) :
    ∃ cost rf, cost = 7*(n+3)+5+3+(n*(7*(d.stacks 17).length+7)+6) +
      (7*(d.stacks 27).length+5+(7*(d.stacks 31).length+5+
        (7*(d.stacks 30).length+5))) ∧
      Eval initialArray cost d ⟨rf,Function.update d.stacks 32 (initialBits d n)⟩ := by
  obtain ⟨ra,ha⟩ := paddedZeros_eval d 32 3 n hd h1 h2 (by decide) (by decide) (by decide)
  let a : Data := ⟨ra,Function.update d.stacks 32
    (Subexp.BlockCopyProgram.copies n (d.stacks 17))⟩
  have ha' : Eval (paddedZeros 32 3)
      (7*(n+3)+5+3+(n*(7*(d.stacks 17).length+7)+6)) d a := by
    simpa [a,h32] using ha
  have hb := copySources_eval 32 [27,31,30] a (by decide)
    (by simp [a,h2]) (by simp)
  have hs : (copiedSources 32 [27,31,30] a).stacks =
      Function.update d.stacks 32 (initialBits d n) := by
    simp [copiedSources,afterCopy,StackRoutines.copyStacks,a,initialBits,
      Function.update_idem,List.append_assoc]
  have hf : copiedSources 32 [27,31,30] a =
      ⟨(copiedSources 32 [27,31,30] a).regs,Function.update d.stacks 32 (initialBits d n)⟩ :=
    state_ext rfl hs
  have he := ha'.seq hb
  rw [hf] at he
  refine ⟨_,(copiedSources 32 [27,31,30] a).regs,rfl,?_⟩
  simpa [initialArray,copiedSourcesCost,afterCopy,StackRoutines.copyStacks,a] using he

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramArrayStage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

open BitProgram StructuredCalls

theorem arrayStage_eval (d : Data) (t B : ℕ) (ht : 0 < t)
    (hd : d.stacks 37 = List.replicate (3*t) true)
    (h1 : d.stacks 1 = []) (h2 : d.stacks 2 = [])
    (h32 : d.stacks 32 = []) (h33 : d.stacks 33 = [])
    (h34 : d.stacks 34 = []) (h35 : d.stacks 35 = []) (h36 : d.stacks 36 = [])
    (hz : (d.stacks 17).length=B) (hu : (d.stacks 27).length=B)
    (hm : (d.stacks 28).length=B) (hx : (d.stacks 30).length=B)
    (hy : (d.stacks 31).length=B) :
    ∃ cost rf, cost ≤ 500*(3*t+1)*(B+1) ∧
      Eval arrayStage cost d ⟨rf,arrayStacks d.stacks t⟩ := by
  have hd3 : 3*t-3+3=3*t := by omega
  have hd1 : 3*t-1+1=3*t := by omega
  obtain ⟨na,ra,hna,ha⟩ := initialArray_eval d (3*t-3) (by simpa only [hd3] using hd) h1 h2 h32
  let a : Data := ⟨ra,Function.update d.stacks 32 (initialBits d (3*t-3))⟩
  obtain ⟨rb,hb⟩ := cloneInitial_eval a (by simp [a,h2]) (by simp [a,h33])
    (by simp [a,h34]) (by simp [a,h35])
  let b : Data := ⟨rb,Function.update (Function.update (Function.update a.stacks
    33 (a.stacks 32)) 34 (a.stacks 32)) 35 (a.stacks 32)⟩
  obtain ⟨rc,hc⟩ := negativeOneArray_eval b (3*t-1)
    (by simpa [b,a,hd1] using hd) (by simp [b,a,h1]) (by simp [b,a,h2]) (by simp [b,a,h36])
  have he := ha.seq (hb.seq hc)
  have hlen : (a.stacks 32).length = 3*t*B := by
    simp only [a,Function.update_same,initialBits,List.length_append,
      Subexp.BlockCopyProgram.copies_length,hx,hy,hu,hz]
    calc
      _ = ((3*t-3)+3)*B := by ring
      _ = _ := by rw [hd3]
  refine ⟨na+((21*(a.stacks 32).length+15)+
    (7*(3*t-1+1)+5+1+((3*t-1)*(7*(b.stacks 17).length+7)+6)+
      (7*(b.stacks 28).length+5))),rc,?_,?_⟩
  · rw [hna,hlen]
    simp only [b,a,Function.update_of_ne (by decide : (17:Fin 41)≠35),
      Function.update_of_ne (by decide : (17:Fin 41)≠34),
      Function.update_of_ne (by decide : (17:Fin 41)≠33),
      Function.update_of_ne (by decide : (17:Fin 41)≠32),
      Function.update_of_ne (by decide : (28:Fin 41)≠35),
      Function.update_of_ne (by decide : (28:Fin 41)≠34),
      Function.update_of_ne (by decide : (28:Fin 41)≠33),
      Function.update_of_ne (by decide : (28:Fin 41)≠32),hz,hu,hm,hx,hy,hd1,hd3]
    nlinarith [Nat.mul_le_mul_right (7*B+7) (Nat.sub_le (3*t) 3),
      Nat.mul_le_mul_right (7*B+7) (Nat.sub_le (3*t) 1)]
  · simpa [arrayStage,arrayStacks,b,a,initialBits] using he

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpBlockParameterProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual block-size and block-threshold arithmetic

The three input words contain `s`, `delta`, and `Q`.  The width `k` is part
of the fixed code.  Seven high stacks are a reusable empty work bank; the
fifteen low stacks retain inputs, constants, and computed intermediate words.
Every arithmetic operation below invokes a proved finite Boolean program.
-/

namespace SubexponentialSAT.SubexpBlockParameterProgram

open BitProgram StructuredCalls BinaryArithmetic

def powerPorts (a b o : Fin 15) (hoa : o ≠ a) (hob : o ≠ b) :
    PowerCalls.Ports 22 where
  base := port a
  exponent := port b
  out := port o
  work := work 7 (by decide)
  out_ne_base := by intro h; exact hoa ((Fin.castAdd_injective 15 7) h)
  out_ne_exponent := by intro h; exact hob ((Fin.castAdd_injective 15 7) h)
  work_ne_base := fun i => work_ne_port 7 (by decide) i a
  work_ne_exponent := fun i => work_ne_port 7 (by decide) i b
  work_ne_out := fun i => work_ne_port 7 (by decide) i o

abbrev powerCmd (a b o : Fin 15) (hoa : o ≠ a) (hob : o ≠ b) : Cmd 8 22 :=
  PowerCalls.powerAt (powerPorts a b o hoa hob)

theorem power_eval (r : Regs) (w : Words) (a b o : Fin 15)
    (hoa : o ≠ a) (hob : o ≠ b) (ho : w o = []) :
    ∃ t rf word,
      Eval (powerCmd a b o hoa hob) t (state r w)
        (state rf (Function.update w o word)) ∧
      BinaryArithmetic.toNat word = BinaryArithmetic.toNat (w a) ^ BinaryArithmetic.toNat (w b) ∧
      word.length ≤ 1 + BinaryArithmetic.toNat (w b) * (w a).length ∧
      t ≤ PowerPrograms.runtimeBound (w a) (w b) + 9 * (w b).length + 8 := by
  have hv : PowerCalls.Valid (powerPorts a b o hoa hob) (state r w) := by
    constructor
    · simpa only [powerPorts, state_port] using ho
    · intro i
      simpa only [powerPorts] using
        (state_work r w (work 7 (by decide) i) (by change 15 ≤ 15 + i.val; omega))
  obtain ⟨t, rf, word, he, hval, hlen, htime⟩ :=
    PowerCalls.powerAt_spec (powerPorts a b o hoa hob) (state r w) hv
  refine ⟨t, rf, word, ?_, ?_, ?_, ?_⟩
  · simpa only [powerCmd, powerPorts, state_update] using he
  · simpa only [powerPorts, state_port] using hval
  · simpa only [powerPorts, state_port] using hlen
  · simpa only [powerPorts, state_port] using htime

theorem load_eval (r : Regs) (w : Words) (o : Fin 15)
    (word : List Bool) (ho : w o = []) :
    ∃ rf, Eval (loadCmd o word) (2 * word.length) (state r w)
      (state rf (Function.update w o word)) := by
  obtain ⟨rf, he⟩ := ArithmeticExpressionSupport.pushWord_eval (port o) word (state r w)
  refine ⟨rf, ?_⟩
  simpa only [loadCmd, state_port, ho, List.append_nil, state_update] using he

end SubexponentialSAT.SubexpBlockParameterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramField
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed binary power program produces the runtime field cardinality.
Its exponent word is data; no extension degree is compiled into the control. -/
namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Field

open BitProgram StructuredCalls BinaryArithmetic
open SubexpBlockParameterProgram

/-- Input exponent on port 1; output 3^d on port 2. Port 0 is private constant
space and is restored empty; all other input words are preserved. -/
abbrev command : Cmd 8 22 :=
  .seq (loadCmd 0 [true,true])
    (.seq (powerCmd 0 1 2 (by decide) (by decide))
      (ArithmeticExpressionSupport.clearCmd (port 0)))

theorem command_eval (regs : Regs) (words : Words)
    (h0 : words 0 = []) (h2 : words 2 = []) :
    ∃ t rf word, Eval command t (state regs words) (state rf (Function.update words 2 word)) ∧
      BinaryArithmetic.toNat word = 3 ^ BinaryArithmetic.toNat (words 1) ∧ word.length ≤ 1 + 2 * BinaryArithmetic.toNat (words 1) ∧
      t ≤ bound (words 1) := by
  obtain ⟨r0,hload⟩ := load_eval regs words 0 [true,true] h0
  let w0 := Function.update words 0 [true,true]
  obtain ⟨tp,rp,wp,hpower,hv,hl,ht⟩ := power_eval r0 w0 0 1 2
    (by decide) (by decide) (by simp [w0,h2])
  let w1 := Function.update w0 2 wp
  let a := state rp w1
  have hclear := ArithmeticExpressionSupport.clear_eval (port 0) a
  let rf := readRegs a.regs 0 1 none
  have hs : (⟨rf,Function.update a.stacks (port 0) []⟩ : Data) =
      state rf (Function.update words 2 wp) := by
    rw [show a = state rp w1 by rfl,state_update]
    congr 1
    funext i
    by_cases hi : i = 0
    · subst i; simp [w1,w0,h0]
    · by_cases hi2 : i = 2
      · subst i; simp [w1,w0]
      · simp [w1,w0,hi,hi2]
  have hc : Eval (ArithmeticExpressionSupport.clearCmd (port 0)) 7 a
      (state rf (Function.update words 2 wp)) := by
    change Eval _ (2*(a.stacks (port 0)).length+3) a
      (⟨rf,Function.update a.stacks (port 0) []⟩ : Data) at hclear
    rw [hs] at hclear
    have ha : a.stacks (port 0) = [true,true] := by simp [a,w1,w0]
    simpa [ha] using hclear
  refine ⟨4+(tp+7),rf,wp,hload.seq (hpower.seq hc),?_,?_,?_⟩
  · simpa [w0,BinaryArithmetic.toNat,bitVal] using hv
  · simpa [w0,Nat.mul_comm] using hl
  · simp [w0] at ht
    dsimp [bound]
    omega

abbrev program := compiled command 1 2

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Field

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramModulus
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native production of the ternary modulus from runtime binary precision.
The output bytes themselves instantiate the prepared-modulus structure;
no canonical encoding or precomputed power is supplied to the machine. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

open BitProgram StructuredCalls SubexpScanPrimitives

abbrev modulusCommand : Cmd 8 41 :=
  .call (ProgramLinking.liftProgram LeafParametersProgram.Field.program id modulusPorts)

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramBoot
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

open BitProgram StructuredCalls

abbrev boot : Cmd 8 41 := .seq metadataFromBinary modulusCommand

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramConstants
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact word identities connecting the padded native preparation arrays
to the finite H-adic implementation. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t)

theorem scalar_neg_zero (hz : BinaryArithmetic.toNat cache.zero.val < p^t) :
    ((RingProgram.scalarProgram p t M cache).negRun cache.zero).1 = cache.zero := by
  apply RingProgram.word_eq_of_value p t _ _
  · exact RingProgram.wordMul_canonical p t M _ _
  · exact hz
  · simp only [RingProgram.scalarProgram, SubexpPreparedQuartic.wordMul_correct,
      cache.zero_correct, zero_mul]

theorem scalar_neg_one (hm : BinaryArithmetic.toNat cache.minusOne.val < p^t) :
    ((RingProgram.scalarProgram p t M cache).negRun cache.one).1 = cache.minusOne := by
  apply RingProgram.word_eq_of_value p t _ _
  · exact RingProgram.wordMul_canonical p t M _ _
  · exact hm
  · simp only [RingProgram.scalarProgram, SubexpPreparedQuartic.wordMul_correct,
      cache.one_correct, one_mul]

theorem minusOneRun_apply (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    (hm : BinaryArithmetic.toNat cache.minusOne.val < p^t)
    (height : ℕ) (i : Fin (3*height)) :
    (minusOneRun (RingProgram.scalarProgram p t M cache) height).1 i =
      if i.val = 0 then cache.minusOne else cache.zero := by
  simp only [minusOneRun, RingProgram.negRun, RingProgram.tabulateRun_eq, oneCode]
  by_cases hi : i.val = 0
  · simp only [hi, ↓reduceIte, RingProgram.scalarProgram]
    exact scalar_neg_one p t M cache hm
  · simp only [hi, ↓reduceIte, RingProgram.scalarProgram]
    exact scalar_neg_zero p t M cache hz

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarInit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar
open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing ModularRingPrograms ModularArithmetic

variable (p t : ℕ) [Fact p.Prime]

def initializePool : List Reg → Cmd 8 41
  | []=>.base .skip
  | i::is=>.seq (literal (port i) []) (initializePool is)

abbrev initializeAll : Cmd 8 41 := initializePool (List.finRange 12)

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarBase
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar
open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing ModularRingPrograms ModularArithmetic BinaryArithmetic

variable (t : ℕ)

abbrev baseCommand : Cmd 8 41 :=
  .seq initializeAll (.seq (literal 18 [true]) (negativeOne 28))

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramCanonical
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Canonical-word uniqueness allows native preparation to construct each
small integer by any measured arithmetic sequence, not a fixed syntax tree. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t)

/-- The native selector need only prove its cached output canonical and give
its integer residue; exact equality with the functional generator follows. -/
theorem integerRun_eq_of_value
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    (z : ℤ) (word : RingProgram.ScalarCode p t)
    (hw : BinaryArithmetic.toNat word.val < p^t)
    (hvalue : wordValue p t word = (z : ZMod (p^t))) :
    (integerRun (RingProgram.scalarProgram p t M cache) z).1 = word := by
  apply RingProgram.word_eq_of_value p t _ _
    (integerRun_canonical p t M cache hz z) hw
  have h := integerRun_correct (RingProgram.scalarRing p t M cache) z
  exact h.trans hvalue.symm

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalar
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native scalar preparation contract for the 41-stack H-adic setup.
All generated constants are canonical; the selector and array builder receive
exact functional words. The only unbounded iteration uses cached unary t. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar
open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing BinaryArithmetic

/-- Canonical scalar zero is literally the all-false fixed-width word. -/
theorem canonical_zero_bytes (t:ℕ) (cache:RingProgram.ScalarCache 3 t)
    (hz:BinaryArithmetic.toNat cache.zero.val < 3^t) :
    cache.zero.val=List.replicate (baseWidth 3 t) false := by
  have hn:∀n,BinaryArithmetic.toNat (List.replicate n false)=0 := by
    intro n; induction n with
    | zero=>rfl
    | succ n ih=>simp [List.replicate_succ,bitVal,ih]
  have he:cache.zero=SubexpPreparedQuartic.zeroWord 3 t := by
    apply RingProgram.word_eq_of_value 3 t _ _ hz
    · change BinaryArithmetic.toNat (List.replicate (baseWidth 3 t) false) < 3^t
      rw [hn]; positivity
    · rw [cache.zero_correct,SubexpPreparedQuartic.zeroWord_value]
  exact congrArg Subtype.val he

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A native descending-index traversal. The remaining unary counter is the
runtime index passed to the callback. Prefixing each generated word therefore
materializes the final array in increasing index order, without a precomputed
array or a value-dependent control table. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scan

open BitProgram StructuredCalls

def ports (counter : Fin 41) : UnaryForPrograms.Ports 8 41 := ⟨counter, 0, 7⟩

abbrev command (counter : Fin 41) (body : Cmd 8 41) : Cmd 8 41 :=
  UnaryForPrograms.forCmd (ports counter) body

abbrev copyAndScan (source counter _output scratch : Fin 41) (body : Cmd 8 41) : Cmd 8 41 :=
  .seq (.call (StackRoutines.copyProgram source counter scratch (0 : Fin 8) 1))
    (command counter body)

abbrev tableCommand (entry : Cmd 8 41) : Cmd 8 41 :=
  copyAndScan 37 24 22 38
    (copyAndScan 37 25 22 38 (copyAndScan 37 26 22 38 entry))

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramTableRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

open BitProgram StructuredCalls SubexpScanPrimitives
open IdempotentTableEntryProgram (entryCode)

abbrev nativeTable : Cmd 8 41 := Scan.tableCommand entryCommand

namespace Scan

theorem tableCells_eq_tableTape {n B : ℕ} (f : ℕ → ℕ → ℕ → List Bool)
    (table : Fin n → Fin n → Fin n → SubexpQuarticRing.Word B)
    (h : ∀ i j k : Fin n, f i.val j.val k.val = (table i j k).val) :
    tableCells f n = IdempotentProgram.tableTape table := by
  simp only [tableCells,cells_eq_ofFn]
  simp only [h]
  simp [IdempotentProgram.tableTape,IdempotentProgram.tableWords,List.map_flatten,
    List.flatten_flatten,List.map_ofFn,Function.comp_def]

end Scan

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramFinish
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

open BitProgram StructuredCalls SubexpQuarticRing

abbrev finishCommand : Cmd 8 41 := .seq nativeTable (.seq arrayStage preparationCleanup)

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramEncoded
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

open SubexpQuarticRing

theorem finished_counter (t : ℕ) (d e : Data) (table : List Bool)
    (he : e.stacks=finishedStacks d.stacks t table) :
    e.stacks 39=d.stacks 39 ∧ e.stacks 40=[] := by
  simp [he,finishedStacks,arrayStacks,preparationDiscard]

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IntegerRingLiftProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed little-endian binary-to-ring scanner.  No natural-number value is
used by the program: each input bit conditionally adds the current place and
then doubles that place.  Arithmetic is supplied by finite native commands;
the concrete RingModel instantiation is in IntegerRingLiftProgramModel. -/
namespace SubexponentialSAT.SqrtLog.IntegerRingLiftProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open CRTLocalProgram (ServiceSpec LowFrame lowFrame_update lowFrame_refl
  callAt CachePort)

def bitPorts : UnaryForPrograms.Ports 16 256 := ⟨246, 0, 1⟩

def bitStep (add : Code) : Code :=
  .seq (.ite 0 (callAt add 247 248 247) (.base .skip))
    (callAt add 248 248 248)

end SubexponentialSAT.SqrtLog.IntegerRingLiftProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IntegerRingLiftProgramModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete, fixed native programs lifting a pair of arbitrary little-endian
binary words to the actual RingModel. There is no integer-lifting callback.
The only runtime constants are explicit represented ring caches. -/
namespace SubexponentialSAT.SqrtLog.IntegerRingLiftProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open CRTLocalProgram (lowFrame_refl)

abbrev ModelCode (t d : ℕ) := RingProgram.Code (RingProgram.ScalarCode 3 t) d

def modelTable (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t) :=
  (RingProgram.structureTableRun (RingProgram.scalarProgram 3 t M cache)
    (RingProgram.liftCoefficientsRun t a.coefficients).1).1

end SubexponentialSAT.SqrtLog.IntegerRingLiftProgram

end OAI.Algorithms
end

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
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.BinaryArithmetic
open SubexponentialSAT.SqrtLog.RowSelectionProgram
open SubexponentialSAT.SqrtLog.LayoutProgramScalar
open SubexponentialSAT.Subexp.MatrixProgramSupport

def saved (regs : Fin 8 → Bool) (acc : WordPair)
    (prior old queue backup : List Bool) : State 8 18 :=
  ⟨regs, Function.update (state regs acc (prior,[]) (old,[]) queue).stacks 14 backup⟩

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

/-! One paid Pascal row pass over the framed cache. -/

/-! A fixed while loop consumes the runtime unary iteration count. -/

/-! A fixed loop builds the initial zero cache row from a runtime unary
length. The constant program contains one record, independent of that length. -/

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


