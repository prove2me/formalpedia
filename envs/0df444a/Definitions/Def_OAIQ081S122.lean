-- Prove2me | Definitions.Def_OAIQ081S122
-- name    : OAIQ081S122
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:35:44.091603+00:00
-- url     : https://prove2.me/theorems/e15ccf5c-fbc3-4151-b451-adfdb5db1543
-- title:
--   Definitions bundle OAIQ081S122 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 69 declarations of OpenAI's Lean: 34 definitions and 35 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap.searchProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.candidateState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.addCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.addLocal`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.finalFlatten`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.flatCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.flatFinish`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.flatNegative`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.flatParse`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.flatPositive`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.flatProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.flatRow`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.initialBuild`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.initialCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.initialPop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.normalizeComponent`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.zeroBody`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.zeroCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.zeroPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutDenominatorProgram.powerCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQuery.localInput`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQuery.view`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.matrixBase`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.EntryContract`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.clearColumn`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.clearIDs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.entryState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.cacheClear`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.cacheEmit`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.cacheFinishList`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.cacheRead`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Constants.constantCode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingNodeProgram.nodeCode`, `OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisEntryCore.Code`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_IrreducibleSearchBootstrap`, `SubexponentialSAT_SqrtLog_IrreducibleSearchNativeScan`, `SubexponentialSAT_SqrtLog_IrreducibleSearchPairAdapter`, `SubexponentialSAT_SqrtLog_IrreducibleSearchProgram`, `SubexponentialSAT_SqrtLog_IrreducibleSearchProgramDot`, `SubexponentialSAT_SqrtLog_IrreducibleSearchProgramDotRun`, `SubexponentialSAT_SqrtLog_IrreducibleSearchProgramLift`, `SubexponentialSAT_SqrtLog_LayoutBinomialProgramCell`, `SubexponentialSAT_SqrtLog_LayoutDenominatorProgram`, `SubexponentialSAT_SqrtLog_LayoutDenominatorProgramQueryCode`, `SubexponentialSAT_SqrtLog_LayoutDenominatorProgramQueryRun`, `SubexponentialSAT_SqrtLog_LayoutFiberSumProgramInterface`, `SubexponentialSAT_SqrtLog_LayoutMatrixProgram`, `SubexponentialSAT_SqrtLog_LayoutMatrixProgramRowStep`, `SubexponentialSAT_SqrtLog_LayoutMatrixProgramSource`, `SubexponentialSAT_SqrtLog_LayoutProgramScalarCacheCell`, `SubexponentialSAT_SqrtLog_LeafProgramConstantsModel`, `SubexponentialSAT_SqrtLog_RingNodeProgramModel`, `SubexponentialSAT_SubexpKernelControl`, `SubexponentialSAT_Subexp_GlobalBasisEntryCore`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S100`, `OAIQ081S102`, `OAIQ081S104`, `OAIQ081S105` and `OAIQ081S106` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S140`, `OAIQ081S142`, `OAIQ081S143`, `OAIQ081S144`, `OAIQ081S145` and `OAIQ081S146`; the statement `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.matrixBase_fiberReady`; the proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.matrixBase_fiberReady`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S100
import Definitions.Def_OAIQ081S102
import Definitions.Def_OAIQ081S104
import Definitions.Def_OAIQ081S105
import Definitions.Def_OAIQ081S106

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchProgramDot
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed bit program for the dynamically long F₃ dot product. Every
coefficient is physically read and every multiply-add uses the static
64-entry bit table. The source arrays are consumed. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram

theorem dotLoop_eval (as bs : List IrreducibleSearch.F) (s : IrreducibleSearch.F)
    (hlen : as.length = bs.length) (regs : Fin 8 → Bool) (output : List Bool) :
    ∃ finalRegs, Eval dotLoop (15 * as.length + 1)
      (dotGuardState as bs s regs output)
      (dotGuardState [] [] (dotAccumulator as bs s) finalRegs output) := by
  induction as generalizing bs s regs with
  | nil =>
      have hb : bs = [] := List.length_eq_zero_iff.mp (by simpa using hlen.symm)
      subst bs
      refine ⟨regs, ?_⟩
      apply Eval.while_false
      simp [dotGuardState, dotState, Atom.eval, Atom.instr, State.ofCfg, execInstr, readRegs]
  | cons a as ih =>
      cases bs with
      | nil => simp at hlen
      | cons b bs =>
          obtain ⟨mid, hb⟩ := dotBody_eval a b s as bs regs output
          obtain ⟨last, ht⟩ := ih bs (s + a * b) (by simpa using hlen) mid
          refine ⟨last, ?_⟩
          have hg : (dotGuardState (a :: as) (b :: bs) s regs output).regs 6 = true := by
            simp [dotGuardState, dotState, Atom.eval, Atom.instr, State.ofCfg, execInstr, readRegs]
          have he := Eval.while_true hg hb ht
          convert he using 1 <;> simp [ dotAccumulator] ; omega

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchProgramDotRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Complete execution of the fixed F₃ dot product, including initialization,
serialization of its output, the final halt, and primitive simulation. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram

theorem dotCommand_eval (as bs : List IrreducibleSearch.F)
    (hlen : as.length = bs.length) (regs : Fin 8 → Bool) (output : List Bool) :
    ∃ finalRegs, Eval dotCommand (15 * as.length + 6)
      (dotInput as bs regs output)
      ⟨finalRegs, ![[], [], coefficientWord ((List.zipWith (· * ·) as bs).sum) ++ output]⟩ := by
  have hi := atoms_eval dotInitialAtoms (dotInput as bs regs output)
  rw [dotInitial_result] at hi
  obtain ⟨last, hl⟩ := dotLoop_eval as bs 0 hlen regs output
  have hf := atoms_eval dotFinalAtoms
    (dotGuardState [] [] (dotAccumulator as bs 0) last output)
  rw [dotFinal_result] at hf
  refine ⟨(dotGuardState [] [] (dotAccumulator as bs 0) last output).regs, ?_⟩
  have he := hi.seq (hl.seq hf)
  convert he using 1 <;>
    simp [ dotInitialAtoms, dotFinalAtoms, dotAccumulator_value] ; omega

theorem dotProgram_run (as bs : List IrreducibleSearch.F)
    (hlen : as.length = bs.length) (regs : Fin 8 → Bool) (output : List Bool) :
    ∃ finalRegs, Trace dotProgram (15 * as.length + 7)
      ((dotInput as bs regs output).withPC (some dotProgram.entry))
      (State.withPC
        ⟨finalRegs, ![[], [], coefficientWord ((List.zipWith (· * ·) as bs).sum) ++ output]⟩ none) := by
  obtain ⟨last, he⟩ := dotCommand_eval as bs hlen regs output
  refine ⟨last, ?_⟩
  simpa [dotProgram, Nat.add_assoc] using compiled_halt_trace he 0 2

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchProgramLift
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Framed invocation of the fixed three-stack prefix and dot programs. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem dotCall_eval {R S : ℕ} (regs : Fin 8 ↪ Fin R) (ports : Fin 3 ↪ Fin S)
    (as bs : List IrreducibleSearch.F) (hlen : as.length = bs.length)
    (output : List Bool) (d : State R S)
    (ha : d.stacks (ports 0) = coefficientArray as)
    (hb : d.stacks (ports 1) = coefficientArray bs) (hc : d.stacks (ports 2) = output) :
    ∃ rf, Eval (dotCall regs ports) (15 * as.length + 7) d
      (afterThree regs ports rf [] []
        (coefficientWord ((List.zipWith (· * ·) as bs).sum) ++ output) d) := by
  obtain ⟨rf, he⟩ := dotProgram_run as bs hlen (fun i => d.regs (regs i)) output
  have ht := eval_call_lifted dotProgram regs ports d regs.injective ports.injective he
  simp only [dotInput] at ht
  rw [three_initial regs ports _ _ _ d ha hb hc, three_embed] at ht
  exact ⟨rf, ht⟩

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchPairAdapter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed physical split of a concatenated pair of coefficient arrays. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchPairAdapter

open BitProgram StructuredCalls SubexpSetupStorage IrreducibleSearchProgram

theorem command_eval (as bs : List IrreducibleSearch.F) (count : List Bool)
    (hc : count.length = as.length) (regs : Fin 16 → Bool) :
    ∃ finalRegs, Eval command (28 * count.length + 16)
      (input as bs count regs) (output as bs count finalRegs) := by
  let a := input as bs count regs
  let b := copyState (1 : Fin 6) 2 a
  have e1 := copy_eval (1 : Fin 6) 2 5 a (by decide) (by decide) (by decide)
    (by simp [a, input])
  obtain ⟨r2, e2⟩ := prefixCall_eval registers firstPorts (as ++ bs) count [] b
    (by simp [b, a, copyState, StackRoutines.copyStacks, input, firstPorts])
    (by simp [b, a, copyState, StackRoutines.copyStacks, input, firstPorts])
    (by simp [b, a, copyState, StackRoutines.copyStacks, input, firstPorts])
  simp only [hc, List.drop_left, paddedPrefix_append_left, List.append_nil] at e2
  let c := afterThree registers firstPorts r2 (coefficientArray bs) []
    (coefficientArray as.reverse) b
  change Eval _ _ _ c at e2
  let d := copyState (1 : Fin 6) 2 c
  have e3 := copy_eval (1 : Fin 6) 2 5 c (by decide) (by decide) (by decide)
    (by simp [c, b, a, afterThree, replaceThree, firstPorts,
      copyState, StackRoutines.copyStacks, input])
  obtain ⟨r4, e4⟩ := prefixCall_eval registers secondPorts as.reverse count [] d
    (by simp [d, c, copyState, StackRoutines.copyStacks, afterThree,
      replaceThree, firstPorts, secondPorts])
    (by simp [d, c, b, a, copyState, StackRoutines.copyStacks, afterThree,
      replaceThree, firstPorts, secondPorts, input])
    (by simp [d, c, b, a, copyState, StackRoutines.copyStacks, afterThree,
      replaceThree, firstPorts, secondPorts, input])
  have hdrop : as.reverse.drop count.length = [] := by
    apply List.drop_eq_nil_iff.mpr
    simp [hc]
  have hpad : paddedPrefix count.length as.reverse = as.reverse :=
    paddedPrefix_of_length _ _ (by simp [hc])
  simp only [hdrop, hpad, List.reverse_reverse, coefficientArray_nil,
    List.append_nil] at e4
  let e := afterThree registers secondPorts r4 [] [] (coefficientArray as) d
  change Eval _ _ _ e at e4
  have he := e1.seq (e2.seq (e3.seq e4))
  have hend : e = output as bs count e.regs := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    funext i
    fin_cases i <;> simp [e, d, c, b, a, afterThree, replaceThree,
      firstPorts, secondPorts, copyState, StackRoutines.copyStacks, input, output]
  rw [hend] at he
  refine ⟨e.regs, ?_⟩
  convert he using 1 ;
    simp [a, c, b, input, afterThree, replaceThree, firstPorts,
      copyState, StackRoutines.copyStacks, hc] ; omega

theorem program_runsIn (as bs : List IrreducibleSearch.F) (count : List Bool)
    (hc : count.length = as.length) (regs : Fin 16 → Bool) :
    ∃ finalRegs, RunsIn program (28 * count.length + 17)
      ((input as bs count regs).withPC (some program.entry))
      ((output as bs count finalRegs).withPC none) := by
  obtain ⟨rf, he⟩ := command_eval as bs count hc regs
  exact ⟨rf, _, by omega, compiled_halt_trace he 0 4⟩

end SubexponentialSAT.SqrtLog.IrreducibleSearchPairAdapter

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Closed fixed-bit F₃ factor checker. The complete command is independent
of the degree. All coefficient addresses and loop bounds are runtime unary
words; source vectors are preserved and scratch stacks are discharged. -/


/-! Coefficient -/

/-! A fixed coefficient kernel: two preserved source arrays, a preserved
unary coefficient address plus one, and an output stack. Every copy, padded
prefix, coefficient reversal, multiply-add and cleanup is an actual call. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage

theorem coefficientCommand_eval (as bs : List IrreducibleSearch.F)
    (count output : List Bool) (regs : Fin 16 → Bool) :
    ∃ steps finalRegs, steps ≤ 300 * (as.length + bs.length + count.length + 1) ∧
      Eval coefficientCommand steps (coefficientState as bs count output regs)
        (coefficientState as bs count
          (coefficientWord (coefficientValue as bs count.length) ++ output) finalRegs) := by
  let d0 := coefficientState as bs count output regs
  let d1 := copyState (0 : Fin 11) 3 d0
  have e1 := copy_eval (0 : Fin 11) 3 10 d0 (by decide) (by decide) (by decide)
    (by simp [d0, coefficientState])
  let d2 := copyState (2 : Fin 11) 5 d1
  have e2 := copy_eval (2 : Fin 11) 5 10 d1 (by decide) (by decide) (by decide)
    (by simp [d1, d0, copyState, StackRoutines.copyStacks, coefficientState])
  obtain ⟨r3, e3⟩ := prefixCall_eval sixRegisters coefficientLeftPorts as count [] d2
    (by simp [d2, d1, d0, copyState, StackRoutines.copyStacks, coefficientState,
      coefficientLeftPorts])
    (by simp [d2, d1, d0, copyState, StackRoutines.copyStacks, coefficientState,
      coefficientLeftPorts])
    (by simp [d2, d1, d0, copyState, StackRoutines.copyStacks, coefficientState,
      coefficientLeftPorts])
  let d3 := afterThree sixRegisters coefficientLeftPorts r3
    (coefficientArray (as.drop count.length)) []
    (coefficientArray (paddedPrefix count.length as).reverse) d2
  simp only [List.append_nil] at e3
  change Eval _ _ _ d3 at e3
  let d4 := copyState (2 : Fin 11) 5 d3
  have e4 := copy_eval (2 : Fin 11) 5 10 d3 (by decide) (by decide) (by decide)
    (by simp [d3, d2, d1, d0, afterThree, replaceThree, coefficientLeftPorts,
      copyState, StackRoutines.copyStacks, coefficientState])
  obtain ⟨r5, e5⟩ := prefixCall_eval sixRegisters coefficientReversePorts
    (paddedPrefix count.length as).reverse count [] d4
    (by simp [d4, d3, copyState, StackRoutines.copyStacks, afterThree, replaceThree,
      coefficientReversePorts, coefficientLeftPorts])
    (by simp [d4, d3, d2, d1, d0, copyState, StackRoutines.copyStacks, afterThree,
      replaceThree, coefficientReversePorts, coefficientLeftPorts, coefficientState])
    (by simp [d4, d3, d2, d1, d0, copyState, StackRoutines.copyStacks, afterThree,
      replaceThree, coefficientReversePorts, coefficientLeftPorts, coefficientState])
  have hlen : ((paddedPrefix count.length as).reverse).length = count.length := by simp
  have hdrop : (paddedPrefix count.length as).reverse.drop count.length = [] :=
    List.drop_eq_nil_iff.mpr hlen.le
  have hpad : paddedPrefix count.length (paddedPrefix count.length as).reverse =
      (paddedPrefix count.length as).reverse := paddedPrefix_of_length _ _ hlen
  simp only [hdrop, hpad, List.reverse_reverse, coefficientArray_nil, List.append_nil] at e5
  let d5 := afterThree sixRegisters coefficientReversePorts r5 [] []
    (coefficientArray (paddedPrefix count.length as)) d4
  change Eval _ _ _ d5 at e5
  let d6 := copyState (1 : Fin 11) 4 d5
  have e6 := copy_eval (1 : Fin 11) 4 10 d5 (by decide) (by decide) (by decide)
    (by simp [d5, d4, d3, d2, d1, d0, copyState, StackRoutines.copyStacks,
      afterThree, replaceThree, coefficientLeftPorts, coefficientReversePorts, coefficientState])
  let d7 := copyState (2 : Fin 11) 5 d6
  have e7 := copy_eval (2 : Fin 11) 5 10 d6 (by decide) (by decide) (by decide)
    (by simp [d6, d5, d4, d3, d2, d1, d0, copyState, StackRoutines.copyStacks,
      afterThree, replaceThree, coefficientLeftPorts, coefficientReversePorts, coefficientState])
  obtain ⟨r8, e8⟩ := prefixCall_eval sixRegisters coefficientRightPorts bs count [] d7
    (by simp [d7, d6, d5, d4, d3, d2, d1, d0, copyState, StackRoutines.copyStacks,
      afterThree, replaceThree, coefficientLeftPorts, coefficientReversePorts,
      coefficientRightPorts, coefficientState])
    (by simp [d7, d6, d5, d4, d3, d2, d1, d0, copyState, StackRoutines.copyStacks,
      afterThree, replaceThree, coefficientLeftPorts, coefficientReversePorts,
      coefficientRightPorts, coefficientState])
    (by simp [d7, d6, d5, d4, d3, d2, d1, d0, copyState, StackRoutines.copyStacks,
      afterThree, replaceThree, coefficientLeftPorts, coefficientReversePorts,
      coefficientRightPorts, coefficientState])
  let d8 := afterThree sixRegisters coefficientRightPorts r8
    (coefficientArray (bs.drop count.length)) []
    (coefficientArray (paddedPrefix count.length bs).reverse) d7
  simp only [List.append_nil] at e8
  change Eval _ _ _ d8 at e8
  obtain ⟨r9, e9⟩ := dotCall_eval eightRegisters coefficientDotPorts
    (paddedPrefix count.length as) (paddedPrefix count.length bs).reverse (by simp) output d8
    (by simp [d8, d7, d6, d5, copyState, StackRoutines.copyStacks, afterThree,
      replaceThree, coefficientRightPorts, coefficientReversePorts, coefficientDotPorts])
    (by simp [d8, afterThree, replaceThree, coefficientRightPorts, coefficientDotPorts])
    (by simp [d8, d7, d6, d5, d4, d3, d2, d1, d0, copyState, StackRoutines.copyStacks,
      afterThree, replaceThree, coefficientLeftPorts, coefficientReversePorts,
      coefficientRightPorts, coefficientDotPorts, coefficientState])
  let d9 := afterThree eightRegisters coefficientDotPorts r9 [] []
    (coefficientWord (coefficientValue as bs count.length) ++ output) d8
  change Eval _ _ _ d9 at e9
  let d10 := clearState (3 : Fin 11) d9
  let d11 := clearState (4 : Fin 11) d10
  have e10 := clear_eval (3 : Fin 11) d9
  have e11 := clear_eval (4 : Fin 11) d10
  have he := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq
    (e8.seq (e9.seq (e10.seq e11)))))))))
  have hend : d11 = coefficientState as bs count
      (coefficientWord (coefficientValue as bs count.length) ++ output) d11.regs := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    funext i
    fin_cases i <;>
      simp [d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1, d0,
        clearState, copyState, StackRoutines.copyStacks, afterThree, replaceThree,
        coefficientLeftPorts, coefficientReversePorts, coefficientRightPorts,
        coefficientDotPorts, coefficientState]
  change Eval coefficientCommand _ d0 d11 at he
  rw [hend] at he
  refine ⟨_, d11.regs, ?_, he⟩
  have ha : (as.drop count.length).length ≤ as.length := by simp
  have hb : (bs.drop count.length).length ≤ bs.length := by simp
  simp [d10, d9, d8, d7, d6, d5, d4, d3, d2, d1, d0, clearState, copyState,
    StackRoutines.copyStacks, afterThree, replaceThree, coefficientLeftPorts,
    coefficientReversePorts, coefficientRightPorts, coefficientDotPorts,
    coefficientState, coefficientArray_length]
  omega

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram


/-! CoefficientRun -/

/-! The closed, fixed-program boundary for one arbitrary convolution
coefficient. Its sources and runtime unary address are preserved and all
work stacks are empty again. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem coefficientProgram_run (as bs : List IrreducibleSearch.F)
    (count output : List Bool) (regs : Fin 16 → Bool) :
    ∃ finalRegs, RunsIn coefficientProgram
      (300 * (as.length + bs.length + count.length + 1) + 1)
      ((coefficientState as bs count output regs).withPC (some coefficientProgram.entry))
      ((coefficientState as bs count
        (coefficientWord (coefficientValue as bs count.length) ++ output) finalRegs).withPC none) := by
  obtain ⟨steps, last, hb, he⟩ := coefficientCommand_eval as bs count output regs
  exact ⟨last, steps + 1, by omega, compiled_halt_trace he 0 9⟩

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram


/-! ProductLift -/

/-! A framed invocation of the source-preserving coefficient kernel. The
extra stack stores the remaining runtime product length. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem coefficientCall_eval (as bs : List IrreducibleSearch.F)
    (count remaining output : List Bool) (regs : Fin 16 → Bool) :
    ∃ steps finalRegs, steps ≤ 300 * (as.length + bs.length + count.length + 1) + 1 ∧
      Eval coefficientCall steps (productState as bs count remaining output regs)
        (productState as bs count remaining
          (coefficientWord (coefficientValue as bs count.length) ++ output) finalRegs) := by
  obtain ⟨rf, steps, hb, he⟩ := coefficientProgram_run as bs count output regs
  have ht := eval_call_lifted coefficientProgram id coefficientStackPorts
    (productState as bs count remaining output regs) Function.injective_id
    coefficientStackPorts.injective he
  rw [product_embed, product_embed] at ht
  exact ⟨steps, rf, hb, ht⟩

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram


/-! Product -/

/-! A fixed outer loop runs the coefficient kernel at successively longer
unary addresses. Source arrays are preserved; all output coefficients are
physically written in decreasing degree order. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.StructuredProgram (Atom)

theorem productBody_eval (as bs : List IrreducibleSearch.F)
    (count remaining output : List Bool) (bit : Bool) (regs : Fin 16 → Bool) :
    ∃ steps nextRegs, steps ≤ 300 * (as.length + bs.length + count.length + 1) + 4 ∧
      Eval productBody steps
        (productGuardState as bs count (bit :: remaining) output regs)
        (productGuardState as bs (false :: count) remaining
          (coefficientWord (coefficientValue as bs count.length) ++ output) nextRegs) := by
  let d0 := productGuardState as bs count (bit :: remaining) output regs
  have hd0 : d0 = productState as bs count remaining output d0.regs := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    funext i; fin_cases i <;>
      simp [d0, productGuardState, productState, Atom.eval, Atom.instr,
        StructuredProgram.State.ofCfg, execInstr, readRegs]
  obtain ⟨steps, rf, hb, he⟩ := coefficientCall_eval as bs count remaining output d0.regs
  rw [← hd0] at he
  let d1 := productState as bs count remaining
    (coefficientWord (coefficientValue as bs count.length) ++ output) rf
  let d2 := atomsResult productIncrement d1
  have hd2 : d2 = productState as bs (false :: count) remaining
      (coefficientWord (coefficientValue as bs count.length) ++ output) d2.regs := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    funext i; fin_cases i <;>
      simp [d2, d1, atomsResult, productIncrement, productState, Atom.eval,
        Atom.instr, StructuredProgram.State.ofCfg,
        execInstr, readRegs]
  have hi := Eval.base (atoms_eval productIncrement d1)
  have hp := Eval.base (StructuredProgram.Eval.atom (.pop 11 14 15) d2)
  have ht := he.seq (hi.seq hp)
  rw [hd2] at ht
  refine ⟨steps + 3, d2.regs, by omega, ?_⟩
  simpa only [d0, productBody, productIncrement, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.add_assoc, productGuardState] using ht

theorem productLoop_eval (as bs : List IrreducibleSearch.F)
    (count remaining output : List Bool) (regs : Fin 16 → Bool) :
    ∃ steps finalRegs,
      steps ≤ remaining.length *
        (300 * (as.length + bs.length + count.length + remaining.length + 1) + 5) + 1 ∧
      Eval productLoop steps (productGuardState as bs count remaining output regs)
        (productGuardState as bs (List.replicate remaining.length false ++ count) []
          (productOutput as bs count.length remaining.length output) finalRegs) := by
  induction remaining generalizing count output regs with
  | nil =>
      refine ⟨1, regs, by simp, ?_⟩
      simp only [List.length_nil, List.replicate_zero, List.nil_append, productOutput]
      apply Eval.while_false
      simp [productGuardState, productState, Atom.eval, Atom.instr,
        StructuredProgram.State.ofCfg, execInstr, readRegs]
  | cons bit remaining ih =>
      obtain ⟨n, middle, hn, he⟩ := productBody_eval as bs count remaining output bit regs
      obtain ⟨m, last, hm, ht⟩ := ih (false :: count)
        (coefficientWord (coefficientValue as bs count.length) ++ output) middle
      have hg : (productGuardState as bs count (bit :: remaining) output regs).regs 15 = true := by
        simp [productGuardState, productState, Atom.eval, Atom.instr,
          StructuredProgram.State.ofCfg, execInstr, readRegs]
      have hr := Eval.while_true hg he ht
      refine ⟨n + m + 1, last, ?_, ?_⟩
      · simp only [List.length_cons] at hm ⊢
        nlinarith
      · simpa only [productLoop, List.length_cons, productOutput,
          List.append_assoc, List.singleton_append,
          List.replicate_succ', List.cons_append, List.nil_append] using hr

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram


/-! ProductRun -/

namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.StructuredProgram (Atom)

theorem productProgram_run (as bs : List IrreducibleSearch.F)
    (count remaining output : List Bool) (regs : Fin 16 → Bool) :
    ∃ finalRegs, RunsIn productProgram
      (remaining.length *
        (300 * (as.length + bs.length + count.length + remaining.length + 1) + 5) + 3)
      ((productState as bs count remaining output regs).withPC (some productProgram.entry))
      ((productState as bs (List.replicate remaining.length false ++ count) []
        (productOutput as bs count.length remaining.length output) finalRegs).withPC none) := by
  obtain ⟨n, rf, hb, he⟩ := productLoop_eval as bs count remaining output regs
  have hi := Eval.base (StructuredProgram.Eval.atom (.pop 11 14 15)
    (productState as bs count remaining output regs))
  have ht := hi.seq he
  let last := productGuardState as bs (List.replicate remaining.length false ++ count) []
    (productOutput as bs count.length remaining.length output) rf
  have hl : last = productState as bs (List.replicate remaining.length false ++ count) []
      (productOutput as bs count.length remaining.length output) last.regs := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    funext i; fin_cases i <;>
      simp [last, productGuardState, productState, Atom.eval, Atom.instr,
        StructuredProgram.State.ofCfg, execInstr, readRegs]
  change Eval productCommand (1 + n) _ last at ht
  rw [hl] at ht
  exact ⟨last.regs, 1 + n + 1, by omega, compiled_halt_trace ht 0 9⟩

theorem convolutionProduct_run {d : ℕ} (a b : Fin d → IrreducibleSearch.F)
    (remaining output : List Bool) (regs : Fin 16 → Bool) :
    ∃ finalRegs, RunsIn productProgram
      (remaining.length * (300 * (2 * d + remaining.length + 2) + 5) + 3)
      ((productState (List.ofFn a) (List.ofFn b) [false] remaining output regs).withPC
        (some productProgram.entry))
      ((productState (List.ofFn a) (List.ofFn b)
        (List.replicate remaining.length false ++ [false]) []
        (coefficientArray (((List.range remaining.length).map
          (IrreducibleSearch.convolution a b)).reverse) ++ output) finalRegs).withPC none) := by
  have ht := productProgram_run (List.ofFn a) (List.ofFn b) [false] remaining output regs
  simpa only [List.length_cons, List.length_nil, Nat.reduceAdd, List.length_ofFn,
    show d + d + 1 + remaining.length + 1 = 2 * d + remaining.length + 2 by omega,
    productOutput_convolution] using ht

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram


/-! Monic -/

/-! Appending the implicit monic coefficient uses two physical transfers.
No input-dependent instruction table or uncharged array append is used. -/


/-! MonicAlgebra -/


/-! CheckLift -/

/-! Framed calls to the physical Boolean predicates. -/


/-! PairProduct -/

namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.StructuredProgram (Atom)
open SubexponentialSAT.SubexpSetupStorage

theorem pairProduct_embed (as bs cs : List IrreducibleSearch.F)
    (depth count remaining output newCount newRemaining newOutput : List Bool)
    (regs finalRegs : Fin 16 → Bool) :
    embedState id pairProductPorts (pairState as bs cs depth count remaining output regs)
      (productState as bs newCount newRemaining newOutput finalRegs) =
      pairState as bs cs depth newCount newRemaining newOutput finalRegs := by
  apply embedState_eq_of_ports id pairProductPorts _ _ _
    Function.injective_id pairProductPorts.injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h : 12 ≤ i.val := by
      by_contra hn
      exact hi ⟨⟨i.val, by omega⟩, rfl⟩
    fin_cases i <;> simp_all [pairState]

theorem pairProductCall_eval {d : ℕ} (a b : Fin d → IrreducibleSearch.F)
    (cs : List IrreducibleSearch.F) (depth remaining : List Bool) (regs : Fin 16 → Bool) :
    ∃ steps rf,
      steps ≤ remaining.length * (300 * (2 * d + remaining.length + 2) + 5) + 3 ∧
      Eval pairProductCall steps (pairState (List.ofFn a) (List.ofFn b) cs depth
        [false] remaining [] regs)
      (pairState (List.ofFn a) (List.ofFn b) cs depth
        (List.replicate remaining.length false ++ [false]) []
        (coefficientArray (((List.range remaining.length).map
          (IrreducibleSearch.convolution a b)).reverse)) rf) := by
  obtain ⟨rf, steps, hb, he⟩ := convolutionProduct_run a b remaining [] regs
  have ht := eval_call_lifted productProgram id pairProductPorts
    (pairState (List.ofFn a) (List.ofFn b) cs depth [false] remaining [] regs)
    Function.injective_id pairProductPorts.injective he
  simp only [List.append_nil] at ht
  rw [pairProduct_embed, pairProduct_embed] at ht
  exact ⟨steps, rf, hb, ht⟩

theorem pairProductCommand_eval {d : ℕ} (a b : Fin (d + 1) → IrreducibleSearch.F)
    (cs : List IrreducibleSearch.F) (depth : List Bool) (hlen : depth.length = d)
    (regs : Fin 16 → Bool) :
    ∃ steps rf, steps ≤ 10000 * (d + 1)^2 ∧
      Eval pairProductCommand steps (pairState (List.ofFn a) (List.ofFn b) cs depth [] [] [] regs)
        (pairState (List.ofFn a) (List.ofFn b) cs depth [] []
          (coefficientArray (((List.range (2*d+1)).map
            (IrreducibleSearch.convolution a b)).reverse)) rf) := by
  let d0 := pairState (List.ofFn a) (List.ofFn b) cs depth [] [] [] regs
  let d1 := copyState (14 : Fin 18) 11 d0
  let d2 := copyState (14 : Fin 18) 11 d1
  let d3 := atomsResult pairProductSetupAtoms d2
  have e1 := copy_eval (14 : Fin 18) 11 17 d0 (by decide) (by decide) (by decide)
    (by simp [d0, pairState])
  have e2 := copy_eval (14 : Fin 18) 11 17 d1 (by decide) (by decide) (by decide)
    (by simp [d1, d0, pairState, copyState, StackRoutines.copyStacks])
  have e3 := Eval.base (atoms_eval pairProductSetupAtoms d2)
  have h3 : d3 = pairState (List.ofFn a) (List.ofFn b) cs depth [false]
      (false :: (depth ++ depth)) [] d3.regs := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    funext i; fin_cases i <;>
      simp [d3, d2, d1, d0, atomsResult, pairProductSetupAtoms, pairState,
        copyState, StackRoutines.copyStacks, Atom.eval, Atom.instr,
        StructuredProgram.State.ofCfg, execInstr]
  obtain ⟨n, rf, hn, e4⟩ := pairProductCall_eval a b cs depth (false :: (depth ++ depth)) d3.regs
  rw [← h3] at e4
  have hr : (false :: (depth ++ depth)).length = 2*d+1 := by simp [hlen]; omega
  rw [hr] at e4 hn
  let d4 := pairState (List.ofFn a) (List.ofFn b) cs depth
    (List.replicate (2*d+1) false ++ [false]) []
    (coefficientArray (((List.range (2*d+1)).map
      (IrreducibleSearch.convolution a b)).reverse)) rf
  have e5 := clear_eval (2 : Fin 18) d4
  let d5 := clearState (2 : Fin 18) d4
  have h5 : d5 = pairState (List.ofFn a) (List.ofFn b) cs depth [] []
      (coefficientArray (((List.range (2*d+1)).map
        (IrreducibleSearch.convolution a b)).reverse)) d5.regs := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    funext i; fin_cases i <;> simp [d5, d4, clearState, pairState]
  have he := e1.seq (e2.seq (e3.seq (e4.seq e5)))
  change Eval pairProductCommand _ d0 d5 at he
  rw [h5] at he
  refine ⟨_, d5.regs, ?_, he⟩
  simp [d4, d1, d0, pairState, copyState, StackRoutines.copyStacks,
    pairProductSetupAtoms, hlen]
  nlinarith

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram


/-! Candidate -/

namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
open SubexponentialSAT.StructuredProgram (Atom)

def candidateState (as bs cs : List IrreducibleSearch.F)
    (depth product target : List Bool) (regs : Fin 16 → Bool) : State 16 18 :=
  ⟨regs, Function.update (pairState as bs cs depth [] [] product regs).stacks 16 target⟩

theorem candidateCommand_eval {d : ℕ} (c : Fin d → IrreducibleSearch.F)
    (as bs : List IrreducibleSearch.F) (depth product : List Bool)
    (hlen : depth.length = d) (regs : Fin 16 → Bool) :
    ∃ steps rf, steps ≤ 100 * (d + 1) ∧
      Eval candidateCommand steps (pairState as bs (List.ofFn c) depth [] [] product regs)
        (candidateState as bs (List.ofFn c) depth product
          (coefficientArray (paddedPrefix (2*d+1) (List.ofFn c ++ [1])).reverse) rf) := by
  let d0 := pairState as bs (List.ofFn c) depth [] [] product regs
  let d1 := copyState (13 : Fin 18) 15 d0
  have e1 := copy_eval (13 : Fin 18) 15 17 d0 (by decide) (by decide) (by decide)
    (by simp [d0, pairState])
  obtain ⟨r2, e2⟩ := appendOneCommand_eval (15 : Fin 18) 3 (by decide) (List.ofFn c) d1
    (by simp [d1, d0, copyState, StackRoutines.copyStacks, pairState])
    (by simp [d1, d0, copyState, StackRoutines.copyStacks, pairState])
  let d2 : State 16 18 := ⟨r2, Function.update d1.stacks 15 (coefficientArray (List.ofFn c ++ [1]))⟩
  let d3 := copyState (14 : Fin 18) 5 d2
  let d4 := copyState (14 : Fin 18) 5 d3
  let d5 := atomsResult candidateCountAtoms d4
  have e3 := copy_eval (14 : Fin 18) 5 17 d2 (by decide) (by decide) (by decide)
    (by simp [d2, d1, d0, copyState, StackRoutines.copyStacks, pairState])
  have e4 := copy_eval (14 : Fin 18) 5 17 d3 (by decide) (by decide) (by decide)
    (by simp [d3, d2, d1, d0, copyState, StackRoutines.copyStacks, pairState])
  have e5 := Eval.base (atoms_eval candidateCountAtoms d4)
  obtain ⟨r6, e6⟩ := prefixCall_eval sixRegisters candidatePorts
    (List.ofFn c ++ [1]) (false :: (depth ++ depth)) [] d5
    (by simp [d5, d4, d3, d2, d1, d0, atomsResult, candidateCountAtoms,
      candidatePorts, copyState, StackRoutines.copyStacks, pairState, Atom.eval,
      Atom.instr, StructuredProgram.State.ofCfg, execInstr])
    (by simp [d5, d4, d3, d2, d1, d0, atomsResult, candidateCountAtoms,
      candidatePorts, copyState, StackRoutines.copyStacks, pairState, Atom.eval,
      Atom.instr, StructuredProgram.State.ofCfg, execInstr])
    (by simp [d5, d4, d3, d2, d1, d0, atomsResult, candidateCountAtoms,
      candidatePorts, copyState, StackRoutines.copyStacks, pairState, Atom.eval,
      Atom.instr, StructuredProgram.State.ofCfg, execInstr])
  have hc : (false :: (depth ++ depth)).length = 2*d+1 := by simp [hlen]; omega
  have hd : (List.ofFn c ++ [1]).drop (2*d+1) = [] := by
    apply List.drop_eq_nil_iff.mpr
    simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil]
    omega
  simp only [hc, hd, coefficientArray_nil, List.append_nil] at e6
  let d6 := afterThree sixRegisters candidatePorts r6 [] []
    (coefficientArray (paddedPrefix (2*d+1) (List.ofFn c ++ [1])).reverse) d5
  change Eval _ _ _ d6 at e6
  have h6 : d6 = candidateState as bs (List.ofFn c) depth product
      (coefficientArray (paddedPrefix (2*d+1) (List.ofFn c ++ [1])).reverse) d6.regs := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    funext i; fin_cases i <;>
      simp [d6, d5, d4, d3, d2, d1, d0, afterThree, replaceThree, candidatePorts,
        atomsResult, candidateCountAtoms, copyState, StackRoutines.copyStacks,
        candidateState, pairState, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg, execInstr]
  have he := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq e6))))
  change Eval candidateCommand _ d0 d6 at he
  rw [h6] at he
  refine ⟨_, d6.regs, ?_, he⟩
  simp [d3, d2, d1, d0, copyState, StackRoutines.copyStacks, pairState,
    coefficientArray_length, candidateCountAtoms, hlen]
  omega

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram


/-! ProductCheck -/

namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem productCheckCommand_eval {d : ℕ} (c : Fin d → IrreducibleSearch.F)
    (a b : Fin (d + 1) → IrreducibleSearch.F) (depth : List Bool)
    (hlen : depth.length = d) (regs : Fin 16 → Bool) :
    ∃ steps rf, steps ≤ 12000 * (d + 1)^2 ∧
      Eval productCheckCommand steps
        (pairState (List.ofFn a) (List.ofFn b) (List.ofFn c) depth [] [] [] regs)
        (pairState (List.ofFn a) (List.ofFn b) (List.ofFn c) depth [] [] [] rf) ∧
      rf 3 = IrreducibleSearch.productEq c a b := by
  let product := coefficientArray (((List.range (2*d+1)).map
    (IrreducibleSearch.convolution a b)).reverse)
  let target := coefficientArray (paddedPrefix (2*d+1) (List.ofFn c ++ [1])).reverse
  obtain ⟨n, r1, hn, e1⟩ := pairProductCommand_eval a b (List.ofFn c) depth hlen regs
  obtain ⟨m, r2, hm, e2⟩ := candidateCommand_eval c (List.ofFn a) (List.ofFn b)
    depth product hlen r1
  let d2 := candidateState (List.ofFn a) (List.ofFn b) (List.ofFn c) depth product target r2
  have hlength : product.length = target.length := by
    simp [product, target, coefficientArray_length]
  obtain ⟨r3, e3, hv⟩ := compareCall_eval productComparePorts product target hlength d2
    (by simp [d2, candidateState, pairState, productComparePorts])
    (by simp [d2, candidateState, productComparePorts])
  let d3 := afterTwo fourRegisters productComparePorts r3 [] [] d2
  have h3 : d3 = pairState (List.ofFn a) (List.ofFn b) (List.ofFn c) depth [] [] [] d3.regs := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    funext i; fin_cases i <;>
      simp [d3, d2, afterTwo, replaceTwo, productComparePorts, candidateState, pairState]
  have he := e1.seq (e2.seq e3)
  change Eval productCheckCommand _ _ d3 at he
  rw [h3] at he
  refine ⟨n + (m + (6 * product.length + 4)), d3.regs, ?_, he, ?_⟩
  · have hp : product.length = 2 * (2*d+1) := by simp [product, coefficientArray_length]
    rw [hp]
    have hsq : d + 1 ≤ (d + 1) ^ 2 := by
      rw [pow_two]
      exact Nat.le_mul_of_pos_left (d + 1) (by omega)
    have hsmall : 100 * (d + 1) + 6 * (2 * (2 * d + 1)) + 4 ≤
        2000 * (d + 1) := by omega
    have hscale : 2000 * (d + 1) ≤ 2000 * (d + 1) ^ 2 :=
      Nat.mul_le_mul_left 2000 hsq
    omega
  · change d3.regs 3 = decide (product = target) at hv
    exact hv.trans (productComparison_eq c a b)

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram


/-! Pair -/

/-! Closed primitive pair test. All three source vectors and the runtime
unary degree are preserved. The return bit is exactly the scalar pairPass. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
open SubexponentialSAT.StructuredProgram (Atom)

theorem pairTailCommand_eval {d : ℕ} (c : Fin d → IrreducibleSearch.F)
    (a b : Fin (d + 1) → IrreducibleSearch.F) (depth : List Bool) (regs : Fin 16 → Bool) :
    ∃ steps rf, steps ≤ 1000 * (d + 1) ∧
      Eval pairTailCommand steps
        (pairState (List.ofFn a) (List.ofFn b) (List.ofFn c) depth [] [] [] regs)
        (pairState (List.ofFn a) (List.ofFn b) (List.ofFn c) depth [] [] [] rf) ∧
      rf 3 = !(IrreducibleSearch.nonconstant a && IrreducibleSearch.nonconstant b && regs 3) := by
  let d0 := pairState (List.ofFn a) (List.ofFn b) (List.ofFn c) depth [] [] [] regs
  let d1 := (Atom.push (12 : Fin 18) (3 : Fin 16)).eval d0
  let d2 := copyState (0 : Fin 18) 3 d1
  have e1 := Eval.base (StructuredProgram.Eval.atom (.push 12 3) d0)
  have e2 := copy_eval (0 : Fin 18) 3 17 d1 (by decide) (by decide) (by decide)
    (by simp [d1, d0, pairState, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg, execInstr])
  obtain ⟨r3, e3, h3⟩ := nonconstantCall_eval (3 : Fin 18) a d2
    (by simp [d2, d1, d0, copyState, StackRoutines.copyStacks, pairState,
      Atom.eval, Atom.instr, StructuredProgram.State.ofCfg, execInstr])
  let d3 := afterOne fourRegisters (3 : Fin 18) r3 [] d2
  let d4 := (Atom.push (12 : Fin 18) (3 : Fin 16)).eval d3
  let d5 := copyState (1 : Fin 18) 3 d4
  have e4 := Eval.base (StructuredProgram.Eval.atom (.push 12 3) d3)
  have e5 := copy_eval (1 : Fin 18) 3 17 d4 (by decide) (by decide) (by decide)
    (by simp [d4, d3, d2, d1, d0, afterOne, copyState, StackRoutines.copyStacks,
      pairState, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg, execInstr])
  obtain ⟨r6, e6, h6⟩ := nonconstantCall_eval (3 : Fin 18) b d5
    (by simp [d5, d4, d3, d2, d1, d0, afterOne, copyState, StackRoutines.copyStacks,
      pairState, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg, execInstr])
  let d6 := afterOne fourRegisters (3 : Fin 18) r6 [] d5
  let d7 := atomsResult pairFlagsAtoms d6
  have e7 := Eval.base (atoms_eval pairFlagsAtoms d6)
  have hs : d6.stacks 12 = [IrreducibleSearch.nonconstant a, regs 3] := by
    change d3.regs 3 = IrreducibleSearch.nonconstant a at h3
    simpa [d6, d5, d4, afterOne, copyState, StackRoutines.copyStacks,
      Atom.eval, Atom.instr, StructuredProgram.State.ofCfg, StructuredProgram.State.withPC,
      execInstr, d3, d2, d1, d0, pairState] using h3
  have hv : d7.regs 3 =
      !(IrreducibleSearch.nonconstant a && IrreducibleSearch.nonconstant b && regs 3) := by
    change d6.regs 3 = IrreducibleSearch.nonconstant b at h6
    simp [d7, atomsResult, pairFlagsAtoms, Atom.eval, Atom.instr,
      StructuredProgram.State.ofCfg, execInstr,
      readRegs, hs, h6]
  have hend : d7 = pairState (List.ofFn a) (List.ofFn b) (List.ofFn c) depth [] [] [] d7.regs := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    funext i; fin_cases i <;>
      simp [d7, d6, d5, d4, d3, d2, d1, d0, atomsResult, pairFlagsAtoms,
        afterOne, copyState, StackRoutines.copyStacks, pairState, Atom.eval,
        Atom.instr, StructuredProgram.State.ofCfg, execInstr]
  have he := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq e7)))))
  change Eval pairTailCommand _ d0 d7 at he
  rw [hend] at he
  refine ⟨_, d7.regs, ?_, he, hv⟩
  simp [ d4, d3, d2, d1, d0, afterOne, copyState, StackRoutines.copyStacks,
    pairState, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg, execInstr, coefficientArray_length, pairFlagsAtoms]
  omega

theorem pairCommand_eval {d : ℕ} (c : Fin d → IrreducibleSearch.F)
    (a b : Fin (d + 1) → IrreducibleSearch.F) (depth : List Bool)
    (hlen : depth.length = d) (regs : Fin 16 → Bool) :
    ∃ steps rf, steps ≤ 14000 * (d + 1)^2 ∧
      Eval pairCommand steps
        (pairState (List.ofFn a) (List.ofFn b) (List.ofFn c) depth [] [] [] regs)
        (pairState (List.ofFn a) (List.ofFn b) (List.ofFn c) depth [] [] [] rf) ∧
      rf 3 = IrreducibleSearch.pairPass c (a, b) := by
  obtain ⟨n, r1, hn, e1, h1⟩ := productCheckCommand_eval c a b depth hlen regs
  obtain ⟨m, r2, hm, e2, h2⟩ := pairTailCommand_eval c a b depth r1
  refine ⟨n+m, r2, by nlinarith, e1.seq e2, ?_⟩
  simpa only [h1, IrreducibleSearch.pairPass] using h2

theorem pairProgram_run {d : ℕ} (c : Fin d → IrreducibleSearch.F)
    (a b : Fin (d + 1) → IrreducibleSearch.F) (depth : List Bool)
    (hlen : depth.length = d) (regs : Fin 16 → Bool) :
    ∃ rf, rf 3 = IrreducibleSearch.pairPass c (a,b) ∧
      RunsIn pairProgram (14000 * (d + 1)^2 + 1)
        ((pairState (List.ofFn a) (List.ofFn b) (List.ofFn c) depth [] [] [] regs).withPC
          (some pairProgram.entry))
        ((pairState (List.ofFn a) (List.ofFn b) (List.ofFn c) depth [] [] [] rf).withPC none) := by
  obtain ⟨n, rf, hn, he, hv⟩ := pairCommand_eval c a b depth hlen regs
  exact ⟨rf, hv, n+1, by omega, compiled_halt_trace he 13 13⟩


end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchNativeScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native irreducible-polynomial search: concrete factor callbacks,
saved universal scans, exact ordered candidate selection, and measured cost. -/

/-! A fixed factor-pair callback and universal scan. All checker arithmetic,
record extraction, array splitting, and cleanup use explicit bit programs. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchFactorControl

open BitProgram StructuredCalls IrreducibleSearchProgram
open Subexp.BlockSearchPreparation (restrictState lifted_call)
attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod

theorem split_restrict (as bs cs : List IrreducibleSearch.F)
    (depth count source saved extra : List Bool) (regs : Fin 16 → Bool) :
    restrictState lowRegs splitStacks
      (wide (pairState [] (as ++ bs) cs depth [] [] [] regs)
        false false false source [] saved count extra) =
    IrreducibleSearchPairAdapter.input as bs count regs := by
  apply SubexpScanPrimitives.state_ext
  · funext i; simp [restrictState, lowRegs, wide, IrreducibleSearchPairAdapter.input, pairState]
  · funext i; fin_cases i <;>
      simp [restrictState, splitStacks, wide, pairState, IrreducibleSearchPairAdapter.input]

theorem split_embed (as bs cs : List IrreducibleSearch.F)
    (depth count source saved extra : List Bool) (regs rf : Fin 16 → Bool) :
    embedState lowRegs splitStacks
      (wide (pairState [] (as ++ bs) cs depth [] [] [] regs)
        false false false source [] saved count extra)
      (IrreducibleSearchPairAdapter.output as bs count rf) =
      wide (pairState as bs cs depth [] [] [] rf)
        false false false source [] saved count extra := by
  apply SubexpScanPrimitives.embedState_eq lowRegs splitStacks lowRegs_injective splitStacks_injective
  · intro i; simp [wide, lowRegs, IrreducibleSearchPairAdapter.output, pairState]
  · intro i; fin_cases i <;>
      simp [wide, splitStacks, IrreducibleSearchPairAdapter.output, pairState]
  · intro j hj
    revert hj
    refine Fin.addCases (m := 16) (n := 3) (fun i => ?_) (fun i => ?_) j
    · intro hi; exact (hi ⟨i,rfl⟩).elim
    · intro _; simp [wide]
  · intro j hj
    have h0 : j ≠ 0 := fun h => hj ⟨4, by simpa [splitStacks] using h.symm⟩
    have h1 : j ≠ 1 := fun h => hj ⟨0, by simpa [splitStacks] using h.symm⟩
    fin_cases j <;> simp_all [wide, pairState]

theorem split_eval (as bs cs : List IrreducibleSearch.F)
    (depth count source saved extra : List Bool) (hc : count.length = as.length)
    (regs : Fin 16 → Bool) :
    ∃ n rf, n ≤ 28 * count.length + 17 ∧ Eval split n
      (wide (pairState [] (as ++ bs) cs depth [] [] [] regs)
        false false false source [] saved count extra)
      (wide (pairState as bs cs depth [] [] [] rf)
        false false false source [] saved count extra) := by
  obtain ⟨rf, hr⟩ := IrreducibleSearchPairAdapter.program_runsIn as bs count hc regs
  obtain ⟨n, hn, he⟩ := lifted_call IrreducibleSearchPairAdapter.program lowRegs splitStacks
    lowRegs_injective splitStacks_injective
    (wide (pairState [] (as ++ bs) cs depth [] [] [] regs)
      false false false source [] saved count extra)
    (IrreducibleSearchPairAdapter.output as bs count rf) (28 * count.length + 17)
    (by rw [split_restrict]; exact hr)
  exact ⟨n, rf, hn, by simpa only [split, split_embed] using he⟩


theorem unpack_eval (as bs cs : List IrreducibleSearch.F)
    (depth count source saved extra : List Bool) (regs : Fin 16 → Bool) :
    Eval unpack (3 * (coefficientArray (as ++ bs)).length + 3)
      (wide (pairState [] [] cs depth [] [] [] regs)
        false true false source (coefficientArray (as ++ bs)).reverse saved count extra)
      (wide (pairState [] (as ++ bs) cs depth [] [] [] regs)
        false false false source [] saved count extra) := by
  let before := wide (pairState [] [] cs depth [] [] [] regs)
    false true false source (coefficientArray (as ++ bs)).reverse saved count extra
  have he := Subexp.TupleProgram.transfer_eval (19 : Fin 24) 1 (16 : Fin 19) 17
    (by decide) (by decide) before
  have hend : (⟨readRegs before.regs 16 17 none,
      StackRoutines.transferStacks 19 1 before.stacks⟩ : Data) =
      wide (pairState [] (as ++ bs) cs depth [] [] [] regs)
        false false false source [] saved count extra := by
    apply SubexpScanPrimitives.state_ext
    · funext i; fin_cases i <;> simp [before, wide, pairState, readRegs]
    · funext i; fin_cases i <;>
        simp [before, wide, pairState, StackRoutines.transferStacks]
  rw [hend] at he
  simpa [unpack, before, wide, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using he

theorem tail_eval (as bs cs : List IrreducibleSearch.F)
    (depth count source saved extra : List Bool) (regs : Fin 16 → Bool) :
    Eval (.seq saveResult (.seq (clear 0) (.seq (clear 1) presentTrue)))
      (4 * as.length + 4 * bs.length + 8)
      (wide (pairState as bs cs depth [] [] [] regs)
        false false false source [] saved count extra)
      (wide (pairState [] [] cs depth [] [] [] regs)
        false true (regs 3) source [] saved count extra) := by
  let d0 := wide (pairState as bs cs depth [] [] [] regs)
    false false false source [] saved count extra
  let d1 := (StructuredProgram.Atom.copy (18 : Fin 19) 3).eval d0
  let d2 : Data := ⟨readRegs d1.regs 16 17 none, StackRoutines.clearStacks 0 d1.stacks⟩
  let d3 : Data := ⟨readRegs d2.regs 16 17 none, StackRoutines.clearStacks 1 d2.stacks⟩
  let d4 := (StructuredProgram.Atom.set (17 : Fin 19) true).eval d3
  have e1 : Eval saveResult 1 d0 d1 := .base (.atom _ _)
  have e2 := Subexp.TupleProgram.clear_eval (0 : Fin 24) (16 : Fin 19) 17 d1
  have e3 := Subexp.TupleProgram.clear_eval (1 : Fin 24) (16 : Fin 19) 17 d2
  have e4 : Eval presentTrue 1 d3 d4 := .base (.atom _ _)
  have he := e1.seq (e2.seq (e3.seq e4))
  have hend : d4 = wide (pairState [] [] cs depth [] [] [] regs)
      false true (regs 3) source [] saved count extra := by
    apply SubexpScanPrimitives.state_ext
    · funext i; fin_cases i <;>
        simp [d4, d3, d2, d1, d0, wide, pairState, readRegs,
          StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg, execInstr]
    · funext i; fin_cases i <;>
        simp [d4, d3, d2, d1, d0, wide, pairState, StackRoutines.clearStacks,
          StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg, execInstr]
  rw [hend] at he
  convert he using 1 ;
    simp [ d2, d1, d0, wide, pairState, StackRoutines.clearStacks,
      StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr,
      coefficientArray_length] ; omega


theorem record_state_wide (low : State 16 18) (tag present found v pr f : Bool)
    (source payload saved count extra newSource newPayload : List Bool) :
    RecordPrograms.state ports (wide low tag present found source payload saved count extra)
      v pr f newSource newPayload = wide low v pr f newSource newPayload saved count extra := by
  apply SubexpScanPrimitives.state_ext
  · funext i; fin_cases i <;> simp [RecordPrograms.state, ports, wide]
  · funext i; fin_cases i <;> simp [RecordPrograms.state, ports, wide]

theorem factorRecords_all {d : ℕ} (c : Fin d → IrreducibleSearch.F) :
    (factorRecords d).all (factorTest c) = IrreducibleSearch.passes c := by
  simp only [factorRecords, List.all_map, Function.comp_def, factorTest_encode,
    IrreducibleSearch.passes]

end SubexponentialSAT.SqrtLog.IrreducibleSearchFactorControl

/-! Fixed first-success scan using the concrete saved factor checker. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchCandidateControl

open BitProgram StructuredCalls IrreducibleSearchProgram
open Subexp.BlockSearchPreparation (restrictState lifted_call)
open SubexpEnumerationPayload SubexpTupleRefinement
attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod

theorem prepare_eval {d : ℕ} (c : Fin d → IrreducibleSearch.F)
    (old : List IrreducibleSearch.F) (depth count source extra : List Bool)
    (regs : Fin 16 → Bool) (tag present found : Bool) :
    Eval (.seq clearCandidate unpack) (4 * old.length + 6 * d + 6)
      (wide (readyLow old depth count d regs tag present found)
        false true false source (coefficientArray (List.ofFn c)).reverse extra)
      (wide (readyLow (List.ofFn c) depth count d regs tag present found)
        false false false source [] extra) := by
  let d0 := wide (readyLow old depth count d regs tag present found)
    false true false source (coefficientArray (List.ofFn c)).reverse extra
  let d1 : Data := ⟨readRegs d0.regs 19 20 none, StackRoutines.clearStacks 13 d0.stacks⟩
  let d2 : Data := ⟨readRegs d1.regs 19 20 none, StackRoutines.transferStacks 25 13 d1.stacks⟩
  have e1 := Subexp.TupleProgram.clear_eval (13 : Fin 28) (19 : Fin 22) 20 d0
  have e2 := Subexp.TupleProgram.transfer_eval (25 : Fin 28) 13 (19 : Fin 22) 20
    (by decide) (by decide) d1
  have he := e1.seq e2
  have hend : d2 = wide (readyLow (List.ofFn c) depth count d regs tag present found)
      false false false source [] extra := by
    apply SubexpScanPrimitives.state_ext
    · funext i; fin_cases i <;>
        simp [d2, d1, d0, wide, readyLow, IrreducibleSearchFactorControl.wide,
          pairState, readRegs]
    · funext i; fin_cases i <;>
        simp [d2, d1, d0, wide, readyLow, IrreducibleSearchFactorControl.wide,
          pairState, StackRoutines.clearStacks, StackRoutines.transferStacks]
  change Eval (.seq clearCandidate unpack) _ d0 d2 at he
  rw [hend] at he
  convert he using 1 ;
    simp [d1, d0, wide, readyLow, IrreducibleSearchFactorControl.wide, pairState,
      StackRoutines.clearStacks, coefficientArray_length] ; omega

theorem finish_eval {d : ℕ} (c : Fin d → IrreducibleSearch.F)
    (depth count source extra : List Bool) (regs : Fin 16 → Bool) :
    Eval (.seq saveResult presentTrue) 2
      (wide (readyLow (List.ofFn c) depth count d regs false true (IrreducibleSearch.passes c))
        false false false source [] extra)
      (wide (readyLow (List.ofFn c) depth count d regs false true (IrreducibleSearch.passes c))
        false true (IrreducibleSearch.passes c) source [] extra) := by
  let d0 := wide (readyLow (List.ofFn c) depth count d regs false true (IrreducibleSearch.passes c))
    false false false source [] extra
  let d1 := (StructuredProgram.Atom.copy (21 : Fin 22) 18).eval d0
  let d2 := (StructuredProgram.Atom.set (20 : Fin 22) true).eval d1
  have e1 : Eval saveResult 1 d0 d1 := .base (.atom _ _)
  have e2 : Eval presentTrue 1 d1 d2 := .base (.atom _ _)
  have he := e1.seq e2
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  apply SubexpScanPrimitives.state_ext
  · funext i; fin_cases i <;>
      simp [d2, d1, d0, wide, readyLow, IrreducibleSearchFactorControl.wide,
        StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr]
  · funext i; fin_cases i <;>
      simp [d2, d1, d0, wide, readyLow, IrreducibleSearchFactorControl.wide,
        StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr]

end SubexponentialSAT.SqrtLog.IrreducibleSearchCandidateControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchBootstrap
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


namespace SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

open BitProgram StructuredCalls
open SubexpEnumerationPayload SubexpTupleRefinement IrreducibleSearchProgram
attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod

def searchProgram := compiled searchCommand 14 13


end SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScalarCacheCell
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The unsigned cache recurrence is executed by a one-bit shift followed by
the original finite little-endian adder. Its representation growth is linear
in the number of cells; no canonical-word assumption is used. -/

/-! One complete cache-row transform, including record parsing and preserving
emission of every newly computed value. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

abbrev cacheEmit : Cmd 8 18 :=
  liftCommand LayoutScalarEmitter.emitPair 0 2 id cacheEmitPorts

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

/-! Complete reusable cache pass: read one encoded row, compute and emit its
new row, append the end marker, reverse the output, and clear the carry. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

abbrev cacheFinishList : Cmd 8 18 :=
  liftCommand LayoutScalarEmitter.finishList 2 6 id cacheFinishPorts

abbrev cacheClear : Cmd 8 18 := .call (StackRoutines.clearProgram 0 0 1)

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

/-! The number of coefficient-cache rows is runtime unary data. This fixed
loop invokes the complete paid row pass and preserves the current encoded row.
-/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

abbrev cacheRead : Cmd 8 18 := .base (.atom (.pop 17 7 6))

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

/-! The physical unsigned cache computes the original coefficient recurrence's
natural magnitudes, in ascending degree order. -/

/-! A fixed loop builds the initial all-one cache row from a runtime unary
length. The constant program contains one record, independent of that length. -/

/-! One fixed program builds the complete unsigned H cache from the unary
runtime parameters A and R. No coefficient or initial cache is free input. -/

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

abbrev addLocal : Cmd 8 3 :=
  .seq (.base (.atom (.set 0 false))) (.call BinaryPrograms.Add.littleEndianProgram)

abbrev addCommand : Cmd 8 18 := liftCommand addLocal 0 0 id addPorts

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

/-! One paid Pascal row pass over the framed cache. -/

/-! A fixed while loop consumes the runtime unary iteration count. -/

/-! A fixed loop builds the initial zero cache row from a runtime unary
length. The constant program contains one record, independent of that length. -/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram
open SubexponentialSAT.SqrtLog.LayoutProgramScalar

def zeroPorts : UnaryForPrograms.Ports 8 18 := ⟨17,7,6⟩

abbrev zeroBody : Cmd 8 18 := ArithmeticExpressionSupport.pushWord 15 zeroRecord

abbrev zeroCommand : Cmd 8 18 :=
  .seq (ArithmeticExpressionSupport.pushWord 15 [false])
    (UnaryForPrograms.forCmd zeroPorts zeroBody)



abbrev initialPop : Cmd 8 18 := .base (.atom (.pop 17 7 6))

abbrev initialCommand : Cmd 8 18 :=
  .seq initialPop (.ite 6
    (.seq zeroCommand (ArithmeticExpressionSupport.pushWord 15 [true,true,true,false,false]))
    (ArithmeticExpressionSupport.pushWord 15 [false]))

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

/-! One fixed program builds the complete unsigned binomial row from the unary
runtime parameters h and R. No coefficient or initial cache is free input. -/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram
open SubexponentialSAT.SqrtLog.LayoutProgramScalar

abbrev initialBuild : Cmd 8 19 :=
  .call (ProgramLinking.liftProgram (compiled initialCommand 17 15) id initialBuildPorts)

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

/-! A fixed component routine copies the runtime width, pads or truncates one
word, and consumes that word into a reverse output buffer. -/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.MatrixProgramSupport
open SubexponentialSAT.SqrtLog.LayoutProgram

abbrev normalizeComponent : Cmd 8 9 :=
  .seq (copy 1 3 4) (.seq (normalizeAt normalizePorts) (transfer 0 2))

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

/-! Generic framed unsigned rows are converted to flat signed-component
arrays at a supplied runtime width. Both output arrays are physically built.
-/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.LayoutProgramScalar
open SubexponentialSAT.SqrtLog.RowSelectionProgram

abbrev flatParse : Cmd 8 19 := liftCommand parse 15 15 id basePorts

abbrev flatPositive : Cmd 8 19 := liftCommand normalizeComponent 0 2 id positivePorts
abbrev flatNegative : Cmd 8 19 := liftCommand normalizeComponent 0 2 id negativePorts

abbrev flatRow : Cmd 8 19 :=
  .seq flatParse (.while 7 (.seq flatPositive (.seq flatNegative flatParse)))

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

/-! Finish the generic cache adapter by reversing both physically accumulated
arrays. The common width is preserved for downstream indexed reads. -/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.MatrixProgramSupport
open SubexponentialSAT.SqrtLog.RowSelectionProgram
open SubexponentialSAT.SqrtLog.LayoutProgramScalar

abbrev flatFinish : Cmd 8 19 := .seq (transfer 16 0) (transfer 17 1)

abbrev flatCommand : Cmd 8 19 := .seq flatRow flatFinish
def flatProgram := compiled flatCommand 15 0

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

/-! Value and shape contracts for the generic adapter and binomial row. -/

/-! Complete fixed-control binomial cache construction. The three parameters
are runtime unary stacks; the output consists of actual flat fixed-width
positive and negative arrays in increasing column order. -/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

abbrev finalFlatten : Cmd 8 20 := .call (ProgramLinking.liftProgram flatProgram id flatFinalPorts)

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutDenominatorProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native exponentiation for the common layout denominator. The unary
row parameter is retained at239; the represented half starts at255 and one at250.
The output252 is computed by exactly `R-1` native multiplications. -/
namespace SubexponentialSAT.SqrtLog.LayoutDenominatorProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open CRTLocalProgram (ServiceSpec LowFrame lowFrame_update nativeRepeat binaryStep )

def powerCommand (multiply : Code) : Code :=
  .seq (copy 255 241) (.seq (copy 250 240) (.seq (copy 239 246)
    (.seq (popToken 246) (.seq (nativeRepeat (binaryStep multiply))
      (.seq (copy 240 252) (.seq (clear 240) (.seq (clear 241) (clear 255))))))))

theorem popToken_tail_run (s : Store) (i : Fin 256) :
    ExecutesIn (popToken i) 1 s (Function.update s i (s i).tail) := by
  intro regs
  refine ⟨1, readRegs regs 0 1 (s i).head?, le_rfl, ?_⟩
  have h := StructuredProgram.Eval.atom (StructuredProgram.Atom.pop i 0 1)
    (⟨regs,s⟩ : Data)
  simpa [popToken, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr]
    using Eval.base h

end SubexponentialSAT.SqrtLog.LayoutDenominatorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutDenominatorProgramQueryCode
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The per-query denominator is computed in a disjoint 256-stack bank. The
only persistent output is stack 728; the runtime exponent is read from 740. -/
namespace SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQuery
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

def view (a : LocalData) : SubexpConvolutionControl.Data :=
  ⟨a.regs,fun i => a.stacks (port i)⟩

def localInput (a : LocalData) : SubexpConvolutionControl.Store := fun i =>
  if i=194 then a.stacks 194 else
  if i=201 then a.stacks 201 else
  if i=202 then a.stacks 202 else
  if i=203 then a.stacks 203 else
  if i=204 then a.stacks 204 else
  if i=249 then a.stacks 280 else
  if i=250 then a.stacks 207 else
  if i=251 then a.stacks 211 else
  if i=239 then a.stacks 740 else
  if i=253 then a.stacks 253 else []

theorem staged_view (a : LocalData) (hc : ∀i∈bank,a.stacks i=[]) :
    (view (staged a)).stacks = localInput a := by
  funext i
  have hz := hc (port i) (by rw [mem_bank]; simp only [port]; omega)
  have val (p : Fin 768 × Fin 768) (hp : p∈pairs) :=
    copyMany_value pairs a pairs_distinct (fun p hp => hc p.2 (pairs_destination p hp))
      pairs_separated p hp
  by_cases h194 : i=194
  · subst i
    change (staged a).stacks 534=a.stacks 194
    exact val (194,534) (by simp [pairs])
  by_cases h201 : i=201
  · subst i
    change (staged a).stacks 541=a.stacks 201
    exact val (201,541) (by simp [pairs])
  by_cases h202 : i=202
  · subst i
    change (staged a).stacks 542=a.stacks 202
    exact val (202,542) (by simp [pairs])
  by_cases h203 : i=203
  · subst i
    change (staged a).stacks 543=a.stacks 203
    exact val (203,543) (by simp [pairs])
  by_cases h204 : i=204
  · subst i
    change (staged a).stacks 544=a.stacks 204
    exact val (204,544) (by simp [pairs])
  by_cases h249 : i=249
  · subst i
    change (staged a).stacks 589=a.stacks 280
    exact val (280,589) (by simp [pairs])
  by_cases h250 : i=250
  · subst i
    change (staged a).stacks 590=a.stacks 207
    exact val (207,590) (by simp [pairs])
  by_cases h251 : i=251
  · subst i
    change (staged a).stacks 591=a.stacks 211
    exact val (211,591) (by simp [pairs])
  by_cases h239 : i=239
  · subst i
    change (staged a).stacks 579=a.stacks 740
    exact val (740,579) (by simp [pairs])
  by_cases h253 : i=253
  · subst i
    change (staged a).stacks 593=a.stacks 253
    exact val (253,593) (by simp [pairs])
  have hp : ∀p∈pairs,port i≠p.2 := by
    intro p hp
    simp only [pairs,List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      intro he <;> have hv := congrArg Fin.val he <;>
      simp only [port] at hv <;>
      simp only [Fin.ext_iff] at h194 h201 h202 h203 h204 h249 h250 h251 h239 h253 <;> omega
  change (copyManyState pairs a).stacks (port i)=_
  rw [copyMany_frame pairs a (port i) hp,hz]
  simp [localInput,h194,h201,h202,h203,h204,h249,h250,h251,h239,h253]

end SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQuery

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutDenominatorProgramQueryRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQuery
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage
open SubexpLiftRing SubexpQuarticRing IntegerRingLiftProgram

theorem staged_outside (a : LocalData) (i : Fin 768) (hi : i∉bank) :
    (staged a).stacks i=a.stacks i := by
  apply copyMany_frame
  intro p hp he
  exact hi (he ▸ pairs_destination p hp)

end SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQuery

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutMatrixProgramSource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Relocatable finite-bank contract for integer incidence entries, and the
fixed physical storage layout used by the direct all-row matrix builder. -/
namespace SubexponentialSAT.SqrtLog.LayoutMatrixProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def entryState (base : Fin 288 → List Bool) (regs : Fin 16 → Bool)
    (row col P N : List Bool) : Data 256 :=
  ⟨regs,fun i => if i=252 then row else if i=253 then col else
    if i=254 then P else if i=255 then N else base (bankPort i)⟩

/-- This is a native command contract, not an entry-value oracle. Instantiation
requires an actual Eval of the fixed finite instruction program. Cache and
workspace contents are restored exactly; only the four entry ports vary. -/
def EntryContract (entry : Code 256) (base : Fin 288 → List Bool)
    (Valid : ℕ → ℕ → Prop) (Rel : ℕ → ℕ → Pair → Prop) (T B : ℕ) : Prop :=
  ∀ (regs : Fin 16 → Bool) (j v : ℕ), Valid j v →
    ∃ t ≤ T, ∃ rf result,
      Eval entry t (entryState base regs (List.replicate j true) (List.replicate v true) [] [])
        (entryState base rf (List.replicate j true) (List.replicate v true) result.1 result.2) ∧
      Rel j v result ∧ pairLength result ≤ B

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutFiberSumProgramInterface
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Adapter from the native owner-fiber loop to the matrix builder's fixed-bank
entry contract.  The incidence callback is still an actual command/Eval premise;
there is no table of precomputed entry values. -/
namespace SubexponentialSAT.SqrtLog.LayoutFiberSumProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram

def matrixBase (base : Fin 288 → List Bool) (j : ℕ) : Data :=
  LayoutMatrixProgram.entryState base (fun _ => false) (unary j) [] [] []

end SubexponentialSAT.SqrtLog.LayoutFiberSumProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutMatrixProgramRowStep
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One actual matrix coefficient call followed by physical signed framing. -/
namespace SubexponentialSAT.SqrtLog.LayoutMatrixProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def clearColumn : Code 288 := .call (StackRoutines.clearProgram 278 0 1)

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutMatrixProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Direct all-incidence-row signed matrix construction by one fixed program.
The entry dependency is an explicit native finite-bank command contract. -/
namespace SubexponentialSAT.SqrtLog.LayoutMatrixProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def clearIDs : Code 288 := .call (StackRoutines.clearProgram 282 0 1)

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramConstantsModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The generated dynamic vectors are constants in the supplied ring model. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Constants

open SubexponentialSAT.SubexpQuarticRing SubexponentialSAT.SubexpLiftRing RingProgramTable
open scoped BigOperators

def constantCode {B : ℕ} (d : ℕ) (seed zeroWord : Word B) : RingProgram.Code (Word B) d :=
  fun i => if i.val = 0 then seed else zeroWord

theorem constantCode_flat {B : ℕ} (d : ℕ) (seed zeroWord : Word B) :
    RingProgram.flat (constantCode d seed zeroWord) = literalBits d seed zeroWord := by
  induction d generalizing seed with
  | zero => simp [RingProgram.flat,literalBits]
  | succ d ih =>
    rw [RingProgram.flat,List.ofFn_succ,List.flatten_cons]
    change seed.val ++ RingProgram.flat (fun i : Fin d => constantCode (d+1) seed zeroWord i.succ) = _
    have htail : (fun i : Fin d => constantCode (d+1) seed zeroWord i.succ) =
        constantCode d zeroWord zeroWord := by
      funext i
      simp [constantCode]
    rw [htail,ih]

end SubexponentialSAT.SqrtLog.LeafProgram.Constants

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingNodeProgramModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical radix generator emits precisely the coefficient encoding of
nodes in the actual supplied-polynomial unramified ring. -/
namespace SubexponentialSAT.SqrtLog.RingNodeProgram

open SubexponentialSAT BinaryArithmetic SubexpLiftRing SubexpQuarticRing
open RingProgram

/-- A fixed-width coefficient encoding of a base-three index. -/
def nodeCode (t d n : ℕ) : Code (ScalarCode 3 t) d :=
  fun j => ⟨fixedBits (baseWidth 3 t) (n / 3^j.val % 3), fixedBits_length _ _⟩

end SubexponentialSAT.SqrtLog.RingNodeProgram

end OAI.Algorithms
end

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

@[simp] theorem emit_nil (a : Accumulator) : emit [] a = a := by cases a; rfl

/-! The following induction rule accounts for actual executions of the fixed
payload body. Its premises will be proved for `termBody`, `groupBody`, and
`blockBody`; the exported whole-controller statement has no callback argument. -/

/-! ## Forward-output service boundary -/

end SubexponentialSAT.SubexpKernelControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_GlobalBasisEntryCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete framed-word, comparison, and scalar-cell services for the
global matrix entry callback. Register 6 is the persistent row-kind flag. -/

namespace SubexponentialSAT.Subexp.GlobalBasisEntryCore

open BitProgram StructuredCalls SubexpScanPrimitives

abbrev Code := Cmd 16 32

end SubexponentialSAT.Subexp.GlobalBasisEntryCore

end OAI.Algorithms
end


