-- Prove2me | Definitions.Def_OAIQ081S104
-- name    : OAIQ081S104
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:21:30.515842+00:00
-- url     : https://prove2.me/theorems/bb59fec5-614f-42f4-8c08-cf7f6d711c9b
-- title:
--   Definitions bundle OAIQ081S104 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 29 declarations of OpenAI's Lean: 14 definitions and 15 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.computeLog`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.inputData`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.logAt`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.metadataFromBinary`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.arithmeticService`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.newtonMachine`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.newtonProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.prepareOperands`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.registerBinary`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap.GeneratorReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap.state`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchCandidateControl.readyLow`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchFactorControl.wide`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.pairState`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramArrays`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramBoot`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramCleanup`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramEncoding`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramEntry`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramEntryRun`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramInput`, `SubexponentialSAT_SqrtLog_IdempotentProgramConstants`, `SubexponentialSAT_SqrtLog_IdempotentProgramFinal`, `SubexponentialSAT_SqrtLog_IdempotentProgramMachine`, `SubexponentialSAT_SqrtLog_IdempotentProgramRegisters`, `SubexponentialSAT_SqrtLog_IrreducibleSearch`, `SubexponentialSAT_SqrtLog_IrreducibleSearchBootstrapPreparation`, `SubexponentialSAT_SqrtLog_IrreducibleSearchNativeScan`, `SubexponentialSAT_SqrtLog_IrreducibleSearchProgram`, `SubexponentialSAT_SubexpBlockParameterProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S082`, `OAIQ081S083`, `OAIQ081S084`, `OAIQ081S085`, `OAIQ081S086` and `OAIQ081S087` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S120`, `OAIQ081S121`, `OAIQ081S122` and `OAIQ081S128`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.add_constant_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.loop_eval`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S082
import Definitions.Def_OAIQ081S083
import Definitions.Def_OAIQ081S084
import Definitions.Def_OAIQ081S085
import Definitions.Def_OAIQ081S086
import Definitions.Def_OAIQ081S087

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramArrays
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

theorem popCounts_eval (drop n : ℕ) (d : Data)
    (hc : d.stacks 1 = List.replicate (n+drop) true) :
    ∃ rf, Eval (popCounts drop) drop d
      ⟨rf, Function.update d.stacks 1 (List.replicate n true)⟩ := by
  induction drop generalizing d with
  | zero =>
      simp only [Nat.add_zero] at hc
      refine ⟨d.regs, ?_⟩
      simpa [popCounts,←hc] using (Eval.base (StructuredProgram.Eval.skip d))
  | succ drop ih =>
      let a : Data := ⟨readRegs d.regs 0 1 (some true),
        Function.update d.stacks 1 (List.replicate (n+drop) true)⟩
      have hp : Eval popCount 1 d a := by
        have hh : d.stacks 1 = true :: List.replicate (n+drop) true := by
          simpa only [Nat.add_succ,List.replicate_succ] using hc
        have h := Eval.base (StructuredProgram.Eval.atom
          (StructuredProgram.Atom.pop (r:=8) (s:=41) 1 0 1) d)
        change Eval popCount 1 d ⟨readRegs d.regs 0 1 (d.stacks 1).head?,
          Function.update d.stacks 1 (d.stacks 1).tail⟩ at h
        simpa only [hh,List.head?_cons,List.tail_cons] using h
      obtain ⟨rf,hr⟩ := ih a (by simp [a])
      refine ⟨rf,?_⟩
      simpa [popCounts,a,Function.update_idem,Nat.add_comm] using hp.seq hr

theorem paddedZeros_eval (d : Data) (target : Fin 41) (drop n : ℕ)
    (hd : d.stacks 37 = List.replicate (n+drop) true)
    (h1 : d.stacks 1 = []) (h2 : d.stacks 2 = [])
    (ht1 : target ≠ 1) (ht2 : target ≠ 2) (ht17 : target ≠ 17) :
    ∃ rf, Eval (paddedZeros target drop)
      (7*(n+drop)+5+drop+(n*(7*(d.stacks 17).length+7)+6)) d
      ⟨rf, Function.update d.stacks target
        (Subexp.BlockCopyProgram.copies n (d.stacks 17) ++ d.stacks target)⟩ := by
  let a := afterCopy d 37 1 0 1
  have hc := copy_eval d 37 1 2 0 1 (by decide) (by decide) (by decide) (by decide) h2
  obtain ⟨rf,hp⟩ := popCounts_eval drop n a
    (by simp [a,afterCopy,StackRoutines.copyStacks,hd,h1])
  let b : Data := ⟨rf,Function.update a.stacks 1 (List.replicate n true)⟩
  have hbs : b.stacks = Function.update d.stacks 1 (List.replicate n true) := by
    simp [b,a,afterCopy,StackRoutines.copyStacks,Function.update_idem]
  have hr := repeatAt_eval b 17 target 2 1 (by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [repeatPorts,Ne.symm ht1,Ne.symm ht2,Ne.symm ht17])
    n (by simp [hbs]) (by simp [hbs,h2])
  have he := hc.seq (hp.seq hr)
  let final := repeated b target 1 n (b.stacks 17)
  have hs : final.stacks = Function.update d.stacks target
      (Subexp.BlockCopyProgram.copies n (d.stacks 17) ++ d.stacks target) := by
    simp [final,repeated,hbs,ht1,Function.update_idem,←h1]
  refine ⟨final.regs,?_⟩
  have hf : final = ⟨final.regs,Function.update d.stacks target
      (Subexp.BlockCopyProgram.copies n (d.stacks 17) ++ d.stacks target)⟩ := state_ext rfl hs
  change Eval _ _ _ final at he
  rw [hf] at he
  convert he using 1 ; simp [hd,hbs] ; omega

theorem negativeOneArray_eval (d : Data) (n : ℕ)
    (hd : d.stacks 37 = List.replicate (n+1) true)
    (h1 : d.stacks 1 = []) (h2 : d.stacks 2 = []) (h36 : d.stacks 36 = []) :
    ∃ rf, Eval negativeOneArray
      (7*(n+1)+5+1+(n*(7*(d.stacks 17).length+7)+6)+(7*(d.stacks 28).length+5)) d
      ⟨rf,Function.update d.stacks 36
        (d.stacks 28 ++ Subexp.BlockCopyProgram.copies n (d.stacks 17))⟩ := by
  obtain ⟨ra,ha⟩ := paddedZeros_eval d 36 1 n hd h1 h2 (by decide) (by decide) (by decide)
  let a : Data := ⟨ra,Function.update d.stacks 36
    (Subexp.BlockCopyProgram.copies n (d.stacks 17))⟩
  have ha' : Eval (paddedZeros 36 1)
      (7*(n+1)+5+1+(n*(7*(d.stacks 17).length+7)+6)) d a := by
    simpa [a,h36] using ha
  have hb := copy_eval a 28 36 2 0 1 (by decide) (by decide) (by decide)
    (by decide) (by simp [a,h2])
  have he := ha'.seq hb
  refine ⟨(afterCopy a 28 36 0 1).regs,?_⟩
  simpa [negativeOneArray,a,afterCopy,StackRoutines.copyStacks,Function.update_idem] using he

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramInput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The unary iteration budget is derived from the runtime binary t word.
This module includes its native conversion trace and preserves the original
word for modulus construction. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

open BitProgram StructuredCalls SubexpScanPrimitives

abbrev logAt : Cmd 8 41 := .seq resetThree
  (.call (ProgramLinking.liftProgram Log.program repeatRegisters logPorts))

theorem logAt_eval (d : Data) (h40 : d.stacks 40 = []) (h0 : d.stacks 0 = [])
    (ht : 0 < CounterPrograms.value (d.stacks 39)) :
    ∃ word n rf, CounterPrograms.value word = Nat.clog 2 (CounterPrograms.value (d.stacks 39)) ∧
      word.length ≤ (d.stacks 39).length+1 ∧ n ≤ 3+65*((d.stacks 39).length+2)^2 ∧
      Eval logAt n d ⟨rf,Function.update d.stacks 39 word⟩ := by
  obtain ⟨word,hv,hl,n,hn,hr⟩ := Log.program_runs (d.stacks 39) ht
  change Trace Log.program n ((Log.io (d.stacks 39)).withPC (some Log.program.entry))
    ((Log.io word).withPC none) at hr
  let a := resetData d
  let out := Log.io word
  have hi : embedState repeatRegisters logPorts a (Log.io (d.stacks 39)) = a := by
    apply embedState_eq _ _ repeatRegisters_injective logPorts_injective
    · intro i
      fin_cases i <;> simp [a,resetData,repeatRegisters]
    · intro i
      fin_cases i <;> simp [a,resetData,logPorts,h40,h0]
    · intros; rfl
    · intros; rfl
  have he := eval_call_lifted Log.program repeatRegisters logPorts a
    repeatRegisters_injective logPorts_injective hr
  have ho : (embedState repeatRegisters logPorts a out).stacks =
      Function.update d.stacks 39 word := by
    funext j
    by_cases hj : ∃ i, logPorts i = j
    · obtain ⟨i,rfl⟩ := hj
      rw [embedState_stack _ _ _ _ logPorts_injective]
      fin_cases i <;> simp [out,logPorts,h40,h0]
    · rw [embedState_stack_frame _ _ _ _ j hj]
      have h39 : j ≠ 39 := fun h => hj ⟨0,by simpa [logPorts] using h.symm⟩
      simp [a,resetData,h39]
  have hout : embedState repeatRegisters logPorts a out =
      ⟨(embedState repeatRegisters logPorts a out).regs,Function.update d.stacks 39 word⟩ :=
    state_ext rfl ho
  refine ⟨word,3+n,(embedState repeatRegisters logPorts a out).regs,hv,hl,by omega,?_⟩
  change Eval _ n (embedState repeatRegisters logPorts a (Log.io (d.stacks 39)))
    (embedState repeatRegisters logPorts a out) at he
  rw [hi,hout] at he
  exact (resetThree_eval d).seq he

abbrev computeLog : Cmd 8 41 :=
  .seq (.call (StackRoutines.copyProgram 31 39 38 (0 : Fin 8) 1)) logAt

theorem computeLog_eval (d : Data) (h39 : d.stacks 39 = [])
    (h40 : d.stacks 40 = []) (h38 : d.stacks 38 = []) (h0 : d.stacks 0 = [])
    (ht : 0 < CounterPrograms.value (d.stacks 31)) :
    ∃ word n rf, CounterPrograms.value word = Nat.clog 2 (CounterPrograms.value (d.stacks 31)) ∧
      word.length ≤ (d.stacks 31).length+1 ∧
      n ≤ 7*(d.stacks 31).length+8+65*((d.stacks 31).length+2)^2 ∧
      Eval computeLog n d ⟨rf,Function.update d.stacks 39 word⟩ := by
  let a := afterCopy d 31 39 0 1
  have hc := copy_eval d 31 39 38 0 1 (by decide) (by decide) (by decide) (by decide) h38
  have ha39 : a.stacks 39 = d.stacks 31 := by simp [a,afterCopy,StackRoutines.copyStacks,h39]
  obtain ⟨word,n,rf,hv,hl,hn,he⟩ := logAt_eval a
    (by simp [a,afterCopy,StackRoutines.copyStacks,h40])
    (by simp [a,afterCopy,StackRoutines.copyStacks,h0]) (by simpa only [ha39] using ht)
  refine ⟨word,7*(d.stacks 31).length+5+n,rf,by simpa only [ha39] using hv,
    by simpa only [ha39] using hl,?_,?_⟩
  · simp only [ha39] at hn; omega
  · have hs : Function.update a.stacks 39 word = Function.update d.stacks 39 word := by
      simp [a,afterCopy,StackRoutines.copyStacks,Function.update_idem]
    rw [hs] at he
    exact hc.seq he

abbrev metadataFromBinary : Cmd 8 41 :=
  .seq unaryFromBinary (.seq metadataCommand computeLog)

theorem metadataFromBinary_eval (d : Data)
    (h0 : d.stacks 0 = []) (h1 : d.stacks 1 = []) (h2 : d.stacks 2 = [])
    (h12 : d.stacks 12 = []) (h28 : d.stacks 28 = [])
    (h29 : d.stacks 29 = []) (h30 : d.stacks 30 = [])
    (h37 : d.stacks 37 = []) (h38 : d.stacks 38 = [])
    (h39 : d.stacks 39 = []) (h40 : d.stacks 40 = [])
    (ht : 0 < CounterPrograms.value (d.stacks 31)) :
    ∃ word n rf, CounterPrograms.value word = Nat.clog 2 (CounterPrograms.value (d.stacks 31)) ∧
      word.length ≤ (d.stacks 31).length+1 ∧
      n ≤ 1000*(CounterPrograms.value (d.stacks 31)+(d.stacks 31).length+2)^2 ∧
      Eval metadataFromBinary n d ⟨rf,metadataStacks d.stacks word⟩ := by
  obtain ⟨nu,ru,hnu,hu⟩ := unaryFromBinary_eval d h28 h29 h30
  let a : Data := ⟨ru,Function.update d.stacks 29
    (List.replicate (CounterPrograms.value (d.stacks 31)) true)⟩
  obtain ⟨rm,hm⟩ := metadataCommand_eval a (CounterPrograms.value (d.stacks 31))
    (by simp [a]) (by simp [a,h0]) (by simp [a,h1]) (by simp [a,h2])
    (by simp [a,h12]) (by simp [a,h37])
  let b : Data := ⟨rm,Function.update (Function.update a.stacks
    12 (List.replicate (2*CounterPrograms.value (d.stacks 31)) true))
    37 (List.replicate (3*CounterPrograms.value (d.stacks 31)) true)⟩
  obtain ⟨word,nl,rl,hv,hl,hnl,he⟩ := computeLog_eval b
    (by simp [b,a,h39]) (by simp [b,a,h40]) (by simp [b,a,h38])
    (by simp [b,a,h0]) (by simpa [b,a] using ht)
  have hb31 : b.stacks 31 = d.stacks 31 := by simp [b,a]
  refine ⟨word,nu+(63*CounterPrograms.value (d.stacks 31)+48+nl),rl,
    by simpa only [hb31] using hv,by simpa only [hb31] using hl,?_,?_⟩
  · simp only [hb31] at hnl
    dsimp [CounterConversions.runtimeBound] at hnu
    nlinarith [Nat.zero_le (CounterPrograms.value (d.stacks 31)*(d.stacks 31).length)]
  · exact hu.seq (hm.seq he)

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

theorem state_update (r rf : Regs) (w : Words) (i : Fin 15) (word : List Bool) :
    (⟨rf, Function.update (state r w).stacks (port i) word⟩ : Data) =
      state rf (Function.update w i word) := by
  apply CounterForPrograms.data_ext <;> try rfl
  funext j
  by_cases hj : j.val < 15
  · simp [state, Function.update_apply, port, hj, Fin.ext_iff]
  · have hji : j ≠ port i := by
      intro he
      have he' : j.val = i.val := congrArg (fun x : Fin 22 => x.val) he
      have hi := i.isLt
      omega
    simp [state, Function.update_apply, hj, hji]

end SubexponentialSAT.SubexpBlockParameterProgram

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

def inputData (bits : List Bool) : Data :=
  ⟨fun _ => false,Function.update (fun _ => []) 31 bits⟩

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramCleanup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

open BitProgram StructuredCalls

theorem preparationCleanup_eval (d : Data) (W : ℕ)
    (hw : ∀ p ∈ preparationDiscard, (d.stacks p).length ≤ W) :
    ∃ n e, n ≤ 30*(2*W+3) ∧ Eval preparationCleanup n d e ∧
      ∀ i, e.stacks i = if i ∈ preparationDiscard then [] else d.stacks i := by
  refine ⟨clearPortsCost preparationDiscard d,clearedPorts preparationDiscard d,
    ?_,clearPorts_eval _ _,clearedPorts_stacks _ _⟩
  exact clearPortsCost_bound preparationDiscard d W hw

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

open SubexponentialSAT.SubexpQuarticRing

/-- A sparse constant vector is exactly one word followed by zero padding. -/
theorem flat_sparse {B dim : ℕ} (hd : 0 < dim) (first zero : Word B) :
    RingProgram.flat (fun i : Fin dim => if i.val = 0 then first else zero) =
      first.val ++ (List.replicate (dim-1) zero.val).flatten := by
  cases dim with
  | zero => omega
  | succ n =>
      simp [RingProgram.flat, List.ofFn_succ]

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramEncoding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

open SubexpSymbolicCost SubexpQuarticRing

theorem flat_three {B : ℕ} (n : ℕ) (a b c z : Word B) :
    RingProgram.flat (fun k : Fin (n+3) =>
      if k.val=0 then a else if k.val=1 then b else if k.val=2 then c else z) =
      a.val ++ b.val ++ c.val ++ Subexp.BlockCopyProgram.copies n z.val := by
  simp [RingProgram.flat,List.ofFn_succ,Subexp.BlockCopyProgram.copies,
    List.ofFn_const,List.append_assoc]

theorem initialRun_flat {B : ℕ} (ops : RingProgram (Word B)) (t : ℕ)
    (ht : 0 < t) (u : Word B) :
    RingProgram.flat (IdempotentProgram.initialRun ops t u).1 =
      (ops.addRun u u).1.val ++ (ops.negRun (ops.addRun (ops.addRun u u).1 u).1).1.val ++
        u.val ++ Subexp.BlockCopyProgram.copies (3*t-3) ops.zeroRun.1.val := by
  have hd : 3*t = (3*t-3)+3 := by omega
  change RingProgram.flat (fun k : Fin (3*t) =>
    if k.val=0 then (ops.addRun u u).1
    else if k.val=1 then (ops.negRun (ops.addRun (ops.addRun u u).1 u).1).1
    else if k.val=2 then u else ops.zeroRun.1) = _
  conv_lhs => rw [hd]
  exact flat_three _ _ _ _ _

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramEntry
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A table entry is selected by a fixed unary bit program and copied from
one of six scalar cache words. The table itself is constructed at runtime. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

open BitProgram StructuredCalls SubexpScanPrimitives
open IdempotentTableEntryProgram (codeBits outputPort entryCode)

theorem selector_eval (d : Data) (i j k : ℕ)
    (h0 : d.stacks 0 = List.replicate i true)
    (h1 : d.stacks 1 = List.replicate j true)
    (h2 : d.stacks 2 = List.replicate k true) (h3 : d.stacks 3 = []) :
    ∃ n rf zs bs, n ≤ 40*(i+j+k+1) ∧ zs.length+bs.length ≤ i+j+k ∧
      Eval selector n d
        ⟨rf,Function.update (Function.update (Function.update (Function.update d.stacks
          0 []) 1 []) 2 zs) 3 bs⟩ ∧
      (∀ z, rf (outputPort z) = codeBits (entryCode i j k) z) := by
  obtain ⟨n,rf,zs,bs,hn,hr,hcode,hsize⟩ :=
    IdempotentTableEntryProgram.program_trace i j k d.regs
  let a := IdempotentTableEntryProgram.data d.regs (List.replicate i true)
    (List.replicate j true) (List.replicate k true) []
  let b := IdempotentTableEntryProgram.data rf [] [] zs bs
  have hi : embedState id selectorPorts d a = d := by
    apply embedState_eq _ _ Function.injective_id selectorPorts_injective
    · intro z; rfl
    · intro z; fin_cases z <;> simp [a,IdempotentTableEntryProgram.data,selectorPorts,h0,h1,h2,h3]
    · intro z hz; exact False.elim (hz ⟨z,rfl⟩)
    · intros; rfl
  have hs : (embedState id selectorPorts d b).stacks =
      Function.update (Function.update (Function.update (Function.update d.stacks
        0 []) 1 []) 2 zs) 3 bs := by
    funext z
    by_cases hz : ∃ x, selectorPorts x = z
    · obtain ⟨x,rfl⟩ := hz
      rw [embedState_stack _ _ _ _ selectorPorts_injective]
      fin_cases x <;> simp [b,IdempotentTableEntryProgram.data,selectorPorts]
    · rw [embedState_stack_frame _ _ _ _ z hz]
      have hzero : z ≠ 0 := fun h => hz ⟨0,by simpa [selectorPorts] using h.symm⟩
      have hone : z ≠ 1 := fun h => hz ⟨1,by simpa [selectorPorts] using h.symm⟩
      have htwo : z ≠ 2 := fun h => hz ⟨2,by simpa [selectorPorts] using h.symm⟩
      have hthree : z ≠ 3 := fun h => hz ⟨3,by simpa [selectorPorts] using h.symm⟩
      simp [hzero,hone,htwo,hthree]
  have hb : embedState id selectorPorts d b =
      ⟨rf,Function.update (Function.update (Function.update (Function.update d.stacks
        0 []) 1 []) 2 zs) 3 bs⟩ := by
    apply state_ext
    · funext z
      exact embedState_register _ _ _ _ Function.injective_id z
    · exact hs
  have he := eval_call_lifted IdempotentTableEntryProgram.program id selectorPorts d
    Function.injective_id selectorPorts_injective hr
  refine ⟨n,rf,zs,bs,hn,hsize,?_,hcode⟩
  change Eval selector n (embedState id selectorPorts d a) (embedState id selectorPorts d b) at he
  simpa only [hi,hb] using he

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramEntryRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

open BitProgram StructuredCalls SubexpScanPrimitives
open IdempotentTableEntryProgram (codeBits outputPort entryCode)

theorem prepareEntry_eval (d : Data)
    (h0 : d.stacks 0 = []) (h1 : d.stacks 1 = [])
    (h2 : d.stacks 2 = []) (h4 : d.stacks 4 = []) :
    ∃ rf, Eval prepareEntry
      (7*((d.stacks 25).length+(d.stacks 26).length+(d.stacks 24).length)+15) d
      ⟨rf,Function.update (Function.update (Function.update d.stacks
        0 (d.stacks 25)) 1 (d.stacks 26)) 2 (d.stacks 24)⟩ := by
  let a := afterCopy d 25 0 0 1
  let b := afterCopy a 26 1 0 1
  have ha := copy_eval d 25 0 4 0 1 (by decide) (by decide) (by decide) (by decide) h4
  have hb := copy_eval a 26 1 4 0 1 (by decide) (by decide) (by decide) (by decide)
    (by simp [a,afterCopy,StackRoutines.copyStacks,h4])
  have hc := copy_eval b 24 2 4 0 1 (by decide) (by decide) (by decide) (by decide)
    (by simp [b,a,afterCopy,StackRoutines.copyStacks,h4])
  have he := ha.seq (hb.seq hc)
  refine ⟨(afterCopy b 24 2 0 1).regs,?_⟩
  convert he using 1 <;>
    simp [b,a,afterCopy,StackRoutines.copyStacks,h0,h1,h2] ; ring

theorem entryCommand_eval (d : Data) (i j k : ℕ)
    (hi : d.stacks 25 = List.replicate i true)
    (hj : d.stacks 26 = List.replicate j true)
    (hk : d.stacks 24 = List.replicate k true)
    (h0 : d.stacks 0 = []) (h1 : d.stacks 1 = [])
    (h2 : d.stacks 2 = []) (h3 : d.stacks 3 = []) (h4 : d.stacks 4 = []) :
    ∃ n rf, n ≤ 49*(i+j+k)+7*(d.stacks (entrySource (entryCode i j k))).length+69 ∧
      Eval entryCommand n d ⟨rf,Function.update d.stacks 22
        (d.stacks (entrySource (entryCode i j k)) ++ d.stacks 22)⟩ := by
  obtain ⟨ra,ha⟩ := prepareEntry_eval d h0 h1 h2 h4
  let a : Data := ⟨ra,Function.update (Function.update (Function.update d.stacks
    0 (d.stacks 25)) 1 (d.stacks 26)) 2 (d.stacks 24)⟩
  obtain ⟨ns,rs,zs,bs,hns,hsize,hs,hcode⟩ := selector_eval a i j k
    (by simp [a,hi]) (by simp [a,hj]) (by simp [a,hk]) (by simp [a,h3])
  let b : Data := ⟨rs,Function.update (Function.update (Function.update (Function.update a.stacks
    0 []) 1 []) 2 zs) 3 bs⟩
  obtain ⟨nc,rc,hnc,hc⟩ := dispatchEntry_eval b (entryCode i j k)
    (by simp [b,a,h4]) hcode
  let c : Data := ⟨rc,Function.update b.stacks 22
    (b.stacks (entrySource (entryCode i j k)) ++ b.stacks 22)⟩
  have hsource : b.stacks (entrySource (entryCode i j k)) =
      d.stacks (entrySource (entryCode i j k)) := by
    generalize entryCode i j k = code
    fin_cases code <;> simp [b,a,entrySource]
  have htwo := clearAt_eval c 2
  let e := clearResult c 2
  have hthree := clearAt_eval e 3
  have hout : (clearResult e 3).stacks = Function.update d.stacks 22
      (d.stacks (entrySource (entryCode i j k)) ++ d.stacks 22) := by
    simp only [e,clearResult,c,hsource]
    funext p
    by_cases hp22 : p = 22
    · subst p; simp [b,a]
    · by_cases hp0 : p = 0
      · subst p; simp [b,a,h0]
      · by_cases hp1 : p = 1
        · subst p; simp [b,a,h1]
        · by_cases hp2 : p = 2
          · subst p; simp [h2]
          · by_cases hp3 : p = 3
            · subst p; simp [h3]
            · simp [b,a,hp22,hp0,hp1,hp2,hp3]
  have hf : clearResult e 3 = ⟨(clearResult e 3).regs,Function.update d.stacks 22
      (d.stacks (entrySource (entryCode i j k)) ++ d.stacks 22)⟩ := state_ext rfl hout
  have he := ha.seq (hs.seq (hc.seq (htwo.seq hthree)))
  rw [hf] at he
  refine ⟨_,_,?_,he⟩
  have hc2 : (c.stacks 2).length = zs.length := by simp [c,b]
  have he3 : (e.stacks 3).length = bs.length := by simp [e,clearResult,c,b]
  simp only [hsource] at hnc
  simp only [hi,hj,hk,List.length_replicate,hc2,he3]
  omega

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramRegisters
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Source-preserving storage for the fixed Newton register machine. Every
copy, replacement, and clearing operation is an actual finite bit program. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open BitProgram StructuredCalls StackRoutines

/-- The cached unary degree is copied; the raw service may consume its copy. -/
abbrev prepareOperands (left right : Fin 41) : Cmd 8 41 :=
  .seq (registerCopy left 8)
    (.seq (registerCopy right 9) (registerCopy 37 11))

/-- The complete register operation has fixed syntax. `raw` is the shared
native service, lifted to the low 32 stacks. -/
abbrev registerBinary (raw : Cmd 8 41) (target left right : Fin 41) : Cmd 8 41 :=
  .seq (prepareOperands left right) (.seq raw (storeResult target))

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramMachine
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed four-array Newton machine. Its native services perform full dynamic
vector arithmetic, operand copying, and target replacement. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open BitProgram StructuredCalls SubexpSymbolicCost
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

/-- This instruction dispatcher is fixed, independent of every ring parameter. -/
def arithmeticService : ArithmeticInstruction → Cmd 8 41
  | .add dst x y => registerBinary (callService RingScan.serviceAdd)
      (arrayRegister dst) (arrayRegister x) (arrayRegister y)
  | .mul dst x y => registerBinary (callService RingScan.serviceMul)
      (arrayRegister dst) (arrayRegister x) (arrayRegister y)
  | .neg dst x => registerBinary (callService RingScan.serviceMul)
      (arrayRegister dst) 36 (arrayRegister x)

abbrev newtonMachine : Cmd 8 41 := nativeNewtonLoop newtonPorts arithmeticService

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramFinal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete native Newton lift and the exact degree-three coefficient output.
The input-state contract includes prepared scalar constants and the cached
H-adic table; native preparation is a separate remaining construction. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open scoped BigOperators
open BitProgram StructuredCalls SubexpSymbolicCost
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev newtonProgram : Program 8 41 (size newtonMachine+1) := compiled newtonMachine 32 32

end SubexponentialSAT.SqrtLog.IdempotentProgram


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Executable arbitrary-degree irreducible search over F₃

Search all monic degree-`d` coefficient vectors and reject each candidate
which is the product of two nonconstant arrays of degree at most `d`.
The test uses explicit convolution. Mathematical finite-field existence
proves that the executable search succeeds for every positive `d`.
-/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearch

open Polynomial

theorem search_ne_none {d : ℕ} (hd : 0 < d) : (search d).1 ≠ none := by
  intro hn
  have hh : (candidates d).find? (fun c => (evaluate c).1) = none := by
    simpa only [search, QuarticSearch.scan_value] using hn
  obtain ⟨c, hc, hp⟩ := exists_passing hd
  have hnop := List.find?_eq_none.mp hh c hc
  exact hnop (by simpa using hp)

end SubexponentialSAT.SqrtLog.IrreducibleSearch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchBootstrapPreparation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! A fixed framed call generates an ordered table from a runtime unary depth.
Only its output and depth ports change; the generator's sentinel is paid for
and cleared before returning. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

open BitProgram StructuredCalls
open Subexp.TupleProgram SubexpOrderedTupleData
open SubexpEnumerationPayload SubexpTupleRefinement

def GeneratorReady (candidate : Bool) (a : Data) : Prop :=
  a.stacks 10 = alphabetWord ∧
  (∀ i : Fin 28, i.val < 6 → a.stacks i = []) ∧
  a.stacks (generatorOut candidate) = []

end SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap


/-! Paid construction of both search tables from a single unary depth word. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

open BitProgram StructuredCalls


abbrev state (depth count candidates factors alphabet fuel : List Bool)
    (regs : Fin 22 → Bool) : Data := ⟨regs, layout depth count candidates factors alphabet fuel⟩

end SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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


/-! CoefficientRun -/

/-! The closed, fixed-program boundary for one arbitrary convolution
coefficient. Its sources and runtime unary address are preserved and all
work stacks are empty again. -/


/-! ProductLift -/

/-! A framed invocation of the source-preserving coefficient kernel. The
extra stack stores the remaining runtime product length. -/


/-! Product -/

/-! A fixed outer loop runs the coefficient kernel at successively longer
unary addresses. Source arrays are preserved; all output coefficients are
physically written in decreasing degree order. -/


/-! ProductRun -/


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

def pairState (as bs cs : List IrreducibleSearch.F) (depth count remaining output : List Bool)
    (regs : Fin 16 → Bool) : State 16 18 :=
  ⟨regs, ![coefficientArray as, coefficientArray bs, count,
    [], [], [], [], [], [], output, [], remaining, [], coefficientArray cs, depth, [], [], []]⟩

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram


/-! Candidate -/


/-! ProductCheck -/


/-! Pair -/

/-! Closed primitive pair test. All three source vectors and the runtime
unary degree are preserved. The return bit is exactly the scalar pairPass. -/

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

def wide (low : State 16 18) (tag present found : Bool)
    (source payload saved count extra : List Bool) : Data :=
  ⟨Fin.addCases (m := 16) (n := 3) (motive := fun _ => Bool)
      low.regs ![tag,present,found],
    Fin.addCases (m := 18) (n := 6) (motive := fun _ => List Bool)
      low.stacks ![source,payload,saved,[],count,extra]⟩

end SubexponentialSAT.SqrtLog.IrreducibleSearchFactorControl

/-! Fixed first-success scan using the concrete saved factor checker. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchCandidateControl

open BitProgram StructuredCalls IrreducibleSearchProgram
open Subexp.BlockSearchPreparation (restrictState lifted_call)
open SubexpEnumerationPayload SubexpTupleRefinement
attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod

def readyLow (cs : List IrreducibleSearch.F) (depth count : List Bool) (d : ℕ)
    (regs : Fin 16 → Bool) (tag present found : Bool) : State 19 24 :=
  IrreducibleSearchFactorControl.wide (pairState [] [] cs depth [] [] [] regs)
    tag present found [] []
    (ProgramEncoding.encodeRecords (IrreducibleSearchFactorControl.factorRecords d)) count []

end SubexponentialSAT.SqrtLog.IrreducibleSearchCandidateControl

end OAI.Algorithms
end


