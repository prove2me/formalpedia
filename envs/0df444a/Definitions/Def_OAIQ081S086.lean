-- Prove2me | Definitions.Def_OAIQ081S086
-- name    : OAIQ081S086
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:07:41.886209+00:00
-- url     : https://prove2.me/theorems/bb3ec8ac-6997-48a1-9500-28379b98d76f
-- title:
--   Definitions bundle OAIQ081S086 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 46 declarations of OpenAI's Lean: 30 definitions and 16 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar.decrementPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.clearAt`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.clearPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.clearPortsCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.clearResult`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.clearedPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.cloneInitial`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.copiedSourcesCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.copiesOfLiteral`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.copySources`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.dispatchEntry`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.entryCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.entryCopy`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.initialBits`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.literalAt`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.literalResult`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.metadataCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.preparationCleanup`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.prepareEntry`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.pushLiteral`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.pushedLiteral`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.selector`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.unaryFromBinary`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.unaryFromWork`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.callService`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.cleared`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.newtonPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.storedResult`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.coefficientValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.chain`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramArrays`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramCleanup`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramEntry`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramEntryRun`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramInput`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramMetadata`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramRepeat`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarConstants`, `SubexponentialSAT_SqrtLog_IdempotentProgramMachine`, `SubexponentialSAT_SqrtLog_IdempotentProgramRegisters`, `SubexponentialSAT_SqrtLog_IdempotentProgramService`, `SubexponentialSAT_SqrtLog_IrreducibleSearchProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S066`, `OAIQ081S067`, `OAIQ081S069` and `OAIQ081S070` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S103`, `OAIQ081S104` and `OAIQ081S105`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S066
import Definitions.Def_OAIQ081S067
import Definitions.Def_OAIQ081S069
import Definitions.Def_OAIQ081S070

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


def chain (commands : List Code) : Code :=
  SparseCountProgram.Controller.firstHit 23 commands

end Selector

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramRepeat
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native runtime-sized cell repetition for idempotent preparation. The
source cell and unary count are data; the finite control is independent of
both lengths. Every source bit copied into the destination is charged. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

open BitProgram StructuredCalls SubexpScanPrimitives

theorem repeatAt_eval (d : Data) (source target scratch count : Fin 41)
    (distinct : Function.Injective (repeatPorts source target scratch count))
    (n : ℕ) (hc : d.stacks count = List.replicate n true)
    (hs : d.stacks scratch = []) :
    Eval (repeatAt source target scratch count)
      (n * (7 * (d.stacks source).length + 7) + 6) d
      (repeated d target count n (d.stacks source)) := by
  let a := resetData d
  let ports := repeatPorts source target scratch count
  have hst : source ≠ target := distinct.ne (by decide : (0 : Fin 4) ≠ 1)
  have hsc : source ≠ count := distinct.ne (by decide : (0 : Fin 4) ≠ 3)
  have htc : target ≠ count := distinct.ne (by decide : (1 : Fin 4) ≠ 3)
  have hts : scratch ≠ target := distinct.ne (by decide : (2 : Fin 4) ≠ 1)
  have hcs : scratch ≠ count := distinct.ne (by decide : (2 : Fin 4) ≠ 3)
  have hi : embedState repeatRegisters ports a
      (Subexp.BlockCopyProgram.initialState n (d.stacks source) (d.stacks target)) = a := by
    apply embedState_eq _ _ repeatRegisters_injective distinct
    · intro i
      fin_cases i <;> simp [a, resetData, repeatRegisters,
        Subexp.BlockCopyProgram.initialState, Subexp.BlockCopyProgram.data]
    · intro i
      fin_cases i <;> simp [a, resetData, repeatPorts,
        Subexp.BlockCopyProgram.initialState, Subexp.BlockCopyProgram.data, hc, hs]
    · intros; rfl
    · intros; rfl
  have ho : embedState repeatRegisters ports a
      (Subexp.BlockCopyProgram.data false false (d.stacks source)
        (Subexp.BlockCopyProgram.copies n (d.stacks source) ++ d.stacks target) []) =
      repeated d target count n (d.stacks source) := by
    apply embedState_eq _ _ repeatRegisters_injective distinct
    · intro i
      fin_cases i <;> simp [repeated, resetData, repeatRegisters,
        Subexp.BlockCopyProgram.data]
    · intro i
      fin_cases i <;> simp [repeated, repeatPorts,
        Subexp.BlockCopyProgram.data, hst, hsc, htc.symm, hts, hcs, hs]
    · intro i hi
      exact rfl
    · intro i hi
      have hit : i ≠ target := fun h => hi ⟨1, by simpa [ports, repeatPorts] using h.symm⟩
      have hic : i ≠ count := fun h => hi ⟨3, by simpa [ports, repeatPorts] using h.symm⟩
      simp [repeated, a, resetData, hit, hic]
  have he := eval_call_lifted Subexp.BlockCopyProgram.program repeatRegisters ports a
    repeatRegisters_injective distinct
    (Subexp.BlockCopyProgram.program_trace n (d.stacks source) (d.stacks target))
  rw [hi, ho] at he
  convert (resetThree_eval d).seq he using 1 ; try rfl
  omega

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramMetadata
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Literal cells, unary metadata and concrete zero-array allocation. Literal
lengths are fixed program syntax; all t-dependent repetitions use a runtime
unary counter and charge each bit copy. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

open BitProgram StructuredCalls SubexpScanPrimitives

abbrev pushLiteral (target : Fin 41) (bit : Bool) : Cmd 8 41 :=
  .base (.seq (.atom (.set 0 bit)) (.atom (.push target 0)))

def pushedLiteral (d : Data) (target : Fin 41) (bit : Bool) : Data :=
  ⟨Function.update d.regs 0 bit, Function.update d.stacks target (bit :: d.stacks target)⟩

theorem pushLiteral_eval (d : Data) (target : Fin 41) (bit : Bool) :
    Eval (pushLiteral target bit) 2 d (pushedLiteral d target bit) := by
  exact .base ((StructuredProgram.Eval.atom (.set 0 bit) d).seq
    (StructuredProgram.Eval.atom (.push target 0) _))

def literalAt (target : Fin 41) : List Bool → Cmd 8 41
  | [] => .base .skip
  | b :: bs => .seq (literalAt target bs) (pushLiteral target b)

def literalResult (d : Data) (target : Fin 41) : List Bool → Data
  | [] => d
  | b :: bs => pushedLiteral (literalResult d target bs) target b

theorem literalAt_eval (d : Data) (target : Fin 41) (bits : List Bool) :
    Eval (literalAt target bits) (2*bits.length) d (literalResult d target bits) := by
  induction bits with
  | nil => exact .base (.skip _)
  | cons b bs ih =>
      convert ih.seq (pushLiteral_eval (literalResult d target bs) target b) using 1 <;>
        simp [literalAt, literalResult]
      all_goals omega

theorem literalResult_stacks (d : Data) (target : Fin 41) (bits : List Bool) :
    (literalResult d target bits).stacks =
      Function.update d.stacks target (bits ++ d.stacks target) := by
  induction bits with
  | nil => simp [literalResult]
  | cons b bs ih => simp [literalResult, pushedLiteral, ih, Function.update_idem]

abbrev clearAt (target : Fin 41) : Cmd 8 41 :=
  .call (StackRoutines.clearProgram target 0 1)

def clearResult (d : Data) (target : Fin 41) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks target []⟩

theorem clearAt_eval (d : Data) (target : Fin 41) :
    Eval (clearAt target) (2*(d.stacks target).length+3) d (clearResult d target) :=
  .call _ (ListRegisterProgram.clear_run target 0 1 d.regs d.stacks)

/-- Port 29 caches unary t; 0,1,2 are private scratch. The output port is a
fixed parameter of this finite program, not an input-dependent address. -/
abbrev copiesOfLiteral (target : Fin 41) (bits : List Bool) : Cmd 8 41 :=
  .seq (literalAt 0 bits) <|
  .seq (.call (StackRoutines.copyProgram 29 1 2 (0 : Fin 8) 1)) <|
  .seq (repeatAt 0 target 2 1) (clearAt 0)

theorem copiesOfLiteral_eval (d : Data) (target : Fin 41) (bits : List Bool)
    (n : ℕ) (hn : d.stacks 29 = List.replicate n true)
    (h0 : d.stacks 0 = []) (h1 : d.stacks 1 = []) (h2 : d.stacks 2 = [])
    (ht0 : target ≠ 0) (ht1 : target ≠ 1) (ht2 : target ≠ 2) :
    ∃ rf, Eval (copiesOfLiteral target bits)
      (n*(7*bits.length+14)+4*bits.length+14) d
      ⟨rf, Function.update d.stacks target
        (Subexp.BlockCopyProgram.copies n bits ++ d.stacks target)⟩ := by
  let a := literalResult d 0 bits
  let b := afterCopy a 29 1 0 1
  let c := repeated b target 1 n bits
  have has : a.stacks = Function.update d.stacks 0 bits := by
    simp [a, literalResult_stacks, h0]
  have hbs : b.stacks = Function.update (Function.update d.stacks 0 bits) 1
      (List.replicate n true) := by
    simp [b, afterCopy, StackRoutines.copyStacks, has, hn, h1]
  have hcopy := copy_eval a 29 1 2 0 1 (by decide) (by decide) (by decide)
    (by decide) (by simp [has, h2])
  have hrep := repeatAt_eval b 0 target 2 1 (by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [repeatPorts, Ne.symm ht0, Ne.symm ht1, Ne.symm ht2])
    n (by simp [hbs]) (by simp [hbs, h2])
  have hrep' : Eval (repeatAt 0 target 2 1) (n*(7*bits.length+7)+6) b c := by
    simpa [hbs, c] using hrep
  have hclear := clearAt_eval c 0
  have hcs : c.stacks = Function.update (Function.update (Function.update d.stacks 0 bits) 1 [])
      target (Subexp.BlockCopyProgram.copies n bits ++ d.stacks target) := by
    simp [c, repeated, hbs, ht0, ht1, Function.update_idem]
  have hout : (clearResult c 0).stacks = Function.update d.stacks target
      (Subexp.BlockCopyProgram.copies n bits ++ d.stacks target) := by
    rw [clearResult, hcs]
    funext i
    by_cases hi0 : i = 0
    · subst i; simp [Ne.symm ht0, h0]
    · by_cases hi1 : i = 1
      · subst i; simp [Ne.symm ht1, h1]
      · by_cases hit : i = target
        · subst i; simp [ht0]
        · simp [hi0,hi1,hit]
  refine ⟨(clearResult c 0).regs, ?_⟩
  have he := (literalAt_eval d 0 bits).seq (hcopy.seq (hrep'.seq hclear))
  have hh : clearResult c 0 =
      ⟨(clearResult c 0).regs, Function.update d.stacks target
        (Subexp.BlockCopyProgram.copies n bits ++ d.stacks target)⟩ := state_ext rfl hout
  rw [hh] at he
  convert he using 1 ; simp [ has, hn, hcs, Ne.symm ht0] ; ring

abbrev metadataCommand : Cmd 8 41 :=
  .seq (copiesOfLiteral 12 [true,true]) (copiesOfLiteral 37 [true,true,true])

theorem metadataCommand_eval (d : Data) (t : ℕ)
    (ht : d.stacks 29 = List.replicate t true)
    (h0 : d.stacks 0 = []) (h1 : d.stacks 1 = []) (h2 : d.stacks 2 = [])
    (h12 : d.stacks 12 = []) (h37 : d.stacks 37 = []) :
    ∃ rf, Eval metadataCommand (63*t+48) d
      ⟨rf, Function.update (Function.update d.stacks 12 (List.replicate (2*t) true))
        37 (List.replicate (3*t) true)⟩ := by
  obtain ⟨rf,ha⟩ := copiesOfLiteral_eval d 12 [true,true] t ht h0 h1 h2
    (by decide) (by decide) (by decide)
  let a : Data := ⟨rf, Function.update d.stacks 12 (List.replicate (2*t) true)⟩
  have ha' : Eval (copiesOfLiteral 12 [true,true]) (28*t+22) d a := by
    have hbits : Subexp.BlockCopyProgram.copies t [true,true] = List.replicate (2*t) true := by
      convert copies_replicate t 2 true using 1 <;> simp [Nat.mul_comm]
    simpa [a, hbits, h12, Nat.mul_comm] using ha
  obtain ⟨sf,hb⟩ := copiesOfLiteral_eval a 37 [true,true,true] t
    (by simp [a,ht]) (by simp [a,h0]) (by simp [a,h1]) (by simp [a,h2])
    (by decide) (by decide) (by decide)
  have hbits : Subexp.BlockCopyProgram.copies t [true,true,true] = List.replicate (3*t) true := by
    convert copies_replicate t 3 true using 1 <;> simp [Nat.mul_comm]
  refine ⟨sf, ?_⟩
  have he := ha'.seq hb
  convert he using 1 <;> simp [ a, hbits, h37] ; ring

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms
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

def copySources (target : Fin 41) : List (Fin 41) → Cmd 8 41
  | [] => .base .skip
  | source :: rest => .seq
      (.call (StackRoutines.copyProgram source target 2 (0 : Fin 8) 1))
      (copySources target rest)

def copiedSourcesCost (target : Fin 41) : List (Fin 41) → Data → ℕ
  | [], _ => 0
  | source :: rest, d => 7*(d.stacks source).length+5+
      copiedSourcesCost target rest (afterCopy d source target 0 1)

theorem copySources_eval (target : Fin 41) (sources : List (Fin 41)) (d : Data)
    (ht : (2 : Fin 41) ≠ target) (hs : d.stacks 2 = [])
    (hd : ∀ source ∈ sources, source ≠ target ∧ source ≠ 2) :
    Eval (copySources target sources) (copiedSourcesCost target sources d) d
      (copiedSources target sources d) := by
  induction sources generalizing d with
  | nil => exact .base (.skip _)
  | cons source rest ih =>
      have hsource := hd source (by simp)
      have hc := copy_eval d source target 2 0 1 hsource.1 hsource.2 ht (by decide) hs
      have hr := ih (afterCopy d source target 0 1)
        (by simp [afterCopy,StackRoutines.copyStacks,ht,hs])
        (by intro i hi; exact hd i (by simp [hi]))
      exact hc.seq hr

abbrev cloneInitial : Cmd 8 41 :=
  .seq (.call (StackRoutines.copyProgram 32 33 2 (0 : Fin 8) 1)) <|
  .seq (.call (StackRoutines.copyProgram 32 34 2 (0 : Fin 8) 1))
    (.call (StackRoutines.copyProgram 32 35 2 (0 : Fin 8) 1))

def initialBits (d : Data) (n : ℕ) : List Bool :=
  d.stacks 30 ++ d.stacks 31 ++ d.stacks 27 ++
    Subexp.BlockCopyProgram.copies n (d.stacks 17)

theorem cloneInitial_eval (d : Data) (h2 : d.stacks 2 = [])
    (h33 : d.stacks 33 = []) (h34 : d.stacks 34 = []) (h35 : d.stacks 35 = []) :
    ∃ rf, Eval cloneInitial (21*(d.stacks 32).length+15) d
      ⟨rf,Function.update (Function.update (Function.update d.stacks
        33 (d.stacks 32)) 34 (d.stacks 32)) 35 (d.stacks 32)⟩ := by
  let a := afterCopy d 32 33 0 1
  let b := afterCopy a 32 34 0 1
  have ha := copy_eval d 32 33 2 0 1 (by decide) (by decide) (by decide) (by decide) h2
  have hb := copy_eval a 32 34 2 0 1 (by decide) (by decide) (by decide) (by decide)
    (by simp [a,afterCopy,StackRoutines.copyStacks,h2])
  have hc := copy_eval b 32 35 2 0 1 (by decide) (by decide) (by decide) (by decide)
    (by simp [b,a,afterCopy,StackRoutines.copyStacks,h2])
  have he := ha.seq (hb.seq hc)
  refine ⟨(afterCopy b 32 35 0 1).regs,?_⟩
  convert he using 1 <;>
    simp [b,a,afterCopy,StackRoutines.copyStacks,h33,h34,h35] ; ring

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

def clearPorts : List (Fin 41) → Cmd 8 41
  | [] => .base .skip
  | p::ps => .seq (clearAt p) (clearPorts ps)

def clearedPorts : List (Fin 41) → Data → Data
  | [],d => d
  | p::ps,d => clearedPorts ps (clearResult d p)

def clearPortsCost : List (Fin 41) → Data → ℕ
  | [],_ => 0
  | p::ps,d => 2*(d.stacks p).length+3+clearPortsCost ps (clearResult d p)

theorem clearPorts_eval (ps : List (Fin 41)) (d : Data) :
    Eval (clearPorts ps) (clearPortsCost ps d) d (clearedPorts ps d) := by
  induction ps generalizing d with
  | nil => exact .base (.skip _)
  | cons p ps ih => exact (clearAt_eval d p).seq (ih _)

theorem clearedPorts_stacks (ps : List (Fin 41)) (d : Data) (i : Fin 41) :
    (clearedPorts ps d).stacks i = if i ∈ ps then [] else d.stacks i := by
  induction ps generalizing d with
  | nil => simp [clearedPorts]
  | cons p ps ih =>
      simp only [clearedPorts,ih,List.mem_cons,clearResult]
      by_cases hi : i=p
      · subst i
        simp
      · by_cases hm : i∈ps <;> simp [hi,hm]

theorem clearPortsCost_bound (ps : List (Fin 41)) (d : Data) (W : ℕ)
    (hw : ∀ p ∈ ps, (d.stacks p).length ≤ W) :
    clearPortsCost ps d ≤ ps.length*(2*W+3) := by
  induction ps generalizing d with
  | nil => simp [clearPortsCost]
  | cons p ps ih =>
      have hp := hw p (by simp)
      have ht : ∀ q ∈ ps, ((clearResult d p).stacks q).length ≤ W := by
        intro q hq
        by_cases h : q=p
        · simp [clearResult,h]
        · simpa [clearResult,h] using hw q (by simp [hq])
      have hh := ih (clearResult d p) ht
      simp only [clearPortsCost,List.length_cons]
      nlinarith

abbrev preparationCleanup : Cmd 8 41 := clearPorts preparationDiscard

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramEntry
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

abbrev entryCopy (source : Fin 41) : Cmd 8 41 :=
  .call (StackRoutines.copyProgram source 22 4 (0 : Fin 8) 1)

abbrev dispatchEntry : Cmd 8 41 :=
  .ite 7 (.ite 5 (entryCopy 23) (entryCopy 21))
    (.ite 6 (.ite 5 (entryCopy 19) (entryCopy 20))
      (.ite 5 (entryCopy 18) (entryCopy 17)))

theorem dispatchEntry_eval (d : Data) (c : Fin 6) (h4 : d.stacks 4 = [])
    (hcode : ∀ z, d.regs (outputPort z) = codeBits c z) :
    ∃ n rf, n ≤ 7*(d.stacks (entrySource c)).length+8 ∧
      Eval dispatchEntry n d ⟨rf,Function.update d.stacks 22
        (d.stacks (entrySource c) ++ d.stacks 22)⟩ := by
  have hcopy := copy_eval d (entrySource c) 22 4 0 1
    (by fin_cases c <;> decide) (by fin_cases c <;> decide)
    (by decide) (by decide) h4
  have h0 := hcode 0
  have h1 := hcode 1
  have h2 := hcode 2
  fin_cases c <;> norm_num [outputPort,codeBits] at h0 h1 h2 <;>
    simp only [entrySource] at hcopy ⊢
  all_goals first
    | refine ⟨_,_,?_,Eval.ite_false (test := 7) h2 (Eval.ite_false (test := 6) h1 (Eval.ite_false (test := 5) h0 hcopy))⟩
    | refine ⟨_,_,?_,Eval.ite_false (test := 7) h2 (Eval.ite_false (test := 6) h1 (Eval.ite_true (test := 5) h0 hcopy))⟩
    | refine ⟨_,_,?_,Eval.ite_false (test := 7) h2 (Eval.ite_true (test := 6) h1 (Eval.ite_false (test := 5) h0 hcopy))⟩
    | refine ⟨_,_,?_,Eval.ite_false (test := 7) h2 (Eval.ite_true (test := 6) h1 (Eval.ite_true (test := 5) h0 hcopy))⟩
    | refine ⟨_,_,?_,Eval.ite_true (test := 7) h2 (Eval.ite_false (test := 5) h0 hcopy)⟩
    | refine ⟨_,_,?_,Eval.ite_true (test := 7) h2 (Eval.ite_true (test := 5) h0 hcopy)⟩
  all_goals omega

abbrev selector : Cmd 8 41 :=
  .call (ProgramLinking.liftProgram IdempotentTableEntryProgram.program id selectorPorts)

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

abbrev prepareEntry : Cmd 8 41 :=
  .seq (.call (StackRoutines.copyProgram 25 0 4 (0 : Fin 8) 1)) <|
  .seq (.call (StackRoutines.copyProgram 26 1 4 (0 : Fin 8) 1))
    (.call (StackRoutines.copyProgram 24 2 4 (0 : Fin 8) 1))

abbrev entryCommand : Cmd 8 41 :=
  .seq prepareEntry (.seq selector (.seq dispatchEntry (.seq (clearAt 2) (clearAt 3))))

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

abbrev unaryFromWork : Cmd 8 41 :=
  .call (ProgramLinking.liftProgram CounterConversions.unaryProgram repeatRegisters unaryPorts)

theorem unaryFromWork_eval (d : Data) (h29 : d.stacks 29 = []) (h30 : d.stacks 30 = []) :
    ∃ n rf, n ≤ CounterConversions.runtimeBound (d.stacks 28) ∧
      Eval unaryFromWork n d
        ⟨rf, Function.update (Function.update d.stacks 28 []) 29
          (List.replicate (CounterPrograms.value (d.stacks 28)) true)⟩ := by
  let small := CounterConversions.state (fun i => d.regs (repeatRegisters i)) (d.stacks 28) []
  obtain ⟨n,hn,hr⟩ := CounterConversions.unary_runs
    (fun i => d.regs (repeatRegisters i)) (d.stacks 28) []
  simp only [List.append_nil] at hr
  let out := CounterConversions.state CounterConversions.zeroRegs []
    (List.replicate (CounterPrograms.value (d.stacks 28)) true)
  have hi : embedState repeatRegisters unaryPorts d small = d := by
    apply embedState_eq _ _ repeatRegisters_injective unaryPorts_injective
    · intro i; rfl
    · intro i
      fin_cases i <;> simp [small,unaryPorts,CounterConversions.state,h29,h30]
    · intros; rfl
    · intros; rfl
  have he := eval_call_lifted CounterConversions.unaryProgram repeatRegisters unaryPorts d
    repeatRegisters_injective unaryPorts_injective hr
  have ho : (embedState repeatRegisters unaryPorts d out).stacks =
      Function.update (Function.update d.stacks 28 []) 29
        (List.replicate (CounterPrograms.value (d.stacks 28)) true) := by
    funext j
    by_cases hj : ∃ i, unaryPorts i = j
    · obtain ⟨i,rfl⟩ := hj
      rw [embedState_stack _ _ _ _ unaryPorts_injective]
      fin_cases i <;> simp [out,unaryPorts,CounterConversions.state,h30]
    · rw [embedState_stack_frame _ _ _ _ j hj]
      have h28 : j ≠ 28 := fun h => hj ⟨0,by simpa [unaryPorts] using h.symm⟩
      have h29' : j ≠ 29 := fun h => hj ⟨1,by simpa [unaryPorts] using h.symm⟩
      simp [h28,h29']
  have hout : embedState repeatRegisters unaryPorts d out =
      ⟨(embedState repeatRegisters unaryPorts d out).regs,
        Function.update (Function.update d.stacks 28 []) 29
          (List.replicate (CounterPrograms.value (d.stacks 28)) true)⟩ := state_ext rfl ho
  refine ⟨n,(embedState repeatRegisters unaryPorts d out).regs,hn,?_⟩
  change Eval unaryFromWork n (embedState repeatRegisters unaryPorts d small)
    (embedState repeatRegisters unaryPorts d out) at he
  rw [hi,hout] at he
  exact he

abbrev unaryFromBinary : Cmd 8 41 :=
  .seq (.call (StackRoutines.copyProgram 31 28 30 (0 : Fin 8) 1)) unaryFromWork

theorem unaryFromBinary_eval (d : Data)
    (h28 : d.stacks 28 = []) (h29 : d.stacks 29 = []) (h30 : d.stacks 30 = []) :
    ∃ n rf, n ≤ 7*(d.stacks 31).length+5+CounterConversions.runtimeBound (d.stacks 31) ∧
      Eval unaryFromBinary n d
        ⟨rf,Function.update d.stacks 29
          (List.replicate (CounterPrograms.value (d.stacks 31)) true)⟩ := by
  let a := afterCopy d 31 28 0 1
  have hc := copy_eval d 31 28 30 0 1 (by decide) (by decide) (by decide) (by decide) h30
  obtain ⟨n,rf,hn,hu⟩ := unaryFromWork_eval a
    (by simp [a,afterCopy,StackRoutines.copyStacks,h29])
    (by simp [a,afterCopy,StackRoutines.copyStacks,h30])
  have ha28 : a.stacks 28 = d.stacks 31 := by simp [a,afterCopy,StackRoutines.copyStacks,h28]
  have hs : Function.update (Function.update a.stacks 28 []) 29
      (List.replicate (CounterPrograms.value (a.stacks 28)) true) =
      Function.update d.stacks 29 (List.replicate (CounterPrograms.value (d.stacks 31)) true) := by
    rw [ha28]
    simp [a,afterCopy,StackRoutines.copyStacks,Function.update_idem,←h28]
  refine ⟨7*(d.stacks 31).length+5+n,rf,?_,?_⟩
  · simpa only [ha28] using Nat.add_le_add_left hn (7*(d.stacks 31).length+5)
  · rw [hs] at hu
    exact hc.seq hu

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

def cleared (d : RegisterData) (target : Fin 41) : RegisterData :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks target []⟩

def storedResult (d : RegisterData) (target : Fin 41) : RegisterData :=
  cleared (ArithmeticCalls.afterCopy 0 target (cleared d target)) 0

theorem storedResult_stacks (d : RegisterData) (target : Fin 41)
    (ht : target ≠ 0) :
    (storedResult d target).stacks =
      Function.update (Function.update d.stacks target (d.stacks 0)) 0 [] := by
  simp [storedResult, cleared, ArithmeticCalls.afterCopy, ht.symm,
    Function.update_idem]

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarConstants
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

open BitProgram StructuredCalls ModularRingPrograms ModularDivisionPrograms
open SubexpLiftRing SubexpQuarticRing BinaryArithmetic ModularArithmetic

def decrementPorts : CounterForPrograms.Ports 8 41 where
  register := ⟨Fin.castAdd 5, by intro i j h; exact Fin.ext (congrArg (fun x : Fin 8 => x.val) h)⟩
  counter := 0
  scratch := 2
  counter_ne_scratch := by decide

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramService
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Lift the common 32-stack arithmetic ABI into the Newton machine and prove
that the source-preserving register wrapper has the exact specified effect. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open BitProgram StructuredCalls

abbrev callService (command : Cmd 8 32) : Cmd 8 41 :=
  .call (ProgramLinking.liftProgram (compiled command 8 0) id servicePorts)

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

def newtonPorts : CounterForPrograms.Ports 8 41 where
  register := ⟨Fin.castAdd 5, by intro i j h; exact Fin.ext (congrArg (fun x : Fin 8 => x.val) h)⟩
  counter := 39
  scratch := 40
  counter_ne_scratch := by decide

end SubexponentialSAT.SqrtLog.IdempotentProgram

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

def coefficientValue (as bs : List IrreducibleSearch.F) (n : ℕ) : IrreducibleSearch.F :=
  (List.zipWith (· * ·) (paddedPrefix n as) (paddedPrefix n bs).reverse).sum

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram


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


/-! Candidate -/


/-! ProductCheck -/


/-! Pair -/

/-! Closed primitive pair test. All three source vectors and the runtime
unary degree are preserved. The return bit is exactly the scalar pairPass. -/

end OAI.Algorithms
end


