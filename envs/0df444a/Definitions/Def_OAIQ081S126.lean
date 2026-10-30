-- Prove2me | Definitions.Def_OAIQ081S126
-- name    : OAIQ081S126
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:38:19.148594+00:00
-- url     : https://prove2.me/theorems/379b2769-6722-453e-b771-e1a1cbac1234
-- title:
--   Definitions bundle OAIQ081S126 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 21 declarations of OpenAI's Lean: 7 definitions, 1 inductive type or structure and 13 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local.flatInitial`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local.state`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.StartReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank.unaryCopyCmd`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Cache.unaryCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Count.Prepare.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.Overlay.Code`, `OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterProgram.move`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_HighQueryAdapter`, `SubexponentialSAT_SqrtLog_LeafHighContextProgramBase`, `SubexponentialSAT_SqrtLog_LeafHighContextProgramFlatProject`, `SubexponentialSAT_SqrtLog_LeafOuterProgramStart`, `SubexponentialSAT_SqrtLog_LeafParameterArithmetic`, `SubexponentialSAT_SqrtLog_LeafParameterArithmeticSqrt`, `SubexponentialSAT_SqrtLog_LeafParametersProgramBank`, `SubexponentialSAT_SqrtLog_LeafParametersProgramBankPred`, `SubexponentialSAT_SqrtLog_LeafParametersProgramBankUnary`, `SubexponentialSAT_SqrtLog_LeafParametersProgramBankUnaryCopy`, `SubexponentialSAT_SqrtLog_LeafParametersProgramCache`, `SubexponentialSAT_SqrtLog_LeafParametersProgramNative`, `SubexponentialSAT_SqrtLog_LeafProgramCountPrepare`, `SubexponentialSAT_SubexpCRTOuterControl`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S100`, `OAIQ081S101`, `OAIQ081S102`, `OAIQ081S106`, `OAIQ081S108` and `OAIQ081S109` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S142`, `OAIQ081S143`, `OAIQ081S144` and `OAIQ081S151`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstructionReplay.prepare_avoids`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local.flat_embed` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local.mask_eval`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.setupAfterFrontend_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local.flat_embed` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local.mask_eval`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S100
import Definitions.Def_OAIQ081S101
import Definitions.Def_OAIQ081S102
import Definitions.Def_OAIQ081S106
import Definitions.Def_OAIQ081S108
import Definitions.Def_OAIQ081S109

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHighContextProgramBase
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A paid parser pipeline stages the current physical high assignment. -/
namespace SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.BlockSearchPreparation

def state (regs : Fin 4 → Bool) (counter mask forward output copy acc high work tmp low : List Bool) : Data :=
  ⟨regs,tapes counter mask forward output copy acc high work tmp low⟩


end SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHighContextProgramFlatProject
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def flatInitial (regs : Fin 4 → Bool) (words : List (List Bool)) (mask forward : List Bool) : Data :=
  state regs (ProgramEncoding.encodeRecords words) mask forward []
    (ProgramEncoding.encodeRecords words) [] [] [] [] []


end SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local

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

namespace Overlay
open OAI.Algorithms.SubexponentialSAT.StackRoutines

abbrev Code := Cmd 8 12

end Overlay


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParameterArithmeticSqrt
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual finite square-root calls. Search is bounded by the runtime input
value, which is charged explicitly; arbitrary padding is charged separately. -/
namespace SubexponentialSAT.SqrtLog.LeafParameterArithmetic

open BitProgram StructuredCalls
open CounterPrograms (value)

theorem sqrtLocal_eval (d : SqrtData) (hd : SqrtLocalReady d) :
    ∃ t rf word,
      Eval sqrtLocal t d ⟨rf,Function.update d.stacks 12 word⟩ ∧
      value word = Nat.sqrt (value (d.stacks 2)) ∧
      word.length ≤ value (d.stacks 2) ∧
      t ≤ 200000*(value (d.stacks 2)+(d.stacks 2).length+2)^3 := by
  obtain ⟨r1,hpush⟩ := ArithmeticExpressionSupport.pushWord_eval (1 : Fin 15) [true] d
  let a : SqrtData := ⟨r1,Function.update d.stacks 1 [true]⟩
  have h1 : Eval (ArithmeticExpressionSupport.pushWord 1 [true]) 2 d a := by
    simpa [a,hd 1 (by decide)] using hpush
  have hcopy := ArithmeticCalls.copyAt_eval (2 : Fin 15) 13 11 a
    (by decide) (by decide) (by decide)
    (by simp [a,hd 13 (by decide)]) (by simp [a,hd 11 (by decide)])
  let b := ArithmeticCalls.afterCopy 2 13 a
  have hbs : b.stacks =
      Function.update (Function.update d.stacks 1 [true]) 13 (d.stacks 2) := by
    simp [b,ArithmeticCalls.afterCopy,a]
  have h2 : Eval (ArithmeticCalls.copyAt 2 13 11) (7*(d.stacks 2).length+5) a b := by
    simpa [a] using hcopy
  obtain ⟨ts,e,hs,hv,hl0,hl12,hl13,he14,hframe,hts⟩ := Search.command_eval b
    (by simp [hbs,CounterPrograms.value])
    (by simpa [hbs,Search.root,CounterPrograms.value] using Nat.sqrt_le_self (value (d.stacks 2)))
    (by simp [hbs,hd 0 (by decide)])
    (by simp [hbs,hd 12 (by decide)])
    (by simp [hbs,hd 14 (by decide)])
    (by
      intro i hi
      have h0 : Setup.Search.guardPorts i ≠ (1 : Fin 15) := by
        intro h
        have hv := congrArg Fin.val h
        change i.val = 1 at hv
        omega
      have h2 : Setup.Search.guardPorts i ≠ (2 : Fin 15) := by
        intro h
        have hv := congrArg Fin.val h
        change i.val = 2 at hv
        omega
      have h13 : Setup.Search.guardPorts i ≠ (13 : Fin 15) := by
        intro h
        have hv := congrArg Fin.val h
        change i.val = 13 at hv
        omega
      simp [hbs,h0,h13,hd _ h2])
  simp only [hbs,Function.update_self,
    Function.update_of_ne (by decide : (1 : Fin 15) ≠ 13),
    Function.update_of_ne (by decide : (2 : Fin 15) ≠ 13),
    Function.update_of_ne (by decide : (2 : Fin 15) ≠ 1)] at hv hl0 hl12 hl13 hts
  have he1 : e.stacks 1 = [true] := by
    rw [hframe 1 (by decide) (by decide) (by decide) (by decide)]
    simp [hbs]
  have he2 : e.stacks 2 = d.stacks 2 := by
    rw [hframe 2 (by decide) (by decide) (by decide) (by decide)]
    simp [hbs]
  let B := value (d.stacks 2)+(d.stacks 2).length+1
  have heB : ∀ i, (e.stacks i).length ≤ B := by
    intro i
    by_cases h0 : i=0
    · subst i; dsimp [B]; omega
    by_cases h12 : i=12
    · subst i; dsimp [B]; omega
    by_cases h13 : i=13
    · subst i; dsimp [B]; omega
    by_cases h14 : i=14
    · subst i; simp [he14,B]
    rw [hframe i h0 h12 h13 h14]
    by_cases h1 : i=1
    · subst i; simp [hbs,B]
    by_cases h2 : i=2
    · subst i
      simp [hbs,B]
      omega
    simp [hbs,h1,h13,hd i h2,B]
  obtain ⟨tc,f,hclean,hfs,htc⟩ := Setup.Cleanup.clearMany_eval [0,1,13] e B heB
  have hfinal : f.stacks = Function.update d.stacks 12 (e.stacks 12) := by
    funext i
    rw [hfs]
    by_cases h12 : i=12
    · subst i; simp
    by_cases hclear : i ∈ ([0,1,13] : List (Fin 15))
    · rw [ite_eq_left hclear,Function.update_of_ne h12]
      have hi2 : i ≠ 2 := by intro h; subst i; simp at hclear
      exact (hd i hi2).symm
    · rw [ite_eq_right hclear,Function.update_of_ne h12]
      by_cases h14 : i=14
      · subst i; rw [he14,hd 14 (by decide)]
      have h0 : i ≠ 0 := by intro h; subst i; simp at hclear
      have h1 : i ≠ 1 := by intro h; subst i; simp at hclear
      have h13 : i ≠ 13 := by intro h; subst i; simp at hclear
      rw [hframe i h0 h12 h13 h14]
      simp [hbs,h1,h13]
  have hf : f = (⟨f.regs,Function.update d.stacks 12 (e.stacks 12)⟩ : SqrtData) :=
    CounterForPrograms.data_ext rfl hfinal
  refine ⟨2+((7*(d.stacks 2).length+5)+(ts+tc)),f.regs,e.stacks 12,?_,?_,hl12,?_⟩
  · rw [← hf]
    exact h1.seq (h2.seq (hs.seq hclean))
  · simpa [Search.root,CounterPrograms.value] using hv
  · simp only [Setup.Search.iterationBound,hbs,Function.update_self,
      Function.update_of_ne (by decide : (1 : Fin 15) ≠ 13),
      Function.update_of_ne (by decide : (2 : Fin 15) ≠ 13),
      Function.update_of_ne (by decide : (2 : Fin 15) ≠ 1),List.length_cons,List.length_nil] at hts
    simp only [List.length_cons,List.length_nil] at htc
    let X := value (d.stacks 2)+(d.stacks 2).length+2
    have hx : 1 ≤ X := by dsimp [X]; omega
    have ha : value (d.stacks 2) ≤ X := by dsimp [X]; omega
    have hb : value (d.stacks 2)+1+(d.stacks 2).length+value (d.stacks 2)+2 ≤ 2*X := by
      dsimp [X]; omega
    have hc : value (d.stacks 2)+1 ≤ X := by dsimp [X]; omega
    have he : 16*(d.stacks 2).length+16 ≤ 16*X := by dsimp [X]; omega
    have hsq := Nat.pow_le_pow_left hb 2
    have hmul := Nat.mul_le_mul ha (Nat.mul_le_mul_left 20000 hsq)
    have hmul2 := Nat.mul_le_mul hc he
    have hx2 : X^2 ≤ X^3 := by
      calc
        X^2 = X^2*1 := by simp
        _ ≤ X^2*X := Nat.mul_le_mul_left _ hx
        _ = X^3 := by ring
    change _ ≤ 200000*X^3
    dsimp [B] at htc
    nlinarith

end SubexponentialSAT.SqrtLog.LeafParameterArithmetic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParameterArithmetic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Framed runtime square-root and quotient interfaces for parameter pipelines.
All program syntax is fixed by the port maps, never by the operand values. -/
namespace SubexponentialSAT.SqrtLog.LeafParameterArithmetic


open BitProgram StructuredCalls
open BinaryArithmetic (toNat)

/-- Only the output word changes. The numeric search range and the actual
padded input length are both present in the source-step bound. -/
theorem sqrtAt_eval {S : ℕ} (p : SqrtPorts S) (d : Data S) (hd : SqrtReady p d) :
    ∃ t rf word,
      Eval (sqrtAt p) t d ⟨rf,Function.update d.stacks p.out word⟩ ∧
      BinaryArithmetic.toNat word = Nat.sqrt (BinaryArithmetic.toNat (d.stacks p.input)) ∧
      word.length ≤ BinaryArithmetic.toNat (d.stacks p.input) ∧
      t ≤ 200001*(BinaryArithmetic.toNat (d.stacks p.input)+(d.stacks p.input).length+2)^3 := by
  let a : SqrtData := projectState id (sqrtBlock p) d
  have ha : SqrtLocalReady a := by
    intro i hi
    fin_cases i <;>
      simp_all [a,projectState,sqrtBlock,sqrtStackMap,SqrtReady]
  obtain ⟨t,rf,word,he,hv,hl,ht⟩ := sqrtLocal_eval a ha
  have hcall := ArithmeticExpressionSupport.call_on_block sqrtLocal 2 12 (sqrtBlock p)
    d a ⟨rf,Function.update a.stacks 12 word⟩ word he rfl rfl rfl
  have ha2 : a.stacks 2 = d.stacks p.input := rfl
  refine ⟨t+1,rf,word,?_,?_,?_,?_⟩
  · exact hcall
  · simpa only [ha2,CounterPrograms.value_eq_toNat] using hv
  · simpa only [ha2,CounterPrograms.value_eq_toNat] using hl
  · rw [ha2,CounterPrograms.value_eq_toNat] at ht
    have hpos : 0 < (BinaryArithmetic.toNat (d.stacks p.input)+(d.stacks p.input).length+2)^3 :=
      Nat.pow_pos (by omega)
    nlinarith

end SubexponentialSAT.SqrtLog.LeafParameterArithmetic

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

theorem add_eval (r : Regs) (w : Words) (a b o : Fin 64)
    (hoa : o ≠ a) (hob : o ≠ b) (ho : w o = []) :
    ∃ t rf word,
      Eval (addCmd a b o hoa hob) t (state r w)
        (state rf (Function.update w o word)) ∧
      BinaryArithmetic.toNat word = BinaryArithmetic.toNat (w a) + BinaryArithmetic.toNat (w b) ∧
      word.length ≤ (w a).length + (w b).length + 1 ∧
      t ≤ 100 * ((w a).length + (w b).length + 1) ^ 2 := by
  have hv : ArithmeticCalls.Valid (arithmeticPorts a b o hoa hob) (state r w) := by
    constructor
    · simpa only [arithmeticPorts, state_port] using ho
    · intro i
      have hi : 64 ≤ (work 5 (by decide) i).val := by
        change 64 ≤ 64 + i.val
        omega
      exact state_work r w (work 5 (by decide) i) hi
  obtain ⟨t, rf, word, he, hval, hlen, htime⟩ :=
    ArithmeticCalls.addAt_eval (arithmeticPorts a b o hoa hob) (state r w) hv
  refine ⟨t, rf, word, ?_, ?_, ?_, ?_⟩
  · simpa only [addCmd, arithmeticPorts, state_update] using he
  · simpa only [arithmeticPorts, state_port] using hval
  · simpa only [arithmeticPorts, state_port] using hlen
  · simpa only [arithmeticPorts, state_port] using htime

theorem multiply_eval (r : Regs) (w : Words) (a b o : Fin 64)
    (hoa : o ≠ a) (hob : o ≠ b) (ho : w o = []) :
    ∃ t rf word,
      Eval (multiplyCmd a b o hoa hob) t (state r w)
        (state rf (Function.update w o word)) ∧
      BinaryArithmetic.toNat word = BinaryArithmetic.toNat (w a) * BinaryArithmetic.toNat (w b) ∧
      word.length ≤ (w a).length + (w b).length + 1 ∧
      t ≤ 100 * ((w a).length + (w b).length + 1) ^ 2 := by
  have hv : ArithmeticCalls.Valid (arithmeticPorts a b o hoa hob) (state r w) := by
    constructor
    · simpa only [arithmeticPorts, state_port] using ho
    · intro i
      have hi : 64 ≤ (work 5 (by decide) i).val := by
        change 64 ≤ 64 + i.val
        omega
      exact state_work r w (work 5 (by decide) i) hi
  obtain ⟨t, rf, word, he, hval, hlen, htime⟩ :=
    ArithmeticCalls.multiplyAt_eval (arithmeticPorts a b o hoa hob) (state r w) hv
  refine ⟨t, rf, word, ?_, ?_, ?_, ?_⟩
  · simpa only [multiplyCmd, arithmeticPorts, state_update] using he
  · simpa only [arithmeticPorts, state_port] using hval
  · simpa only [arithmeticPorts, state_port] using hlen
  · simpa only [arithmeticPorts, state_port] using htime

theorem load_eval (r : Regs) (w : Words) (o : Fin 64)
    (word : List Bool) (ho : w o = []) :
    ∃ rf, Eval (loadCmd o word) (2 * word.length) (state r w)
      (state rf (Function.update w o word)) := by
  obtain ⟨rf, he⟩ := ArithmeticExpressionSupport.pushWord_eval (port o) word (state r w)
  refine ⟨rf, ?_⟩
  simpa only [loadCmd, state_port, ho, List.append_nil, state_update] using he


end SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramBankUnary
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank

open BitProgram StructuredCalls BinaryArithmetic

theorem unaryStacks_injective (a : Fin 64) : Function.Injective (unaryStacks a) := by
  have h0 := work_ne_port 2 (by decide) (0 : Fin 2) a
  have h1 := work_ne_port 2 (by decide) (1 : Fin 2) a
  have h01 : work 2 (by decide) (0 : Fin 2) ≠ work 2 (by decide) (1 : Fin 2) := by
    intro h
    exact Fin.zero_ne_one ((work 2 (by decide)).injective h)
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [unaryStacks]

/-- A real three-stack word routine is relocated into the numeric bank. The
four administrative steps reset its Boolean registers and invoke its finite
instruction table; all numeric work remains charged in `cost`. -/
theorem unary_eval (r : Regs) (w : Words) (a : Fin 64) (body : Cmd 3 3)
    (f lengthBound cost : List Bool → ℕ)
    (hspec : ∀ xs, ∃ word t, BinaryArithmetic.toNat word = f xs ∧ word.length ≤ lengthBound xs ∧
      t ≤ cost xs ∧ Eval body t (Setup.io xs) (Setup.io word)) :
    ∃ t rf word, Eval (unaryCmd a body) t (state r w)
        (state rf (Function.update w a word)) ∧
      BinaryArithmetic.toNat word = f (w a) ∧ word.length ≤ lengthBound (w a) ∧ t ≤ cost (w a)+4 := by
  let d := state r w
  let a0 : LogData := projectState smallRegs (unaryStacks a) d
  have hst : a0.stacks = (Setup.io (w a)).stacks := by
    funext i
    fin_cases i
    · simp [a0, projectState, unaryStacks, d, state_port]
    · simpa [a0, projectState, unaryStacks, d, Setup.io,
        StructuredProgram.ioState] using
        (state_work r w (work 2 (by decide) 0) (by rw [work_val]; omega))
    · simpa [a0, projectState, unaryStacks, d, Setup.io,
        StructuredProgram.ioState] using
        (state_work r w (work 2 (by decide) 1) (by rw [work_val]; omega))
  obtain ⟨word,t,hv,hl,ht,he⟩ := hspec (w a)
  have hr : Eval resetLog 3 a0 (Setup.io (w a)) := by
    simpa only [hst] using resetLog_eval a0
  let e := embedState smallRegs (unaryStacks a) d (Setup.io word)
  have hh : Eval (unaryCmd a body) ((3+t)+1) d e :=
    eval_liftCommand_from_state (.seq resetLog body) 0 0 smallRegs (unaryStacks a) d
      (Fin.castAdd_injective 3 5) (unaryStacks_injective a) (hr.seq he)
  have hw : (Setup.io word).stacks = Function.update a0.stacks 0 word := by
    rw [hst]
    funext i; fin_cases i <;> simp []
  have hes : e.stacks = Function.update d.stacks (port a) word := by
    change Function.extend (unaryStacks a) (Setup.io word).stacks d.stacks = _
    rw [hw,ProgramLinking.extend_update (unaryStacks_injective a)]
    have hx : Function.extend (unaryStacks a) a0.stacks d.stacks = d.stacks :=
      congrArg StructuredProgram.State.stacks
        (embedState_project smallRegs (unaryStacks a) d
          (Fin.castAdd_injective 3 5) (unaryStacks_injective a))
    rw [hx]
    rfl
  have heq : e = state e.regs (Function.update w a word) := by
    rw [← state_update r e.regs w a word]
    exact CounterForPrograms.data_ext rfl hes
  refine ⟨(3+t)+1,e.regs,word,?_,hv,hl,by omega⟩
  rw [← heq]
  exact hh

theorem logSucc_eval (r : Regs) (w : Words) (a : Fin 64) :
    ∃ t rf word, Eval (logSuccCmd a) t (state r w)
        (state rf (Function.update w a word)) ∧
      BinaryArithmetic.toNat word = Nat.log2 (BinaryArithmetic.toNat (w a))+1 ∧ word.length ≤ (w a).length+1 ∧
      t ≤ 32*((w a).length+1)^2+4 := by
  apply unary_eval r w a Setup.logSucc
    (fun xs => Nat.log2 (BinaryArithmetic.toNat xs)+1) (fun xs => xs.length+1)
    (fun xs => 32*(xs.length+1)^2)
  intro xs
  simpa only [CounterPrograms.value_eq_toNat] using Setup.logSucc_eval xs

theorem addConst_eval (r : Regs) (w : Words) (a : Fin 64) (k : ℕ) :
    ∃ t rf word, Eval (addConstCmd a k) t (state r w)
        (state rf (Function.update w a word)) ∧
      BinaryArithmetic.toNat word = BinaryArithmetic.toNat (w a)+k ∧ word.length ≤ (w a).length+k ∧
      t ≤ 8*k*((w a).length+k+1)+4 := by
  apply unary_eval r w a (Setup.addConst k)
    (fun xs => BinaryArithmetic.toNat xs+k) (fun xs => xs.length+k)
    (fun xs => 8*k*(xs.length+k+1))
  intro xs
  simpa only [CounterPrograms.value_eq_toNat] using Setup.addConst_eval k xs

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramBankPred
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank

open BitProgram StructuredCalls BinaryArithmetic

theorem pred_eval (r : Regs) (w : Words) (a : Fin 64) :
    ∃ t rf word, Eval (predCmd a) t (state r w)
        (state rf (Function.update w a word)) ∧
      BinaryArithmetic.toNat word = BinaryArithmetic.toNat (w a)-1 ∧ word.length ≤ (w a).length ∧
      t ≤ 20*((w a).length+1) := by
  obtain ⟨t,rf,word,ht,he,hv,hl⟩ := CounterPredProgram.pred_correct (predPorts a) (state r w)
    (state_work r w _ (by change 64 ≤ 64; omega))
  exact ⟨t,rf,word,by simpa only [predCmd,predPorts,state_update] using he,
    by simpa only [predPorts,state_port] using hv,
    by simpa only [predPorts,state_port] using hl,
    by simpa only [predPorts,state_port] using ht⟩

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native runtime leaf parameter production, integer guards, and paid setup.
The former composition modules are import-only compatibility shims. -/


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramBankRoots -/

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank

open BitProgram StructuredCalls BinaryArithmetic

theorem quotient_eval (r : Regs) (w : Words) (a b o : Fin 64)
    (hoa : o ≠ a) (hob : o ≠ b) (ho : w o = []) (hp : 0 < BinaryArithmetic.toNat (w b)) :
    ∃ t rf word, Eval (quotientCmd a b o hoa hob) t (state r w)
        (state rf (Function.update w o word)) ∧
      BinaryArithmetic.toNat word = BinaryArithmetic.toNat (w a) / BinaryArithmetic.toNat (w b) ∧
      word.length = (w a).length ∧
      t  ≤  150*((w a).length+(w b).length+1)^2 := by
  have hv : LeafParameterArithmetic.QuotientReady (quotientPorts a b o hoa hob) (state r w) := by
    constructor
    · simpa only [quotientPorts,state_port] using ho
    · intro i
      exact state_work r w _ (by change 64 ≤ 64 + i.val; omega)
  obtain ⟨t,rf,word,he,hv,hl,ht⟩ := LeafParameterArithmetic.quotientAt_eval
    (quotientPorts a b o hoa hob) (state r w) hv (by simpa [quotientPorts] using hp)
  exact ⟨t,rf,word,by simpa only [quotientCmd,quotientPorts,state_update] using he,
    by simpa only [quotientPorts,state_port] using hv,
    by simpa only [quotientPorts,state_port] using hl,
    by simpa only [quotientPorts,state_port] using ht⟩

theorem sqrt_eval (r : Regs) (w : Words) (a o : Fin 64) (hoa : o ≠ a) (ho : w o = []) :
    ∃ t rf word, Eval (sqrtCmd a o hoa) t (state r w)
        (state rf (Function.update w o word)) ∧
      BinaryArithmetic.toNat word = Nat.sqrt (BinaryArithmetic.toNat (w a)) ∧ word.length  ≤  BinaryArithmetic.toNat (w a) ∧
      t  ≤  200001*(BinaryArithmetic.toNat (w a)+(w a).length+2)^3 := by
  have hv : LeafParameterArithmetic.SqrtReady (sqrtPorts a o hoa) (state r w) := by
    constructor
    · simpa only [sqrtPorts,state_port] using ho
    · intro i
      exact state_work r w _ (by change 64 ≤ 64 + i.val; omega)
  obtain ⟨t,rf,word,he,hv,hl,ht⟩ :=
    LeafParameterArithmetic.sqrtAt_eval (sqrtPorts a o hoa) (state r w) hv
  exact ⟨t,rf,word,by simpa only [sqrtCmd,sqrtPorts,state_update] using he,
    by simpa only [sqrtPorts,state_port] using hv,
    by simpa only [sqrtPorts,state_port] using hl,
    by simpa only [sqrtPorts,state_port] using ht⟩

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramDispatch -/

/-! A fixed ten-comparison bit guard. All operands are runtime binary words.
This module states their data relation separately from parameter production. -/

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit

open BitProgram StructuredCalls BinaryArithmetic Bank

theorem shape_ready (m : Model) (w : Words) (hs : Shape m w) (i : Instr)
    (hi : Admissible m i) : Ready w i := by
  have hz (a : Fin 64) (ha : m.len a = 0) : w a = [] := by
    have hh := hs.2 a
    rw [ha] at hh
    exact List.length_eq_zero_iff.mp (by omega)
  cases i with
  | clear => trivial
  | load o _ => exact hz o hi
  | copy _ o _ => exact hz o hi
  | add _ _ o _ _ => exact hz o hi
  | mul _ _ o _ _ => exact hz o hi
  | pow _ _ o _ _ => exact hz o hi
  | quot _ b o _ _ =>
      exact ⟨hz o hi.1, by rw [hs.1]; exact hi.2⟩
  | sqrt _ o _ => exact hz o hi
  | logSucc => trivial
  | addConst => trivial
  | pred => trivial
  | maxTwo => trivial

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramLayout -/


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafOuterProgramStart
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Closed outer-leaf startup: count the actual clause records, compute the
numeric hash parameters, and preserve the exact binary decoder width. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

structure StartReady (a : Data) (n m B : ℕ) : Prop where
  worker : WorkerEmpty a
  hash : Execution.HashInputs.Ready (projectState
    LeafProgram.HashParameters.ports.hash.register LeafProgram.HashParameters.ports.hash.stack a)
  ambient : BinaryArithmetic.toNat (a.stacks 785)=n
  clauses : BinaryArithmetic.toNat (a.stacks 782)=m
  occurrence : BinaryArithmetic.toNat (a.stacks 786)=B
  count : BinaryArithmetic.toNat (a.stacks 768)=3*m
  depth : BinaryArithmetic.toNat (a.stacks 773)=SparseCode.distanceDenom m B
  rounds : BinaryArithmetic.toNat (a.stacks 774)=HashSelect.loopCap n m
  width : a.stacks 783=a.stacks 768

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

abbrev unaryCopyCmd (a o : Fin 64) : Cmd 8 77 :=
  liftCommand (Serialization.unaryCopy 0 1) 0 1 unaryRegs (unaryPorts a o)

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramCache
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Cache


open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev unaryCommand : Cmd 8 77 :=
  .seq (Bank.unaryCopyCmd 29 51)
    (.seq (Bank.unaryCopyCmd 46 52) (Bank.unaryCopyCmd 50 53))

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Cache

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

local infixr:55 " ;; " => seq

def move (src dst : Fin 320) : Code := transfer src 319 ;; transfer 319 dst

end SubexponentialSAT.SubexpCRTOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramCountPrepare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual reclamation of node-work scratch before Hermite reconstruction.
The static port set includes both the native CRT work ports and the scalar/
polynomial arithmetic readiness ports, together with the reader temporaries. Runtime data are cleared by real
stack loops; persistent node and jet inputs remain outside this set. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Count.Prepare

open SubexponentialSAT BitProgram StructuredCalls

abbrev command : Cmd 40 768 :=
  .seq (.call (StackRoutines.clearProgram 699 0 1))
    (BankRoutines.clearCmd 699 0 1 ports)

end SubexponentialSAT.SqrtLog.LeafProgram.Count.Prepare

end OAI.Algorithms
end


