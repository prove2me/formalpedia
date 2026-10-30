-- Prove2me | Definitions.Def_OAIQ081S103
-- name    : OAIQ081S103
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:21:02.59376+00:00
-- url     : https://prove2.me/theorems/c9ed37a2-7849-466c-a611-dd5d073db8fa
-- title:
--   Definitions bundle OAIQ081S103 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 39 declarations of OpenAI's Lean: 20 definitions and 19 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.descendingTape`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.scalarVector`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.tripleTape`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.triplesTape`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.ModulusWorkspaceEmpty`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar.Canonical`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar.Values`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar.baseValues`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar.decode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar.literal`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar.minusValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar.negativeOne`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar.normalize`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar.oneValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar.zeroValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.arrayStage`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.initialArray`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.tableTape`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.tableWords`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Normalize.Data`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_IdempotentApplyProgramScalar`, `SubexponentialSAT_SqrtLog_IdempotentApplyProgramTape`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramArrayStage`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramArrays`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramModulus`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarBase`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarConstants`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarCore`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarInit`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarMachine`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarOutput`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarSemantics`, `SubexponentialSAT_SqrtLog_IdempotentProgramCanonical`, `SubexponentialSAT_SqrtLog_IdempotentProgramRegisters`, `SubexponentialSAT_SqrtLog_IdempotentProgramWords`, `SubexponentialSAT_SqrtLog_MomentsProgramNormalize`, `SubexponentialSAT_SqrtLog_RingProgramSerialization`, `SubexponentialSAT_SubexpBlockParameterProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S082`, `OAIQ081S083`, `OAIQ081S085` and `OAIQ081S086` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S119`, `OAIQ081S120`, `OAIQ081S121`, `OAIQ081S128` and `OAIQ081S130`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S082
import Definitions.Def_OAIQ081S083
import Definitions.Def_OAIQ081S085
import Definitions.Def_OAIQ081S086

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

/-- The first array stores `(2u,-3u,u,0,...)`; the three cache source words
are prepended in reverse order to the freshly allocated zero suffix. -/
abbrev initialArray : Cmd 8 41 :=
  .seq (paddedZeros 32 3) (copySources 32 [27,31,30])

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramSerialization
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgram

open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing SubexponentialSAT.BinaryArithmetic

variable (p t : ℕ) [Fact p.Prime]

theorem wordMul_canonical (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus p t)
    (x y : ScalarCode p t) :
    BinaryArithmetic.toNat (SubexponentialSAT.SubexpPreparedQuartic.wordMul p t M x y).1.val < p^t := by
  change BinaryArithmetic.toNat (mulBaseRun _ _ _ _).1 < _
  rw [mulBaseRun_value _ _ _ _ (by
    rw [M.value]; exact pow_pos (Fact.out : p.Prime).pos t) (by
    rw [M.value]; exact modulus_le_width p t), M.value]
  exact Nat.mod_lt _ (pow_pos (Fact.out : p.Prime).pos t)

end SubexponentialSAT.SqrtLog.RingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramScalar
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native injection of a base coefficient into the first coordinate of an
extension-ring coefficient. The remaining coordinates are physically copied
from the canonical zero word. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram

open scoped BigOperators
open BitProgram StructuredCalls SubexpQuarticRing SubexpScanPrimitives
open IdempotentPreparationProgram

abbrev scalarVector {B d : ℕ} (zero scalar : Word B) : RingProgram.Code (Word B) d :=
  fun i => if i.val=0 then scalar else zero

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramTape
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Byte order for descending Horner application. A single whole-tape reversal
puts the last digit first and each digit's coefficients in c,b,a order. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram

open SubexpQuarticRing

def tripleTape {B : ℕ} (v : Triple (Word B)) : List Bool :=
  v.a.val ++ v.b.val ++ v.c.val

def triplesTape {B : ℕ} (vs : List (Triple (Word B))) : List Bool :=
  (vs.map tripleTape).flatten

def descendingTape {B : ℕ} (vs : List (Triple (Word B))) : List Bool :=
  (vs.map fun v => v.c.val.reverse ++ v.b.val.reverse ++ v.a.val.reverse).flatten

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram

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

abbrev arrayStage : Cmd 8 41 := .seq initialArray (.seq cloneInitial negativeOneArray)

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

theorem state_work (r : Regs) (w : Words) (i : Fin 22) (hi : 15 ≤ i.val) :
    (state r w).stacks i = [] := by simp [state, show ¬ i.val < 15 by omega]

end SubexponentialSAT.SubexpBlockParameterProgram

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

def ModulusWorkspaceEmpty (d : Data) : Prop :=
  ∀ i : Fin 22, i ≠ 1 → d.stacks (modulusPorts i) = []

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

theorem registerClear_eval (d : RegisterData) (target : Fin 41) :
    Eval (registerClear target) (2*(d.stacks target).length+3) d (cleared d target) :=
  .call _ (ListRegisterProgram.clear_run target 0 1 d.regs d.stacks)

theorem storeResult_eval (d : RegisterData) (target : Fin 41)
    (ht : target ≠ 0) (h38 : target ≠ 38) (hs : d.stacks 38 = []) :
    Eval (storeResult target)
      (2*(d.stacks target).length + 9*(d.stacks 0).length + 11)
      d (storedResult d target) := by
  have h1 := registerClear_eval d target
  have h2 := ArithmeticCalls.copyAt_eval (0 : Fin 41) target 38 (cleared d target)
    ht.symm (by decide) h38.symm (by simp [cleared])
    (by simp [cleared, h38.symm, hs])
  have h3 := registerClear_eval (ArithmeticCalls.afterCopy 0 target (cleared d target)) 0
  convert h1.seq (h2.seq h3) using 1 <;>
    simp [ storedResult, cleared, ArithmeticCalls.afterCopy, ht.symm] ; omega

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native, source-preserving scalar operations on the preparation ABI.
Only the selected output changes; all low arithmetic scratch is restored. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

open BitProgram StructuredCalls ModularRingPrograms ModularDivisionPrograms
open SubexpLiftRing SubexpQuarticRing
open IdempotentProgram (storeResult storeResult_eval storedResult_stacks)

theorem callLow_eval {l : ℕ} (p : Program 8 8 l) (d : Data)
    (a b : State 8 8) (result : Fin 41 → List Bool) (n : ℕ)
    (hr : a.regs = d.regs)
    (ha : ∀ i, d.stacks (low i) = a.stacks i)
    (hb : ∀ i, result (low i) = b.stacks i)
    (hout : ∀ j, 8 ≤ j.val → result j = d.stacks j)
    (run : Trace p n (a.withPC (some p.entry)) (b.withPC none)) :
    ∃ e, Eval (callLow p) n d e ∧ e.stacks = result := by
  have he := eval_call_lifted p id low d Function.injective_id low_injective run
  have hin : embedState id low d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id low_injective
    · intro i; exact (congrFun hr i).symm
    · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
    · exact ha
    · intro i hi; rfl
  rw [hin] at he
  refine ⟨embedState id low d b, he, ?_⟩
  funext j
  by_cases hj : j.val < 8
  · let i : Fin 8 := ⟨j.val,hj⟩
    have hi : low i = j := Fin.ext rfl
    rw [←hi, embedState_stack _ _ _ _ low_injective]
    exact (hb i).symm
  · rw [embedState_stack_frame]
    · exact (hout j (by omega)).symm
    · rintro ⟨i,hi⟩
      have hval := congrArg Fin.val hi
      dsimp [low] at hval
      omega

theorem prepare_eval (d : Data) (left right : Fin 41) (m : List Bool)
    (h : Rest d m) (hl : 8 ≤ left.val) (hr : 8 ≤ right.val)
    (hl38 : left ≠ 38) (hr38 : right ≠ 38) :
    Eval (prepare left right) (7*(d.stacks left).length+7*(d.stacks right).length+10)
      d (operands d left right) := by
  have hl0 : left ≠ 0 := by intro he; subst left; contradiction
  have hr0 : right ≠ 0 := by intro he; subst right; contradiction
  have hr1 : right ≠ 1 := by intro he; subst right; contradiction
  have h0 : d.stacks 0 = [] := by simpa [low] using h.1 0
  have h1 : d.stacks 1 = [] := by simpa [low] using h.1 1
  have a := ArithmeticCalls.copyAt_eval left 0 38 d hl0 hl38 (by decide) h0 h.2
  have b := ArithmeticCalls.copyAt_eval right 1 38 (ArithmeticCalls.afterCopy left 0 d)
    hr1 hr38 (by decide) (by simp [ArithmeticCalls.afterCopy,h1])
    (by simp [ArithmeticCalls.afterCopy,h.2])
  convert a.seq b using 1 <;>
    simp [operands,ArithmeticCalls.afterCopy,hr0] ; omega

theorem binary_eval {l : ℕ} (p : Program 8 8 l) (d : Data)
    (m x y out : List Bool) (target left right : Fin 41) (n : ℕ) (rf : Fin 8 → Bool)
    (h : Rest d m) (ht : 8 ≤ target.val) (hl : 8 ≤ left.val) (hr : 8 ≤ right.val)
    (ht38 : target ≠ 38) (hl38 : left ≠ 38) (hr38 : right ≠ 38)
    (hx : d.stacks left = x) (hy : d.stacks right = y)
    (run : Trace p n
      ⟨some p.entry, (operands d left right).regs, extendSeven (scalarInput x y m) []⟩
      ⟨none,rf,extendSeven (resting out m []) []⟩) :
    ∃ e, Eval (binary p target left right)
      (n+7*x.length+7*y.length+2*(d.stacks target).length+9*out.length+21) d e ∧
      e.stacks = Function.update d.stacks target out := by
  have hr0 : right ≠ 0 := by intro he; subst right; contradiction
  have ht0 : target ≠ 0 := by intro he; subst target; contradiction
  have prep := prepare_eval d left right m h hl hr hl38 hr38
  have hops : (operands d left right).stacks =
      Function.update (Function.update d.stacks 0 x) 1 y := by
    simp [operands,ArithmeticCalls.afterCopy,hr0,hx,hy]
  obtain ⟨e,he,hes⟩ := callLow_eval p (operands d left right)
    ⟨(operands d left right).regs,extendSeven (scalarInput x y m) []⟩
    ⟨rf,extendSeven (resting out m []) []⟩
    (Function.update d.stacks 0 out) n rfl (by
      intro i
      have hi := h.1 i
      fin_cases i <;> simp [hops,low,extendSeven,scalarInput,seven] at hi ⊢ <;> exact hi)
    (by
      intro i
      have hi := h.1 i
      fin_cases i <;> simp [low,extendSeven,resting,seven] at hi ⊢ <;> exact hi)
    (by
      intro j hj
      have hj0 : j ≠ 0 := by intro hh; subst j; contradiction
      have hj1 : j ≠ 1 := by intro hh; subst j; contradiction
      simp [hops,hj0,hj1]) run
  have store := storeResult_eval e target ht0 ht38 (by rw [hes]; simpa using h.2)
  refine ⟨IdempotentProgram.storedResult e target,?_,?_⟩
  · convert prep.seq (he.seq store) using 1 ;
      simp [hx,hy,hes,ht0] ; omega
  · rw [storedResult_stacks e target ht0,hes]
    have h0 : d.stacks 0 = [] := by simpa [low] using h.1 0
    funext j
    by_cases hjt : j=target
    · subst j; simp [ht0]
    · by_cases hj0 : j=0
      · subst j; simp [hjt,h0]
      · simp [hjt,hj0]

variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)

theorem add_eval (d : Data) (target left right : Fin 41)
    (x y : Word (baseWidth p t)) (h : Rest d M.bits)
    (ht : 8 ≤ target.val) (hl : 8 ≤ left.val) (hr : 8 ≤ right.val)
    (ht38 : target ≠ 38) (hl38 : left ≠ 38) (hr38 : right ≠ 38)
    (hx : d.stacks left=x.val) (hy : d.stacks right=y.val) :
    ∃ n e, Eval (binary wordAddProgram target left right) n d e ∧
      e.stacks = Function.update d.stacks target (SubexpPreparedQuartic.wordAdd p t M x y).1.val ∧
      n ≤ 6000*(baseWidth p t+1)^2+23*baseWidth p t+2*(d.stacks target).length+21 := by
  obtain ⟨rf,n,hn,run⟩ := SubexpScalarMachine.wordAdd_run p t M (operands d left right).regs x y
  obtain ⟨e,he,hes⟩ := binary_eval wordAddProgram d M.bits x.val y.val _ target left right
    n rf h ht hl hr ht38 hl38 hr38 hx hy run
  refine ⟨_,e,he,hes,?_⟩
  rw [x.property,y.property,(SubexpPreparedQuartic.wordAdd p t M x y).1.property]
  omega

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarConstants
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

open BitProgram StructuredCalls ModularRingPrograms ModularDivisionPrograms
open SubexpLiftRing SubexpQuarticRing BinaryArithmetic ModularArithmetic

/-- Normalize a temporary word in stack zero, using the cached unary width. -/
abbrev normalize (target : Fin 41) : Cmd 8 41 :=
  .seq (ArithmeticCalls.copyAt 12 7 38)
    (.seq (callLow normalizeProgram) (IdempotentProgram.storeResult target))

theorem normalize_eval (d : Data) (m input shape : List Bool) (target : Fin 41)
    (ht : 8 ≤ target.val) (ht38 : target ≠ 38)
    (h12 : d.stacks 12=shape) (h0 : d.stacks 0=input)
    (hrest : ∀ i : Fin 8, i ≠ 0 → d.stacks (low i)=if i=5 then m else [])
    (h38 : d.stacks 38=[]) :
    ∃ n e, Eval (normalize target) n d e ∧
      e.stacks=Function.update (Function.update d.stacks target (padTo shape input)) 0 [] ∧
      n ≤ 23*shape.length+2*input.length+2*(d.stacks target).length+25 := by
  let a := ArithmeticCalls.afterCopy 12 7 d
  have h7 : d.stacks 7=[] := by simpa [low] using hrest 7 (by decide)
  have cp := ArithmeticCalls.copyAt_eval (12:Fin 41) 7 38 d (by decide) (by decide)
    (by decide) h7 h38
  obtain ⟨rf,n,hn,run⟩ := normalize_correct a.regs input shape m
  have ht0 : target ≠ 0 := by intro h; subst target; contradiction
  have ht7 : target ≠ 7 := by intro h; subst target; omega
  obtain ⟨e,he,hes⟩ := callLow_eval normalizeProgram a
    ⟨a.regs,normalizationState input shape [] m⟩
    ⟨rf,normalizationState (padTo shape input) [] [] m⟩
    (Function.update d.stacks 0 (padTo shape input)) n rfl (by
      intro i
      by_cases hi : i=0
      · subst i; simp [a,ArithmeticCalls.afterCopy,low,normalizationState,h0]
      · have hh := hrest i hi
        fin_cases i <;> simp_all [a,ArithmeticCalls.afterCopy,low,normalizationState])
    (by
      intro i
      by_cases hi : i=0
      · subst i; rfl
      · have hh := hrest i hi
        fin_cases i <;> simp_all [low,normalizationState])
    (by
      intro j hj
      have hj0 : j≠0 := by intro h; subst j; omega
      have hj7 : j≠7 := by intro h; subst j; omega
      simp [a,ArithmeticCalls.afterCopy,hj0,hj7]) run
  have st := IdempotentProgram.storeResult_eval e target ht0 ht38 (by rw [hes]; simpa using h38)
  refine ⟨_,IdempotentProgram.storedResult e target,cp.seq (he.seq st),?_,?_⟩
  · rw [IdempotentProgram.storedResult_stacks e target ht0,hes]
    funext j
    by_cases hj : j=0
    · subst j; simp
    · by_cases hjt : j=target
      · subst j; simp [ht0]
      · simp [hj,hjt]
  · simp only [hes,Function.update_same,padTo_length]
    have hlen : (a.stacks 12).length=shape.length := by simp [a,ArithmeticCalls.afterCopy,h12]
    simp only [h12,Function.update_of_ne ht0] at *
    omega

abbrev literal (target : Fin 41) (bits : List Bool) : Cmd 8 41 :=
  .seq (literalAt 0 bits) (normalize target)

theorem literal_eval (d : Data) (m shape : List Bool) (target : Fin 41)
    (bits : List Bool) (h : Rest d m) (h12 : d.stacks 12=shape)
    (ht : 8 ≤ target.val) (ht38 : target≠38) :
    ∃ n e, Eval (literal target bits) n d e ∧
      e.stacks=Function.update d.stacks target (padTo shape bits) ∧
      n ≤ 23*shape.length+4*bits.length+2*(d.stacks target).length+25 := by
  let a := literalResult d 0 bits
  have h0 : d.stacks 0=[] := by simpa [low] using h.1 0
  have ha : a.stacks=Function.update d.stacks 0 bits := by simp [a,literalResult_stacks,h0]
  obtain ⟨n,e,he,hes,hn⟩ := normalize_eval a m bits shape target ht ht38
    (by simp [ha,h12]) (by simp [ha]) (by
      intro i hi
      have hlow : low i ≠ 0 := by intro h; apply hi; exact low_injective h
      simpa [ha,hlow] using h.1 i) (by simp [ha,h.2])
  have ht0 : target≠0 := by intro h; subst target; omega
  refine ⟨_,e,(literalAt_eval d 0 bits).seq he,?_,?_⟩
  · rw [hes,ha]
    funext j
    by_cases hj : j=0
    · subst j; simp [ht0.symm,h0]
    · by_cases hjt : j=target
      · subst j; simp [ht0]
      · simp [hj,hjt]
  · simp only [ha,Function.update_of_ne ht0] at hn
    omega

abbrev negativeOne (target : Fin 41) : Cmd 8 41 :=
  .seq (ArithmeticCalls.copyAt 5 0 38)
    (.seq (CounterForPrograms.decrementCmd decrementPorts) (normalize target))

theorem negativeOne_eval (d : Data) (m shape : List Bool) (target : Fin 41)
    (h : Rest d m) (h12 : d.stacks 12=shape) (hm : 0 < BinaryArithmetic.toNat m)
    (ht : 8 ≤ target.val) (ht38 : target≠38) :
    ∃ n e, Eval (negativeOne target) n d e ∧
      e.stacks=Function.update d.stacks target (padTo shape (CounterPrograms.ripple false m)) ∧
      n ≤ 23*shape.length+17*m.length+2*(d.stacks target).length+38 := by
  let a := ArithmeticCalls.afterCopy 5 0 d
  let b := CounterForPrograms.decrementResult decrementPorts a
  have h0 : d.stacks 0=[] := by simpa [low] using h.1 0
  have h5 : d.stacks 5=m := by simpa [low] using h.1 5
  have ha : a.stacks=Function.update d.stacks 0 m := by simp [a,ArithmeticCalls.afterCopy,h5]
  have cp := ArithmeticCalls.copyAt_eval (5:Fin 41) 0 38 d (by decide) (by decide)
    (by decide) h0 h.2
  have h2 : a.stacks 2=[] := by simpa [ha,low] using h.1 2
  have dc := CounterForPrograms.decrement_eval decrementPorts a h2
  have hb : b.stacks=Function.update d.stacks 0 (CounterPrograms.ripple false m) := by
    funext j
    by_cases hj0 : j=0
    · subst j
      change (CounterForPrograms.decrementResult decrementPorts a).stacks decrementPorts.counter = _
      rw [CounterForPrograms.decrementResult_counter]
      simp [decrementPorts,ha]
    · by_cases hj2 : j=2
      · subst j
        change (CounterForPrograms.decrementResult decrementPorts a).stacks decrementPorts.scratch = _
        rw [CounterForPrograms.decrementResult_scratch]
        simpa [low] using (h.1 2).symm
      · rw [show b.stacks j = a.stacks j from
          CounterForPrograms.install_other_stack decrementPorts a _ _ _ _ _ j hj0 hj2]
        simp [ha,hj0]
  obtain ⟨n,e,he,hes,hn⟩ := normalize_eval b m (CounterPrograms.ripple false m) shape target
    ht ht38 (by simp [hb,h12]) (by simp [hb]) (by
      intro i hi
      have hlow : low i≠0 := by intro h; apply hi; exact low_injective h
      simpa [hb,hlow] using h.1 i) (by simp [hb,h.2])
  have ht0 : target≠0 := by intro h; subst target; omega
  refine ⟨_,e,cp.seq (dc.seq he),?_,?_⟩
  · rw [hes,hb]
    funext j
    by_cases hj : j=0
    · subst j; simp [ht0.symm,h0]
    · by_cases hjt : j=target
      · subst j; simp [ht0]
      · simp [hj,hjt]
  · have hc := CounterPrograms.rippleCost_le false m
    have hmv : 0 < CounterPrograms.value m := by simpa [CounterPrograms.value_eq_toNat] using hm
    have hl := CounterPrograms.decrement_length hmv
    simp only [hb,Function.update_of_ne ht0] at hn
    simp only [decrementPorts,ha,Function.update_same,h5]
    rw [hl] at hn
    omega

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarMachine
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed register language for the twelve scalar cache/temporary words.
Its interpreter is actual finite code, not a unit-cost arithmetic oracle. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar
open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing ModularRingPrograms

variable (p t : ℕ) [Fact p.Prime]
abbrev Values := Reg → Word (baseWidth p t)

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

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

def zeroValue (shape : List Bool) (hshape : shape.length=baseWidth p t) : Word (baseWidth p t) :=
  ⟨padTo shape [],by simp [padTo_length,hshape]⟩

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

def oneValue (shape : List Bool) (hs:shape.length=baseWidth 3 t) : Word (baseWidth 3 t) :=
  ⟨padTo shape [true],by simp [padTo_length,hs]⟩

def minusValue (M : SubexpPreparedQuartic.Modulus 3 t)
    (shape : List Bool) (hs:shape.length=baseWidth 3 t) : Word (baseWidth 3 t) :=
  ⟨padTo shape (CounterPrograms.ripple false M.bits),by simp [padTo_length,hs]⟩

def baseValues (M : SubexpPreparedQuartic.Modulus 3 t)
    (shape : List Bool) (hs:shape.length=baseWidth 3 t) : Values 3 t :=
  Function.update (Function.update (fun _=>zeroValue 3 t shape hs) 1 (oneValue t shape hs))
    9 (minusValue t M shape hs)

theorem zeroValue_nat (shape:List Bool) (hs:shape.length=baseWidth 3 t) :
    BinaryArithmetic.toNat (zeroValue 3 t shape hs).val=0 := by
  apply padTo_value_of_lt
  simp

theorem oneValue_nat (ht:0 < t) (shape:List Bool) (hs:shape.length=baseWidth 3 t) :
    BinaryArithmetic.toNat (oneValue t shape hs).val=1 := by
  have hb : 0 < shape.length := by rw [hs,RingProgram.ternary_baseWidth]; omega
  have hp : BinaryArithmetic.toNat [true] < 2^shape.length :=
    Nat.one_lt_pow (Nat.ne_of_gt hb) Nat.one_lt_two
  exact padTo_value_of_lt shape [true] hp

theorem minusValue_nat (M:SubexpPreparedQuartic.Modulus 3 t)
    (shape:List Bool) (hs:shape.length=baseWidth 3 t) :
    BinaryArithmetic.toNat (minusValue t M shape hs).val=3^t-1 := by
  have hm:0 < CounterPrograms.value M.bits := by rw [CounterPrograms.value_eq_toNat,M.value]; positivity
  have hv : BinaryArithmetic.toNat (CounterPrograms.ripple false M.bits)=3^t-1 := by
    have hh:=CounterPrograms.value_decrement hm
    rw [CounterPrograms.value_eq_toNat,CounterPrograms.value_eq_toNat,M.value] at hh
    omega
  have hcap : BinaryArithmetic.toNat (CounterPrograms.ripple false M.bits) < 2^shape.length := by
    rw [hv,hs]
    have cap:=modulus_le_width 3 t
    have hp:0 < 3^t:=by positivity
    omega
  exact (padTo_value_of_lt shape _ hcap).trans hv

theorem baseValues_correct (ht:0 < t) (M:SubexpPreparedQuartic.Modulus 3 t)
    (shape:List Bool) (hs:shape.length=baseWidth 3 t) :
    wordValue 3 t (baseValues t M shape hs 0)=0 ∧
    wordValue 3 t (baseValues t M shape hs 1)=1 ∧
    wordValue 3 t (baseValues t M shape hs 9) = -1 ∧
    (∀i,BinaryArithmetic.toNat (baseValues t M shape hs i).val < 3^t) := by
  have hz:=zeroValue_nat t shape hs
  have ho:=oneValue_nat t ht shape hs
  have hn:=minusValue_nat t M shape hs
  have hp:1 < 3^t:=by exact Nat.one_lt_pow (Nat.ne_of_gt ht) (by decide)
  have hm: ((3^t-1:ℕ):ZMod (3^t)) = -1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 3^t),Nat.cast_one,ZMod.natCast_self,zero_sub]
  constructor
  · simp [baseValues,wordValue,hz]
  constructor
  · simp [baseValues,wordValue,ho]
  constructor
  · simp [baseValues,wordValue,hn]
  · intro i
    by_cases h9:i=9
    · subst i; simp [baseValues,hn]
    · by_cases h1:i=1
      · subst i; simpa [baseValues,ho] using hp
      · simp [baseValues,h9,h1,hz]

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar
open SubexpLiftRing SubexpQuarticRing

variable (p t : ℕ) [Fact p.Prime]

def decode (v : Values p t) : Reg → ZMod (p^t) := fun i=>wordValue p t (v i)

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

theorem naturalRun_canonical
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t) (n : ℕ) :
    BinaryArithmetic.toNat (naturalRun (RingProgram.scalarProgram p t M cache) n).1.val < p^t := by
  cases n with
  | zero => exact hz
  | succ n => exact SubexpPreparedQuartic.wordAdd_canonical p t M _ _

theorem integerRun_canonical
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t) (z : ℤ) :
    BinaryArithmetic.toNat (integerRun (RingProgram.scalarProgram p t M cache) z).1.val < p^t := by
  cases z with
  | ofNat n => exact naturalRun_canonical p t M cache hz n
  | negSucc n => exact RingProgram.wordMul_canonical p t M _ _

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarOutput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar
open SubexpLiftRing SubexpQuarticRing BinaryArithmetic

variable (p t : ℕ) [Fact p.Prime]

def Canonical (v:Values p t) : Prop := ∀i,BinaryArithmetic.toNat (v i).val < p^t

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramWords
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Instantiation on fixed-width Boolean words modulo 3^t.  The scalar
callbacks have existing primitive bit-program refinements.  The remaining
native obligation is the runtime-sized array traversal and Newton controller,
not an unprovided algebraic oracle. -/

namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

/-- Table serialization is k-major, then i, with j fastest, matching the
native expansion/contraction service. -/
def tableWords {d B : ℕ} (table : Fin d → Fin d → Fin d → Word B) : List (Word B) :=
  (List.ofFn fun k : Fin d =>
    (List.ofFn fun i : Fin d => List.ofFn fun j : Fin d => table i j k).flatten).flatten

def tableTape {d B : ℕ} (table : Fin d → Fin d → Fin d → Word B) : List Bool :=
  ((tableWords table).map Subtype.val).flatten

@[simp] theorem tableWords_length {d B : ℕ}
    (table : Fin d → Fin d → Fin d → Word B) : (tableWords table).length = d^3 := by
  simp [tableWords, List.length_flatten, List.map_ofFn, List.sum_ofFn]
  ring

@[simp] theorem tableTape_length {d B : ℕ}
    (table : Fin d → Fin d → Fin d → Word B) : (tableTape table).length = d^3*B := by
  have hlen : ∀ xs : List (Word B), ((xs.map Subtype.val).flatten).length = xs.length*B := by
    intro xs
    induction xs with
    | nil => simp
    | cons a xs ih =>
        simp only [List.map_cons, List.flatten_cons, List.length_append,
          List.length_cons, ih, a.property, Nat.add_mul, Nat.one_mul]
        omega
  rw [tableTape, hlen, tableWords_length]

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramNormalize
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms



namespace SubexponentialSAT.SqrtLog.MomentsProgram.Normalize
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev Data := State 8 28

end SubexponentialSAT.SqrtLog.MomentsProgram.Normalize


end OAI.Algorithms
end


