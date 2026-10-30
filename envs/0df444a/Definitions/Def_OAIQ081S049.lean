-- Prove2me | Definitions.Def_OAIQ081S049
-- name    : OAIQ081S049
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:36:33.549136+00:00
-- url     : https://prove2.me/theorems/3372630d-da10-46df-bc1b-d901c8314035
-- title:
--   Definitions bundle OAIQ081S049 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 44 declarations of OpenAI's Lean: 10 definitions and 34 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.NativeInverse.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.ServiceSpec`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.tripleValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.leftBits`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.rightBits`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.sumBits`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Setup.increment`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairScoreProgram.readPlan`, `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.ExecutesIn`, `OAI.Algorithms.SubexponentialSAT.SubexpKernelControl.operators`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_CRTLocalProgramLoops`, `SubexponentialSAT_SqrtLog_CRTLocalProgramNativeInverse`, `SubexponentialSAT_SqrtLog_RingProgramFold`, `SubexponentialSAT_SqrtLog_RingScanAdd`, `SubexponentialSAT_SqrtLog_RingScanAddLoop`, `SubexponentialSAT_SqrtLog_RingScanContract`, `SubexponentialSAT_SqrtLog_RingScanContractLoop`, `SubexponentialSAT_SqrtLog_RingScanCount`, `SubexponentialSAT_SqrtLog_RingScanLoad`, `SubexponentialSAT_SqrtLog_RingScanServiceAdd`, `SubexponentialSAT_SqrtLog_RingScanServiceBasic`, `SubexponentialSAT_SqrtLog_RingScanServiceLifts`, `SubexponentialSAT_SqrtLog_RingScanTriple`, `SubexponentialSAT_SqrtLog_RingTripleBasic`, `SubexponentialSAT_SqrtLog_RingTripleExpand`, `SubexponentialSAT_SqrtLog_RingTripleMatrix`, `SubexponentialSAT_SqrtLog_RingTripleProgram`, `SubexponentialSAT_SqrtLog_RingTripleRows`, `SubexponentialSAT_SqrtLog_SetupPrimitives`, `SubexponentialSAT_SubexpConvolutionStore`, `SubexponentialSAT_SubexpKernelControl`, `SubexponentialSAT_Subexp_PairScoreProgram`.
--
--   **Imports.** It imports the bundles `OAIQ081S023`, `OAIQ081S024`, `OAIQ081S025`, `OAIQ081S027`, `OAIQ081S028` and `OAIQ081S032` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S068`, `OAIQ081S069`, `OAIQ081S070`, `OAIQ081S073`, `OAIQ081S077` and `OAIQ081S081`; the statement `OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixServices.program_runsIn`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ081S023
import Definitions.Def_OAIQ081S024
import Definitions.Def_OAIQ081S025
import Definitions.Def_OAIQ081S027
import Definitions.Def_OAIQ081S028
import Definitions.Def_OAIQ081S032

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpConvolutionStore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Stack-only contracts for the concrete copies, fixed-width reads, and unary
counter updates in the convolution controller. Register values are genuine
outputs of the executed commands, but are unrestricted between these blocks. -/

namespace SubexponentialSAT.SubexpConvolutionControl

open BitProgram StructuredCalls SubexpScanPrimitives

def ExecutesIn (cmd : Code) (budget : ℕ) (before after : Store) : Prop :=
  ∀ regs : Fin 16 → Bool, ∃ n regs', n ≤ budget ∧
    Eval cmd n ⟨regs, before⟩ ⟨regs', after⟩

theorem ExecutesIn.seq {a b : Code} {ca cb : ℕ} {s t u : Store}
    (ha : ExecutesIn a ca s t) (hb : ExecutesIn b cb t u) :
    ExecutesIn (.seq a b) (ca + cb) s u := by
  intro regs
  obtain ⟨na, ra, hna, hea⟩ := ha regs
  obtain ⟨nb, rb, hnb, heb⟩ := hb ra
  exact ⟨na + nb, rb, Nat.add_le_add hna hnb, hea.seq heb⟩

theorem ExecutesIn.mono {cmd : Code} {a b : ℕ} {s t : Store}
    (h : ExecutesIn cmd a s t) (hab : a ≤ b) : ExecutesIn cmd b s t := by
  intro regs
  obtain ⟨n, regs', hn, he⟩ := h regs
  exact ⟨n, regs', hn.trans hab, he⟩

end SubexponentialSAT.SubexpConvolutionControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramLoops
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native loops used by independent-precision local Hermite CRT.

The arithmetic argument is a finite `Cmd`, never a semantic instruction.
`ServiceSpec` is the exact trace contract discharged by the native represented
ring/array callbacks. All iteration counts remain on runtime stack 246.
-/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

/-- Arithmetic consumes neither input. Its sole changed stack is output 244. -/
def ServiceSpec {C : Type*} (base : Store) (encode : C → List Bool)
    (code : Code) (op : C → C → C) (K : ℕ) : Prop :=
  ∀ (s : Store) (a b : C), LowFrame base s →
    s 240 = encode a → s 241 = encode b → s 244 = [] → s 245 = [] →
    ExecutesIn code K s (Function.update s 244 (encode (op a b)))

theorem serviceSpec_frame {C : Type*} {base next : Store} {encode : C → List Bool}
    {code : Code} {op : C → C → C} {K : ℕ}
    (h : ServiceSpec base encode code op K) (hn : LowFrame base next) :
    ServiceSpec next encode code op K := by
  intro s a b hs
  exact h s a b (lowFrame_trans hn hs)

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramFold
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgram

open scoped BigOperators
open SubexponentialSAT.SubexpSymbolicCost

variable {C A : Type*} [CommRing A]

def tripleValue (ops : RepresentedRing C A) (x : Triple C) : A :=
  ops.decode x.1 * ops.decode x.2.1 * ops.decode x.2.2

end SubexponentialSAT.SqrtLog.RingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanLoad
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed-control dynamic coefficient loader

The source contains a flat vector. A preserved unary width word determines
how many bits are removed. Exactly that many bits are prefixed, in their
original order, to the destination. Control size is independent of both the
width and the number of coefficients.
-/
namespace SubexponentialSAT.SqrtLog.RingScan

open BitProgram StructuredCalls StackRoutines ArrayPrograms

theorem load_counted_stacks (word tail dst width : List Bool) :
    countedTransferStacks (3 : Fin 5) 0 4 word tail
      (loadTapes (word ++ tail) dst width width []) =
      loadTapes tail dst width [] word.reverse := by
  funext i
  fin_cases i <;> simp [countedTransferStacks, loadTapes]

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanAdd
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native scalar addition inside a flat, runtime-sized coefficient scan. -/
namespace SubexponentialSAT.SqrtLog.RingScan

open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem embed_loadX (regs : Fin 8 → Bool) (v pr : Bool)
    (modulus oldLeft newLeft right oldXs newXs ys out count width : List Bool) :
    embedState loadRegisters loadXStacks
      (addState regs modulus oldLeft right oldXs ys out count width)
      (loadState ![v, pr] newXs newLeft width [] []) =
      addState (Function.update (Function.update regs 1 v) 3 pr)
        modulus newLeft right newXs ys out count width := by
  apply embedState_eq_of_ports _ _ _ _ _ loadRegisters_injective loadXStacks_injective
  · intro i; fin_cases i <;> simp [loadRegisters, loadState, addState]
  · intro i hi
    have h1 : i ≠ 1 := fun h => hi ⟨0, h.symm⟩
    have h3 : i ≠ 3 := fun h => hi ⟨1, h.symm⟩
    simp [addState, h1, h3]
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h0 : i ≠ 0 := fun h => hi ⟨1, h.symm⟩
    have h8 : i ≠ 8 := fun h => hi ⟨0, h.symm⟩
    simp [addState, addTapes, h0, h8]

theorem embed_loadY (regs : Fin 8 → Bool) (v pr : Bool)
    (modulus left oldRight newRight xs oldYs newYs out count width : List Bool) :
    embedState loadRegisters loadYStacks
      (addState regs modulus left oldRight xs oldYs out count width)
      (loadState ![v, pr] newYs newRight width [] []) =
      addState (Function.update (Function.update regs 1 v) 3 pr)
        modulus left newRight xs newYs out count width := by
  apply embedState_eq_of_ports _ _ _ _ _ loadRegisters_injective loadYStacks_injective
  · intro i; fin_cases i <;> simp [loadRegisters, loadState, addState]
  · intro i hi
    have h1 : i ≠ 1 := fun h => hi ⟨0, h.symm⟩
    have h3 : i ≠ 3 := fun h => hi ⟨1, h.symm⟩
    simp [addState, h1, h3]
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h1 : i ≠ 1 := fun h => hi ⟨1, h.symm⟩
    have h9 : i ≠ 9 := fun h => hi ⟨0, h.symm⟩
    simp [addState, addTapes, h1, h9]

theorem embed_scalar (regs oldRegs : Fin 8 → Bool)
    (modulus left right oldLeft oldRight xs ys out count width : List Bool) :
    embedState id scalarStacks (addState oldRegs modulus oldLeft oldRight xs ys out count width)
      ⟨regs, ModularRingPrograms.extendSeven (ModularRingPrograms.scalarInput left right modulus) []⟩ =
      addState regs modulus left right xs ys out count width := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id scalarStacks_injective
  · intro i; rfl
  · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h0 : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
    have h1 : i ≠ 1 := fun h => hi ⟨1, h.symm⟩
    simp [addState, addTapes, h0, h1]

theorem emitReverse_eval (regs : Fin 8 → Bool)
    (modulus word xs ys out count width : List Bool) :
    Eval emitReverse (3 * word.length + 3)
      (addState regs modulus word [] xs ys out count width)
      (addState (readRegs regs 1 3 none) modulus [] [] xs ys
        (word.reverse ++ out) count width) := by
  have ht := transferProgram_trace (0 : Fin 15) 10 (1 : Fin 8) 3
    (by decide) (by decide) regs (addTapes modulus word [] xs ys out count width)
  have hh := halt_after_trace _ ht 3 rfl rfl
  apply Eval.call
  simpa only [addState, StructuredProgram.State.withPC, transferResult, emit_stacks,
    show addTapes modulus word [] xs ys out count width 0 = word from rfl,
    Nat.add_assoc] using hh

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanAddLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The vector length is a unary input, never a generated list of instructions. -/
namespace SubexponentialSAT.SqrtLog.RingScan

open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def leftBits {B : ℕ} : List (Word B × Word B) → List Bool
  | [] => []
  | x :: xs => x.1.val ++ leftBits xs

def rightBits {B : ℕ} : List (Word B × Word B) → List Bool
  | [] => []
  | x :: xs => x.2.val ++ rightBits xs

def sumBits (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t) :
    List (Word (baseWidth p t) × Word (baseWidth p t)) → List Bool
  | [] => []
  | x :: xs => (SubexpPreparedQuartic.wordAdd p t M x.1 x.2).1.val ++ sumBits p t M xs

theorem popCount_eval (regs : Fin 8 → Bool)
    (modulus left right xs ys out count width : List Bool) :
    Eval popCount 1 (addState regs modulus left right xs ys out count width)
      (addState (readRegs regs 1 3 count.head?) modulus left right xs ys out count.tail width) := by
  apply Eval.base
  convert StructuredProgram.Eval.atom (StructuredProgram.Atom.pop (r := 8) (s := 15) 11 1 3)
    (addState regs modulus left right xs ys out count width) using 1
  all_goals try with_reducible_and_instances rfl
  cases count <;> simp [ StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr,
    addState,
    addTapes, update_count]

theorem finishAdd_eval (regs : Fin 8 → Bool) (modulus out width : List Bool) :
    Eval finishAdd (3 * out.length + 3)
      (addState regs modulus [] [] [] [] out [] width)
      (addState (readRegs regs 1 3 none) modulus out.reverse [] [] [] [] [] width) := by
  have ht := transferProgram_trace (10 : Fin 15) 0 (1 : Fin 8) 3
    (by decide) (by decide) regs (addTapes modulus [] [] [] [] out [] width)
  have hh := halt_after_trace _ ht 3 rfl rfl
  apply Eval.call
  simpa only [addState, StructuredProgram.State.withPC, transferResult, finish_stacks,
    show addTapes modulus [] [] [] [] out [] width 10 = out from rfl,
    Nat.add_assoc] using hh

theorem sumBits_length (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (pairs : List (Word (baseWidth p t) × Word (baseWidth p t))) :
    (sumBits p t M pairs).length = pairs.length * baseWidth p t := by
  induction pairs with
  | nil => simp [sumBits]
  | cons pair pairs ih =>
      simp only [sumBits, List.length_append, ih, List.length_cons]
      rw [(SubexpPreparedQuartic.wordAdd p t M pair.1 pair.2).1.property]
      simp [Nat.add_mul, Nat.add_comm]

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanTriple
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A native three-scalar product and accumulator step. Triples are serialized
as consecutive fixed-width words; both width and triple count remain data. -/
namespace SubexponentialSAT.SqrtLog.RingScan

open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem embed_loadHead (regs : Fin 8 → Bool) (v pr : Bool)
    (modulus oldLeft newLeft right xs oldYs newYs out count width : List Bool) :
    embedState loadRegisters loadHeadStacks
      (addState regs modulus oldLeft right xs oldYs out count width)
      (loadState ![v, pr] newYs newLeft width [] []) =
      addState (Function.update (Function.update regs 1 v) 3 pr)
        modulus newLeft right xs newYs out count width := by
  apply embedState_eq_of_ports _ _ _ _ _ loadRegisters_injective loadHeadStacks_injective
  · intro i; fin_cases i <;> simp [loadRegisters, loadState, addState]
  · intro i hi
    have h1 : i ≠ 1 := fun h => hi ⟨0, h.symm⟩
    have h3 : i ≠ 3 := fun h => hi ⟨1, h.symm⟩
    simp [addState, h1, h3]
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h0 : i ≠ 0 := fun h => hi ⟨1, h.symm⟩
    have h9 : i ≠ 9 := fun h => hi ⟨0, h.symm⟩
    simp [addState, addTapes, h0, h9]

theorem restoreAccumulator_eval (regs : Fin 8 → Bool)
    (modulus term xs ys saved count width : List Bool) :
    Eval restoreAccumulator (3 * saved.length + 3)
      (addState regs modulus term [] xs ys saved count width)
      (addState (readRegs regs 1 3 none) modulus term saved.reverse xs ys [] count width) := by
  have ht := transferProgram_trace (10 : Fin 15) 1 (1 : Fin 8) 3
    (by decide) (by decide) regs (addTapes modulus term [] xs ys saved count width)
  have hh := halt_after_trace _ ht 3 rfl rfl
  apply Eval.call
  simpa only [addState, StructuredProgram.State.withPC, transferResult, restore_stacks,
    show addTapes modulus term [] xs ys saved count width 10 = saved from rfl,
    Nat.add_assoc] using hh

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanContract
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed outer loop contracts a runtime-sized sequence of triple blocks. -/
namespace SubexponentialSAT.SqrtLog.RingScan
open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem embed_contract (regs oldRegs : Fin 8 → Bool)
    (modulus left oldLeft stream oldStream count oldCount width outer inner zero out : List Bool) :
    embedState id contractLower
      (contractState oldRegs modulus oldLeft oldStream oldCount width outer inner zero out)
      (addState regs modulus left [] [] stream [] count width) =
      contractState regs modulus left stream count width outer inner zero out := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id contractLower_injective
  · intro i; rfl
  · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h0 : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
    have h9 : i ≠ 9 := fun h => hi ⟨9, h.symm⟩
    have h11 : i ≠ 11 := fun h => hi ⟨11, h.symm⟩
    simp [contractState, contractTapes, h0, h9, h11]

theorem contractCopyCount_eval (regs : Fin 8 → Bool)
    (modulus stream width outer inner zero out : List Bool) :
    Eval contractCopyCount (7 * inner.length + 5)
      (contractState regs modulus [] stream [] width outer inner zero out)
      (contractState (readRegs regs 1 3 none) modulus [] stream inner width outer inner zero out) := by
  have ht := copyProgram_trace (16 : Fin 20) 11 19 (1 : Fin 8) 3
    (by decide) (by decide) (by decide) (by decide) regs
    (contractTapes modulus [] stream [] width outer inner zero out) (by rfl)
  have hh := halt_after_trace _ ht 7 rfl rfl
  apply Eval.call
  simpa only [contractState, StructuredProgram.State.withPC, copyResult, copy_count_stacks,
    show contractTapes modulus [] stream [] width outer inner zero out 16 = inner from rfl,
    Nat.add_assoc] using hh

theorem contractCopyZero_eval (regs : Fin 8 → Bool)
    (modulus stream count width outer inner zero out : List Bool) :
    Eval contractCopyZero (7 * zero.length + 5)
      (contractState regs modulus [] stream count width outer inner zero out)
      (contractState (readRegs regs 1 3 none) modulus zero stream count width outer inner zero out) := by
  have ht := copyProgram_trace (17 : Fin 20) 0 19 (1 : Fin 8) 3
    (by decide) (by decide) (by decide) (by decide) regs
    (contractTapes modulus [] stream count width outer inner zero out) (by rfl)
  have hh := halt_after_trace _ ht 7 rfl rfl
  apply Eval.call
  simpa only [contractState, StructuredProgram.State.withPC, copyResult, copy_zero_stacks,
    show contractTapes modulus [] stream count width outer inner zero out 17 = zero from rfl,
    Nat.add_assoc] using hh

theorem contractEmit_eval (regs : Fin 8 → Bool)
    (modulus word stream width outer inner zero out : List Bool) :
    Eval contractEmit (3 * word.length + 3)
      (contractState regs modulus word stream [] width outer inner zero out)
      (contractState (readRegs regs 1 3 none) modulus [] stream [] width outer inner zero
        (word.reverse ++ out)) := by
  have ht := transferProgram_trace (0 : Fin 20) 18 (1 : Fin 8) 3
    (by decide) (by decide) regs (contractTapes modulus word stream [] width outer inner zero out)
  have hh := halt_after_trace _ ht 3 rfl rfl
  apply Eval.call
  simpa only [contractState, StructuredProgram.State.withPC, transferResult, contract_emit_stacks,
    show contractTapes modulus word stream [] width outer inner zero out 0 = word from rfl,
    Nat.add_assoc] using hh

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanContractLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native whole-vector contraction, with both dimensions held on data tapes. -/
namespace SubexponentialSAT.SqrtLog.RingScan
open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem contractPop_eval (regs : Fin 8 → Bool)
    (modulus left stream count width outer inner zero out : List Bool) :
    Eval contractPop 1 (contractState regs modulus left stream count width outer inner zero out)
      (contractState (readRegs regs 1 3 outer.head?) modulus left stream count width outer.tail inner zero out) := by
  apply Eval.base
  convert StructuredProgram.Eval.atom (StructuredProgram.Atom.pop (r := 8) (s := 20) 15 1 3)
    (contractState regs modulus left stream count width outer inner zero out) using 1
  all_goals try with_reducible_and_instances rfl
  cases outer <;> simp [ StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr,
    contractState, contractTapes, update_outer]

theorem contractFinish_eval (regs : Fin 8 → Bool) (modulus stream width inner zero out : List Bool) :
    Eval contractFinish (3 * out.length + 3)
      (contractState regs modulus [] stream [] width [] inner zero out)
      (contractState (readRegs regs 1 3 none) modulus out.reverse stream [] width [] inner zero []) := by
  have ht := transferProgram_trace (18 : Fin 20) 0 (1 : Fin 8) 3
    (by decide) (by decide) regs (contractTapes modulus [] stream [] width [] inner zero out)
  have hh := halt_after_trace _ ht 3 rfl rfl
  apply Eval.call
  simpa only [contractState, StructuredProgram.State.withPC, transferResult, contract_finish_stacks,
    show contractTapes modulus [] stream [] width [] inner zero out 18 = out from rfl,
    Nat.add_assoc] using hh

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanCount
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed native loop produces a unary square from a unary input. -/
namespace SubexponentialSAT.SqrtLog.RingScan
open BitProgram StructuredCalls StackRoutines

theorem countCopy_eval (regs : Fin 2 → Bool) (source counter out : List Bool) :
    Eval countCopy (7*source.length+5) (countState regs source counter out)
      (countState (readRegs regs 0 1 none) source counter (source ++ out)) := by
  apply Eval.call
  simpa only [countState, StructuredProgram.State.withPC, copyResult, count_copy_stacks,
    show countTapes source counter out 0 = source from rfl, Nat.add_assoc] using
    ListRegisterProgram.copy_run (0 : Fin 4) 2 3 (0 : Fin 2) 1
      (by decide) (by decide) (by decide) (by decide) regs (countTapes source counter out) (by rfl)

theorem countInit_eval (regs : Fin 2 → Bool) (source out : List Bool) :
    Eval countInit (7*source.length+5) (countState regs source [] out)
      (countState (readRegs regs 0 1 none) source source out) := by
  apply Eval.call
  simpa only [countState, StructuredProgram.State.withPC, copyResult, count_init_stacks,
    show countTapes source [] out 0 = source from rfl, Nat.add_assoc] using
    ListRegisterProgram.copy_run (0 : Fin 4) 1 3 (0 : Fin 2) 1
      (by decide) (by decide) (by decide) (by decide) regs (countTapes source [] out) (by rfl)

theorem countPop_eval (regs : Fin 2 → Bool) (source counter out : List Bool) :
    Eval countPop 1 (countState regs source counter out)
      (countState (readRegs regs 0 1 counter.head?) source counter.tail out) := by
  apply Eval.base
  convert StructuredProgram.Eval.atom (StructuredProgram.Atom.pop (r := 2) (s := 4) 1 0 1)
    (countState regs source counter out) using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i; fin_cases i <;> cases counter <;>
      simp [ StructuredProgram.Atom.instr, execInstr, countTapes]

theorem countLoop_eval (regs : Fin 2 → Bool) (source counter out : List Bool) :
    ∃ rf, Eval countLoop (counter.length*(7*source.length+7)+1)
      (countState (readRegs regs 0 1 counter.head?) source counter.tail out)
      (countState rf source [] (repeatCount source counter.length ++ out)) := by
  induction counter generalizing regs out with
  | nil =>
      refine ⟨readRegs regs 0 1 none, ?_⟩
      simp only [List.length_nil, Nat.zero_mul, Nat.zero_add, List.head?_nil, List.tail_nil, repeatCount, List.nil_append]
      apply Eval.while_false
      simp [ readRegs_present]
  | cons bit counter ih =>
      have hc := countCopy_eval (readRegs regs 0 1 (some bit)) source counter out
      have hp := countPop_eval (readRegs (readRegs regs 0 1 (some bit)) 0 1 none) source counter (source ++ out)
      obtain ⟨rf, hl⟩ := ih (readRegs (readRegs regs 0 1 (some bit)) 0 1 none) (source ++ out)
      have he := Eval.while_true
        (show (countState (readRegs regs 0 1 (some bit)) source counter out).regs 1 = true by
          simp [ readRegs_present]) (hc.seq hp) hl
      refine ⟨rf, ?_⟩
      convert he using 1 <;>
        simp [List.length_cons, repeatCount, List.append_assoc ] <;>
        try ring
      apply congrArg (countTapes source [])
      exact (List.append_assoc source (repeatCount source counter.length) out).symm.trans
        ((congrArg (fun l => l ++ out)
          (repeatCount_append source counter.length).symm).trans
          (List.append_assoc _ _ _))

theorem countSquare_eval (regs : Fin 2 → Bool) (source : List Bool) :
    ∃ rf, Eval countSquare (7*source.length^2+14*source.length+7)
      (countState regs source [] [])
      (countState rf source [] (repeatCount source source.length)) := by
  have hi := countInit_eval regs source []
  have hp := countPop_eval (readRegs regs 0 1 none) source source []
  obtain ⟨rf, hl⟩ := countLoop_eval (readRegs regs 0 1 none) source source []
  refine ⟨rf, ?_⟩
  have he := hi.seq (hp.seq hl)
  simp only [List.append_nil] at he
  convert he using 1 <;> first | rfl | ring

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTripleBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-port primitives for dynamic Cartesian triple expansion. All loop
bounds and coefficient widths are words on stacks, not generated code. -/
namespace SubexponentialSAT.SqrtLog.RingTriple

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpQuarticRing

theorem copy_eval (d : Data) (src dst : Fin 16)
    (hsd : src ≠ dst) (hs : src ≠ 15) (hd : (15 : Fin 16) ≠ dst)
    (htmp : d.stacks 15 = []) :
    Eval (copy src dst) (7 * (d.stacks src).length + 5) d (afterCopy d src dst) :=
  .call _ (ListRegisterProgram.copy_run src dst 15 0 1 hsd hs hd
    (by decide) d.regs d.stacks htmp)

end SubexponentialSAT.SqrtLog.RingTriple

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTripleRows
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTriple

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpQuarticRing

theorem popJ_eval (regs : Fin 2 → Bool) (s : Store) :
    Eval popJ 1 (state regs s)
      (state (readRegs regs 0 1 s.jc.head?) {s with jc := s.jc.tail}) := by
  apply Eval.base
  convert StructuredProgram.Eval.atom (StructuredProgram.Atom.pop (r := 2) (s := 16) 12 0 1)
    (state regs s) using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    fin_cases i <;> simp [ StructuredProgram.Atom.instr, execInstr, state, tapes]

end SubexponentialSAT.SqrtLog.RingTriple

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTripleMatrix
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTriple

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpQuarticRing

theorem popI_eval (regs : Fin 2 → Bool) (s : Store) :
    Eval popI 1 (state regs s)
      (state (readRegs regs 0 1 s.ic.head?) {s with ic := s.ic.tail}) := by
  apply Eval.base
  convert StructuredProgram.Eval.atom (StructuredProgram.Atom.pop (r := 2) (s := 16) 11 0 1)
    (state regs s) using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    fin_cases i <;> simp [ StructuredProgram.Atom.instr, execInstr, state, tapes]

end SubexponentialSAT.SqrtLog.RingTriple

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTripleExpand
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTriple

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpQuarticRing

theorem startMatrix_eval (s : Store) (regs : Fin 2 → Bool) :
    ∃ regs', Eval startMatrix (7 * s.x.length + 7 * s.degree.length + 10)
      (state regs {s with xs := [], ic := []})
      (state regs' {s with xs := s.x, ic := s.degree}) := by
  let d := state regs {s with xs := [], ic := []}
  let a := afterCopy d 0 4
  have h1 := copy_eval d 0 4 (by decide) (by decide) (by decide) (by rfl)
  have h2 := copy_eval a 9 11 (by decide) (by decide) (by decide) (by rfl)
  have hf : afterCopy a 9 11 =
      state (afterCopy a 9 11).regs {s with xs := s.x, ic := s.degree} := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [a, d, afterCopy, copyStacks, state, tapes]
  refine ⟨(afterCopy a 9 11).regs, ?_⟩
  rw [← hf]
  convert h1.seq h2 using 1
  all_goals try with_reducible_and_instances rfl
  simp [a, d, afterCopy, copyStacks, state, tapes]
  omega

theorem popK_eval (regs : Fin 2 → Bool) (s : Store) :
    Eval popK 1 (state regs s)
      (state (readRegs regs 0 1 s.kc.head?) {s with kc := s.kc.tail}) := by
  apply Eval.base
  convert StructuredProgram.Eval.atom (StructuredProgram.Atom.pop (r := 2) (s := 16) 10 0 1)
    (state regs s) using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    fin_cases i <;> simp [ StructuredProgram.Atom.instr, execInstr, state, tapes]

end SubexponentialSAT.SqrtLog.RingTriple

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTripleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTriple

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpQuarticRing

theorem copyK_eval (s : Store) (regs : Fin 2 → Bool) :
    Eval (copy 9 10) (7 * s.degree.length + 5)
      (state regs {s with kc := []})
      (state (readRegs regs 0 1 none) {s with kc := s.degree}) := by
  have he := copy_eval (state regs {s with kc := []}) 9 10
    (by decide) (by decide) (by decide) (by rfl)
  convert he using 1
  · simp [state, tapes]
  · apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [state, tapes, copyStacks]

end SubexponentialSAT.SqrtLog.RingTriple

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanServiceBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Shared native coefficient-ring ABI. All service programs have fixed size. -/
namespace SubexponentialSAT.SqrtLog.RingScan
open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem serviceCopy_eval (s : State 8 32) (src dst : Fin 32)
    (hsd : src ≠ dst) (hs : src ≠ 31) (hd : (31 : Fin 32) ≠ dst) (ht : s.stacks 31 = []) :
    Eval (serviceCopy src dst) (7*(s.stacks src).length+5) s (serviceAfterCopy s src dst) :=
  .call _ (ListRegisterProgram.copy_run src dst 31 1 3 hsd hs hd (by decide) s.regs s.stacks ht)

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanServiceAdd
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingScan
open BitProgram StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem embed_serviceAdd (regs oldRegs : Fin 8 → Bool)
    (modulus result x y degree width zero table oldResult oldX oldY oldDegree : List Bool) :
    embedState id serviceAddPorts (serviceState oldRegs modulus oldResult oldX oldY oldDegree width zero table)
      (addState regs modulus result [] x y [] degree width) =
    serviceState regs modulus result x y degree width zero table := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id serviceAddPorts_injective
  · intro i; rfl
  · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h0 : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
    have h8 : i ≠ 8 := fun h => hi ⟨8, h.symm⟩
    have h9 : i ≠ 9 := fun h => hi ⟨9, h.symm⟩
    have h11 : i ≠ 11 := fun h => hi ⟨11, h.symm⟩
    simp [serviceState, serviceWorkState, serviceTapes, h0, h8, h9, h11]

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanServiceLifts
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingScan
open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem embed_count_service (regs : Fin 8 → Bool) (r : Fin 2 → Bool)
    (s : ServiceStore) (inner : List Bool) :
    embedState loadRegisters serviceCountPorts (serviceWorkState regs s)
      (countState r s.degree [] inner) =
    serviceWorkState (Function.update (Function.update regs 1 (r 0)) 3 (r 1))
      {s with outer := [], inner := inner} := by
  apply embedState_eq_of_ports _ _ _ _ _ loadRegisters_injective serviceCountPorts_injective
  · intro i; fin_cases i <;> simp [loadRegisters, serviceWorkState]
  · intro i hi
    have h1 : i ≠ 1 := fun h => hi ⟨0, h.symm⟩
    have h3 : i ≠ 3 := fun h => hi ⟨1, h.symm⟩
    simp [serviceWorkState, h1, h3]
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h15 : i ≠ 15 := fun h => hi ⟨1, h.symm⟩
    have h16 : i ≠ 16 := fun h => hi ⟨2, h.symm⟩
    simp [serviceWorkState, serviceTapes, h15, h16]

theorem embed_contract_service (oldRegs regs : Fin 8 → Bool)
    (s : ServiceStore) (result stream outer inner : List Bool) :
    embedState id serviceContractPorts (serviceWorkState oldRegs s)
      (contractState regs s.modulus result stream [] s.width outer inner s.zero []) =
    serviceWorkState regs {s with result := result, x := [], y := stream, degree := [], outer := outer, inner := inner} := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id serviceContractPorts_injective
  · intro i; rfl
  · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h0 : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
    have h8 : i ≠ 8 := fun h => hi ⟨8, h.symm⟩
    have h9 : i ≠ 9 := fun h => hi ⟨9, h.symm⟩
    have h11 : i ≠ 11 := fun h => hi ⟨11, h.symm⟩
    have h15 : i ≠ 15 := fun h => hi ⟨15, h.symm⟩
    have h16 : i ≠ 16 := fun h => hi ⟨16, h.symm⟩
    simp [serviceWorkState, serviceTapes, h0, h8, h9, h11, h15, h16]


end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramNativeInverse
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A standalone native inverse of a node difference. The exponent is the
residue-field cardinality minus two; the separate repair loop has length t. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram.NativeInverse
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing

def budget (t d : ℕ) : ℕ :=
  let Km := HornerProgram.Services.mulBudget (baseWidth 3 t) d
  let Ka := HornerProgram.Services.addBudget (baseWidth 3 t) d
  inverseBudget (3^d-2) t Km Ka (d*baseWidth 3 t) + Km+Ka+102*(d*baseWidth 3 t)+113

end SubexponentialSAT.SqrtLog.CRTLocalProgram.NativeInverse

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SetupPrimitives
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual fixed bit programs for the two logarithmic setup quantities.
Input and output numbers are arbitrary padded little-endian words. -/
namespace SubexponentialSAT.SqrtLog.Setup

open BitProgram StructuredCalls
open CounterPrograms (value ripple)

abbrev increment : Cmd 3 3 :=
  .call (ProgramLinking.liftProgram (CounterPrograms.rippleProgram true) id incrementPorts)

end SubexponentialSAT.SqrtLog.Setup

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

def operators (mul : Bool) (n : ℕ) : Word := (List.replicate n (operator mul)).flatten

/-! ## Fixed source-constructor control -/

/-! ## Concrete machine states and elementary traces -/

/-! The following induction rule accounts for actual executions of the fixed
payload body. Its premises will be proved for `termBody`, `groupBody`, and
`blockBody`; the exported whole-controller statement has no callback argument. -/

/-! ## Forward-output service boundary -/

end SubexponentialSAT.SubexpKernelControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PairScoreProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Aggregating the actual collision streams of all vertex pairs

The fixed program consumes framed pairs of already selected read plans.
Producing those selected plans from original plans and the remaining-index
table is a separate preparation step.  Every pair invokes the actual tuple
generator and collision machine; a final fixed unary tally produces the score.
-/

namespace SubexponentialSAT.Subexp.PairScoreProgram

open BitProgram StackRoutines StructuredCalls

def readPlan (bits : List Bool) : List ℕ :=
  ((ProgramEncoding.readRecords bits).map (fun p => p.1.map List.length)).getD []

end SubexponentialSAT.Subexp.PairScoreProgram

end OAI.Algorithms
end


