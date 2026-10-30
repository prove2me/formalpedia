-- Prove2me | Definitions.Def_OAIQ081S045
-- name    : OAIQ081S045
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:34:48.661111+00:00
-- url     : https://prove2.me/theorems/35eaed54-581d-4c2e-96d7-7457067d05ca
-- title:
--   Definitions bundle OAIQ081S045 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 58 declarations of OpenAI's Lean: 8 definitions and 50 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.ArithmeticExpressionSupport.pushWord`, `OAI.Algorithms.SubexponentialSAT.CounterForPrograms.decrementResult`, `OAI.Algorithms.SubexponentialSAT.CounterForPrograms.install`, `OAI.Algorithms.SubexponentialSAT.CounterForPrograms.nextState`, `OAI.Algorithms.SubexponentialSAT.CounterForPrograms.testResult`, `OAI.Algorithms.SubexponentialSAT.CounterForPrograms.zeroResult`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchFactorControl.clear`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairPreparationProgram.Data`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_ArithmeticCalls`, `SubexponentialSAT_ArithmeticExpressionSupport`, `SubexponentialSAT_ArrayPrograms`, `SubexponentialSAT_ArrayUpdateLifted`, `SubexponentialSAT_ArrayUpdatePrograms`, `SubexponentialSAT_BinaryPrograms`, `SubexponentialSAT_CounterForPrograms`, `SubexponentialSAT_ListRegisterProgram`, `SubexponentialSAT_SqrtLog_IrreducibleSearchNativeScan`, `SubexponentialSAT_StackRoutines`, `SubexponentialSAT_StructuredCalls`, `SubexponentialSAT_StructuredProgram`, `SubexponentialSAT_Subexp_PairPreparationProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S023`, `OAIQ081S024` and `OAIQ081S025` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S066`, `OAIQ081S067`, `OAIQ081S068`, `OAIQ081S069`, `OAIQ081S070`, `OAIQ081S071`, `OAIQ081S073`, `OAIQ081S074`, `OAIQ081S076`, `OAIQ081S077`, `OAIQ081S078`, `OAIQ081S079`, `OAIQ081S080` and `OAIQ081S081`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S023
import Definitions.Def_OAIQ081S024
import Definitions.Def_OAIQ081S025

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_StackRoutines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-alphabet stack routines

This module records stack-state transformations and proves instruction traces
for concrete programs over Boolean stacks. The number of symbols in a stack is
runtime data; no growing alphabet is used.
-/

namespace SubexponentialSAT.StackRoutines

universe u

open BitProgram

theorem clearProgram_trace {r s : ℕ} (src : Fin s) (value present : Fin r)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) :
    Trace (clearProgram src value present) (2 * (stk src).length + 2)
      ⟨some 0, regs, stk⟩ (clearResult 2 src value present regs stk) :=
  clear_trace _ src value present 0 1 2 rfl rfl regs stk

end SubexponentialSAT.StackRoutines

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_BinaryPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control programs for binary arithmetic

Operands, their widths, and moduli are data. None of the programs in this file
have a control-state set depending on an operand length or numeric parameter.
-/

namespace SubexponentialSAT.BinaryPrograms

open SubexponentialSAT.BinaryArithmetic
open SubexponentialSAT.Computation

namespace Mul

/-- One full multiplier iteration, including all copy and arithmetic work. -/
theorem round (r : Regs) (b : Bool) (xs ys acc : List Bool) :
    ∃ rf : Regs, SubexponentialSAT.BitProgram.RunsIn program
      (30 * (max acc.length ys.length + 1))
      (loopCfg r (b :: xs) ys acc)
      (loopCfg rf xs (false :: ys) (if b then add acc ys else acc)) := by
  cases b with
  | false =>
      let r' := SubexponentialSAT.BitProgram.readRegs r 1 3 (some false)
      have ht := (enter_round r false xs ys acc).trans (shift r' xs ys acc)
      refine ⟨Function.update r' 1 false, 5, by omega, ?_⟩
      exact ht
  | true =>
      let r₁ := SubexponentialSAT.BitProgram.readRegs r 1 3 (some true)
      let r₂ := SubexponentialSAT.BitProgram.readRegs r₁ 1 3 none
      let r₃ := Function.update r₂ 0 false
      have hp := (enter_round r true xs ys acc).trans (copy_block r₁ xs ys acc)
      have hp' := hp.trans (reset_carry r₂ xs ys acc)
      obtain ⟨r₄, ha⟩ := add_block r₃ xs ys acc ys [] []
      have ha' : SubexponentialSAT.BitProgram.RunsIn program (10 * (max acc.length ys.length + 1))
          (cfg (some 11) r₃ xs ys acc ys [] [])
          (cfg (some 24) r₄ xs ys [] [] [] (add acc ys).reverse) := by
        simpa [r₃, add] using ha
      let r₅ := SubexponentialSAT.BitProgram.readRegs r₄ 1 3 none
      have hq := (transfer_block r₄ xs ys (add acc ys)).trans (shift r₅ xs ys (add acc ys))
      have hpRun : SubexponentialSAT.BitProgram.RunsIn program (3 + (7 * ys.length + 4) + 1)
          (loopCfg r (true :: xs) ys acc)
          (cfg (some 11) r₃ xs ys acc ys [] []) :=
        ⟨_, le_rfl, hp'⟩
      have hqRun : SubexponentialSAT.BitProgram.RunsIn program (3 * (add acc ys).length + 2 + 2)
          (cfg (some 24) r₄ xs ys [] [] [] (add acc ys).reverse)
          (loopCfg (Function.update r₅ 1 false) xs (false :: ys) (add acc ys)) :=
        ⟨_, le_rfl, hq⟩
      refine ⟨Function.update r₅ 1 false, ?_⟩
      have ht := (hpRun.trans ha').trans hqRun
      have hlen := length_add acc ys
      exact ht.mono (by omega)

/-- The complete fixed program computes the accumulator specification.  The
bound counts every executed Boolean instruction and every stack operation. -/
theorem run (r : Regs) (xs ys acc : List Bool) (B : ℕ)
    (hys : ys.length ≤ B) (hacc : acc.length ≤ B) :
    ∃ rf : Regs, SubexponentialSAT.BitProgram.RunsIn program
      (30 * (xs.length + 1) * (B + xs.length + 1))
      (loopCfg r xs ys acc) (cfg none rf [] [] (accumulate xs ys acc) [] [] []) := by
  induction xs generalizing r ys acc B with
  | nil =>
      obtain ⟨rf, hf⟩ := finish r ys acc
      exact ⟨rf, 2 * ys.length + 5, by simp; omega, hf⟩
  | cons b xs ih =>
      obtain ⟨r', hr⟩ := round r b xs ys acc
      have hnext : (if b then add acc ys else acc).length ≤ B + 1 := by
        have ha := length_add acc ys
        cases b <;> simp <;> omega
      obtain ⟨rf, hf⟩ := ih r' (false :: ys) (if b then add acc ys else acc) (B + 1)
        (by simpa using Nat.succ_le_succ hys) hnext
      refine ⟨rf, ?_⟩
      have ht := hr.trans hf
      have hb : max acc.length ys.length ≤ B := max_le hacc hys
      have hcost : 30 * (max acc.length ys.length + 1) +
          30 * (xs.length + 1) * (B + 1 + xs.length + 1) ≤
          30 * ((b :: xs).length + 1) * (B + (b :: xs).length + 1) := by
        simp only [List.length_cons]
        nlinarith
      exact ht.mono hcost

end Mul

end SubexponentialSAT.BinaryPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_StructuredProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Structured programs compiled to finite bit instruction tables

The syntax has no unbounded natural-number registers or semantic-function
instructions. All data operations are the concrete Boolean-register and stack
instructions of BitProgram. Loops inspect a Boolean register, and changing data
never changes the finite generated instruction table.
-/

namespace SubexponentialSAT.StructuredProgram

open SubexponentialSAT.BitProgram

namespace Atom

theorem exec_instr {r s l : ℕ} (a : Atom r s) (d : State r s)
    (pc : Option (Fin l)) (next : Fin l) :
    execInstr (a.instr next) (d.withPC pc) = (a.eval d).withPC (some next) := by
  cases a <;> rfl

end Atom

/-- The compiler correctness statement is about the actual BitProgram step.
The local table-agreement premise is discharged by the whole-program compiler. -/
theorem eval_trace {r s : ℕ} {c : Cmd r s} {n : ℕ} {a b : State r s}
    (h : Eval c n a b) :
    ∀ {l : ℕ} (p : Program r s l) (embed : Site c → Fin l) (exit : Fin l),
    (∀ q, p.code (embed q) = code c embed exit q) →
    Trace p n (a.withPC (some (entry c embed exit))) (b.withPC (some exit)) := by
  induction h with
  | skip d =>
      intro l p embed exit hcode
      exact .refl _
  | atom op d =>
      intro l p embed exit hcode
      refine .cons ?_ (.refl _)
      rw [← Atom.exec_instr op d (some (entry (.atom op) embed exit)) exit]
      exact step_code p _ (embed ()) (op.instr exit) rfl (hcode ())
  | @seq first second n m a b c hf hs ihf ihs =>
      intro l p embed exit hcode
      exact (ihf p (embed ∘ Sum.inl) (entry second (embed ∘ Sum.inr) exit)
        (fun q => hcode (.inl q))).trans
        (ihs p (embed ∘ Sum.inr) exit (fun q => hcode (.inr q)))
  | @ite_true test yes no n a b ht he ih =>
      intro l p embed exit hcode
      apply SubexponentialSAT.Computation.Trace.cons _
        (ih p (fun q => embed (some (.inl q))) exit (fun q => hcode (some (.inl q))))
      simp [step, State.withPC, entry, hcode none, code, execInstr, ht]
  | @ite_false test yes no n a b ht he ih =>
      intro l p embed exit hcode
      apply SubexponentialSAT.Computation.Trace.cons _
        (ih p (fun q => embed (some (.inr q))) exit (fun q => hcode (some (.inr q))))
      simp [step, State.withPC, entry, hcode none, code, execInstr, ht]
  | @while_false test body a ht =>
      intro l p embed exit hcode
      refine .cons ?_ (.refl _)
      simp [step, State.withPC, entry, hcode none, code, execInstr, ht]
  | @while_true test body n m a b c ht hb hw ihb ihw =>
      intro l p embed exit hcode
      apply SubexponentialSAT.Computation.Trace.cons _
        ((ihb p (embed ∘ some) (embed none) (fun q => hcode (some q))).trans
          (ihw p embed exit hcode))
      simp [step, State.withPC, entry, hcode none, code, execInstr, ht]

end SubexponentialSAT.StructuredProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_StructuredCalls
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Structured invocation of existing finite bit programs

A call contains a fixed finite instruction table. Its execution premise is an
actual trace of that table, rather than a semantic or cost oracle. Compilation
relocates all its instructions and replaces each halt by a return jump. Thus
arbitrary cyclic subroutines can occur inside structured loops without manually
assigning global labels.
-/

namespace SubexponentialSAT.StructuredCalls

open SubexponentialSAT.BitProgram

/-- Exact execution preservation, proved with the concrete subroutine linker
in the call case. -/
theorem eval_trace {r s : ℕ} {c : Cmd r s} {n : ℕ} {a b : State r s}
    (h : Eval c n a b) :
    ∀ {l : ℕ} (p : Program r s l) (embed : Site c → Fin l) (exit : Fin l),
    (∀ q, p.code (embed q) = code c embed exit q) →
    Trace p n (a.withPC (some (entry c embed exit))) (b.withPC (some exit)) := by
  induction h with
  | base he =>
      intro l p embed exit hcode
      exact StructuredProgram.eval_trace he p embed exit hcode
  | @call labels routine n a b ht =>
      intro l p embed exit hcode
      have hrun := ProgramLinking.relocate_trace routine p id id embed (some exit)
        (a.withPC (some (embed routine.entry))) Function.injective_id Function.injective_id
        hcode ht
      simpa [ProgramLinking.embedCfg, ProgramLinking.relocatePc,
        StructuredProgram.State.withPC, entry] using hrun
  | @seq first second n m a b c hf hs ihf ihs =>
      intro l p embed exit hcode
      exact (ihf p (embed ∘ Sum.inl) (entry second (embed ∘ Sum.inr) exit)
        (fun q => hcode (.inl q))).trans
        (ihs p (embed ∘ Sum.inr) exit (fun q => hcode (.inr q)))
  | @ite_true test yes no n a b ht he ih =>
      intro l p embed exit hcode
      apply SubexponentialSAT.Computation.Trace.cons _
        (ih p (fun q => embed (some (.inl q))) exit (fun q => hcode (some (.inl q))))
      simp [step, StructuredProgram.State.withPC, entry, hcode none, code, execInstr, ht]
  | @ite_false test yes no n a b ht he ih =>
      intro l p embed exit hcode
      apply SubexponentialSAT.Computation.Trace.cons _
        (ih p (fun q => embed (some (.inr q))) exit (fun q => hcode (some (.inr q))))
      simp [step, StructuredProgram.State.withPC, entry, hcode none, code, execInstr, ht]
  | @while_false test body a ht =>
      intro l p embed exit hcode
      refine .cons ?_ (.refl _)
      simp [step, StructuredProgram.State.withPC, entry, hcode none, code, execInstr, ht]
  | @while_true test body n m a b c ht hb hw ihb ihw =>
      intro l p embed exit hcode
      apply SubexponentialSAT.Computation.Trace.cons _
        ((ihb p (embed ∘ some) (embed none) (fun q => hcode (some q))).trans
          (ihw p embed exit hcode))
      simp [step, StructuredProgram.State.withPC, entry, hcode none, code, execInstr, ht]

theorem compiled_trace {r s : ℕ} {c : Cmd r s} {n : ℕ} {a b : State r s}
    (h : Eval c n a b) (inputStack outputStack : Fin s) :
    Trace (compiled c inputStack outputStack) n
      (a.withPC (some (compiled c inputStack outputStack).entry))
      (b.withPC (some (exitAddress c))) :=
  eval_trace h _ _ _ (compiled_site c inputStack outputStack)

theorem compiled_halt_trace {r s : ℕ} {c : Cmd r s} {n : ℕ} {a b : State r s}
    (h : Eval c n a b) (inputStack outputStack : Fin s) :
    Trace (compiled c inputStack outputStack) (n + 1)
      (a.withPC (some (compiled c inputStack outputStack).entry)) (b.withPC none) := by
  apply (compiled_trace h inputStack outputStack).trans
  refine .cons ?_ (.refl _)
  rw [step]
  simp only [StructuredProgram.State.withPC, Option.map_some]
  rw [compiled_exit]
  rfl

theorem embedState_register {r s R S : ℕ}
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (frame : State R S) (d : State r s)
    (hinj : Function.Injective register) (i : Fin r) :
    (embedState register stack frame d).regs (register i) = d.regs i :=
  hinj.extend_apply _ _ _

theorem embedState_stack {r s R S : ℕ}
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (frame : State R S) (d : State r s)
    (hinj : Function.Injective stack) (i : Fin s) :
    (embedState register stack frame d).stacks (stack i) = d.stacks i :=
  hinj.extend_apply _ _ _

end SubexponentialSAT.StructuredCalls

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ListRegisterProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Unbounded Boolean-list registers implemented by finite programs

Logical words are Boolean stacks.  Three fixed scratch stacks suffice for
alias-safe word assignment, prefixing, and appending; all are restored empty.
The programs below contain only the existing finite Boolean/stack instructions.
Every stated cost is proved by an actual execution trace.
-/

namespace SubexponentialSAT.ListRegisterProgram

open BitProgram StackRoutines ProgramLinking

theorem clear_run {r s : ℕ} (src : Fin s) (value present : Fin r)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) :
    Run (clearProgram src value present) (2 * (stk src).length + 3)
      regs stk (readRegs regs value present none) (clearStacks src stk) := by
  have h := halt_after_trace _ (clearProgram_trace src value present regs stk) 2 rfl rfl
  simpa [Run, clearProgram, clearResult, Nat.add_assoc] using h

end SubexponentialSAT.ListRegisterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ArithmeticCalls
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Source-preserving arithmetic calls on fixed Boolean-stack ports

Operands are copied into distinct work ports before the actual finite adder or
multiplier runs. The source ports may coincide. The only final stack change is
the output word; every work port is restored to its incoming empty state.
-/

namespace SubexponentialSAT.ArithmeticCalls

open BitProgram StructuredCalls

theorem embed_mul_start {S : ℕ} (p : Ports S) (d : Data S) (hv : Valid p d) :
    embedState id (mulPorts p) d
      ⟨(mulReady p d).regs,
        BinaryPrograms.Mul.stackState (d.stacks p.left) (d.stacks p.right) [] [] [] []⟩ =
      mulReady p d := by
  apply embedState_eq_of_ports id (mulPorts p) d _ _ Function.injective_id (mulPorts_injective p)
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i
    fin_cases i <;> simp [mulReady, mulPorts, BinaryPrograms.Mul.stackState,
      p.work.injective.eq_iff, hv.1, hv.2]
  · intro i hi
    have h0 : i ≠ p.work 0 := fun h => hi ⟨0, h.symm⟩
    have h1 : i ≠ p.work 1 := fun h => hi ⟨1, h.symm⟩
    simp [mulReady, h0, h1]

theorem embed_mul_finish {S : ℕ} (p : Ports S) (d : Data S) (hv : Valid p d)
    (rf : Fin 8 → Bool) (word : List Bool) :
    embedState id (mulPorts p) d
      ⟨rf, BinaryPrograms.Mul.stackState [] [] word [] [] []⟩ =
      (⟨rf, Function.update d.stacks p.out word⟩ : Data S) := by
  apply embedState_eq_of_ports id (mulPorts p) d _ _ Function.injective_id (mulPorts_injective p)
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i
    fin_cases i <;> simp [mulPorts, BinaryPrograms.Mul.stackState, p.work_ne_out, hv.2]
  · intro i hi
    have ho : i ≠ p.out := fun h => hi ⟨2, h.symm⟩
    simp [ho]

/-- Source-preserving binary multiplication by an actual finite program.
All five work stacks are empty in the returned state, because only out changes. -/
theorem multiplyAt_eval {S : ℕ} (p : Ports S) (d : Data S) (hv : Valid p d) :
    ∃ (t : ℕ) (rf : Fin 8 → Bool) (word : List Bool),
      Eval (multiplyAt p) t d ⟨rf, Function.update d.stacks p.out word⟩ ∧
      BinaryArithmetic.toNat word =
        BinaryArithmetic.toNat (d.stacks p.left) * BinaryArithmetic.toNat (d.stacks p.right) ∧
      word.length ≤ (d.stacks p.left).length + (d.stacks p.right).length + 1 ∧
      t ≤ 100 * ((d.stacks p.left).length + (d.stacks p.right).length + 1) ^ 2 := by
  let first := afterCopy p.left (p.work 0) d
  have hleft := copyAt_eval p.left (p.work 0) (p.work 3) d
    (left_ne_work p 0) (left_ne_work p 3)
    (by simp [p.work.injective.eq_iff]) (hv.2 0) (hv.2 3)
  have hrightWord : first.stacks p.right = d.stacks p.right := by
    simp [first, afterCopy]
  have hright := copyAt_eval p.right (p.work 1) (p.work 3) first
    (right_ne_work p 1) (right_ne_work p 3)
    (by simp [p.work.injective.eq_iff])
    (by simp [first, afterCopy, p.work.injective.eq_iff, hv.2])
    (by simp [first, afterCopy, p.work.injective.eq_iff, hv.2])
  rw [hrightWord] at hright
  change Eval _ _ first
    (afterCopy p.right (p.work 1) (afterCopy p.left (p.work 0) d)) at hright
  rw [copy_mul_ready] at hright
  let word := BinaryPrograms.Mul.accumulate (d.stacks p.left) (d.stacks p.right) []
  obtain ⟨rf, t, htime, htrace⟩ := BinaryPrograms.Mul.run (mulReady p d).regs
    (d.stacks p.left) (d.stacks p.right) [] (d.stacks p.right).length le_rfl (by simp)
  have hcall := eval_call_lifted BinaryPrograms.Mul.program id (mulPorts p) d
    Function.injective_id (mulPorts_injective p)
    (a := ⟨(mulReady p d).regs,
      BinaryPrograms.Mul.stackState (d.stacks p.left) (d.stacks p.right) [] [] [] []⟩)
    (b := ⟨rf, BinaryPrograms.Mul.stackState [] [] word [] [] []⟩) htrace
  rw [embed_mul_start p d hv, embed_mul_finish p d hv] at hcall
  refine ⟨(7 * (d.stacks p.left).length + 5) +
      ((7 * (d.stacks p.right).length + 5) + t), rf, word,
    hleft.seq (hright.seq hcall), ?_, ?_, ?_⟩
  · simpa [word] using BinaryPrograms.Mul.accumulate_value
      (d.stacks p.left) (d.stacks p.right) []
  · have hlen := BinaryPrograms.Mul.accumulate_length
      (d.stacks p.left) (d.stacks p.right) []
    simp only [List.length_nil, Nat.zero_max] at hlen
    dsimp [word]
    omega
  · nlinarith

end SubexponentialSAT.ArithmeticCalls

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ArithmeticExpressionSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.ArithmeticExpressionSupport

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem clear_eval {S : ℕ} (port : Fin S) (d : Data S) :
    Eval (clearCmd port) (2 * (d.stacks port).length + 3) d
      ⟨readRegs d.regs 0 1 none, Function.update d.stacks port []⟩ := by
  apply Eval.call
  exact ListRegisterProgram.clear_run port (0 : Fin 8) 1 d.regs d.stacks

/-- The word is part of the fixed program, rather than a runtime arithmetic operation. -/
def pushWord {S : ℕ} (dst : Fin S) : List Bool → Cmd 8 S
  | [] => .base .skip
  | b :: bs => .seq (pushWord dst bs) (.seq (atom (.set 0 b)) (atom (.push dst 0)))

theorem pushWord_eval {S : ℕ} (dst : Fin S) (bits : List Bool) (d : Data S) :
    ∃ rf : Fin 8 → Bool, Eval (pushWord dst bits) (2 * bits.length) d
      ⟨rf, Function.update d.stacks dst (bits ++ d.stacks dst)⟩ := by
  induction bits generalizing d with
  | nil =>
      refine ⟨d.regs, ?_⟩
      have hs : Function.update d.stacks dst (d.stacks dst) = d.stacks :=
        Function.update_eq_self dst d.stacks
      simpa [pushWord, hs] using Eval.base (StructuredProgram.Eval.skip d)
  | cons b bs ih =>
      obtain ⟨rf, h⟩ := ih d
      let middle : Data S := ⟨rf, Function.update d.stacks dst (bs ++ d.stacks dst)⟩
      have hset := Eval.base (StructuredProgram.Eval.atom (.set (0 : Fin 8) b) middle)
      have hpush := Eval.base (StructuredProgram.Eval.atom (.push dst (0 : Fin 8))
        ((StructuredProgram.Atom.set 0 b).eval middle))
      refine ⟨Function.update rf 0 b, ?_⟩
      simpa [pushWord, atom, middle, StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
        StructuredProgram.State.withPC, execInstr, Nat.mul_add, Nat.add_assoc] using
        Eval.seq h (Eval.seq hset hpush)

/-- A compiled child call changes only the image of its output stack.
The hypothesis is a genuine execution of the concrete child command. -/
theorem call_on_block {s S : ℕ} (c : Cmd 8 s) (input output : Fin s)
    (block : Fin s ↪ Fin S) (d : Data S) (a b : Data s) (word : List Bool)
    {n : ℕ} (h : Eval c n a b) (hr : a.regs = d.regs)
    (ha : a.stacks = d.stacks ∘ block)
    (hb : b.stacks = Function.update a.stacks output word) :
    Eval (.call (ProgramLinking.liftProgram (compiled c input output) id block)) (n + 1) d
      ⟨b.regs, Function.update d.stacks (block output) word⟩ := by
  have hrun := eval_call_lifted (compiled c input output) id block d
    Function.injective_id block.injective (compiled_halt_trace h input output)
  have hstart : embedState id block d a = d := by
    apply embedState_eq_of_ports id block d d a Function.injective_id block.injective
    · intro i
      simpa using congrFun hr i |>.symm
    · intro i hi
      exact False.elim (hi ⟨i, rfl⟩)
    · intro i
      simpa using congrFun ha i |>.symm
    · intro i hi
      rfl
  have hend : embedState id block d b =
      (⟨b.regs, Function.update d.stacks (block output) word⟩ : Data S) := by
    apply embedState_eq_of_ports id block d _ b Function.injective_id block.injective
    · intro i
      rfl
    · intro i hi
      exact False.elim (hi ⟨i, rfl⟩)
    · intro i
      rw [hb, ha]
      simp only [Function.update_apply, block.injective.eq_iff, Function.comp_apply]
    · intro i hi
      have hne : i ≠ block output := by
        intro he
        exact hi ⟨output, he.symm⟩
      simp [hne]
  simpa only [hstart, hend] using hrun

end SubexponentialSAT.ArithmeticExpressionSupport

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ArrayPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Dynamic counted operations on Boolean stacks

The counter is a stack whose *length* is the requested number of bits. Its bit
values are ignored. In particular, bounds are data, not control-label counts.
-/

namespace SubexponentialSAT.ArrayPrograms

open BitProgram StackRoutines

/-- The counter controls a fixed four-instruction loop. The precondition names
the segment it will consume, and proves the source contains enough data. -/
theorem counted_transfer_trace {r s l : ℕ} (p : Program r s l)
    (counter src dst : Fin s) (value present : Fin r)
    (loop check read put exit : Fin l)
    (hcs : counter ≠ src) (hcd : counter ≠ dst) (hsd : src ≠ dst)
    (hvp : value ≠ present)
    (hloop : p.code loop = .pop counter value present check)
    (hcheck : p.code check = .branch present read exit)
    (hread : p.code read = .pop src value present put)
    (hput : p.code put = .push dst value loop)
    (segment rest countWord : List Bool) (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (hsrc : stk src = segment ++ rest) (hcounter : stk counter = countWord)
    (hcount : countWord.length = segment.length) :
    Trace p (4 * segment.length + 2) ⟨some loop, regs, stk⟩
      (countedTransferResult exit counter src dst value present segment rest regs stk) := by
  induction segment generalizing countWord regs stk with
  | nil =>
      have hc : countWord = [] := List.length_eq_zero_iff.mp (by simpa using hcount)
      subst countWord
      have hs : stk src = rest := by simpa using hsrc
      have hst : countedTransferStacks counter src dst [] rest stk =
          Function.update stk counter [] := by
        funext j
        by_cases hd : j = dst
        · subst j; simp [countedTransferStacks, hcd.symm]
        · by_cases hj : j = src
          · subst j; simp [countedTransferStacks, hs, hcs.symm, hsd]
          · simp [countedTransferStacks, hd, hj]
      refine .cons (b := ⟨some check, readRegs regs value present none,
        Function.update stk counter []⟩) ?_ ?_
      · simp [step, hloop, execInstr, hc]
      · refine .cons (b := countedTransferResult exit counter src dst value present [] rest regs stk)
          ?_ (.refl _)
        simp [step, hcheck, execInstr, countedTransferResult, hst, readRegs_present]
  | cons a segment ih =>
      cases countWord with
      | nil => simp at hcount
      | cons bit countTail =>
          have hlen : countTail.length = segment.length := by simpa using hcount
          let regs₁ := readRegs regs value present (some bit)
          let regs₂ := readRegs regs₁ value present (some a)
          let stk₁ := Function.update stk counter countTail
          let stk₂ := Function.update stk₁ src (segment ++ rest)
          let stk₃ := Function.update stk₂ dst (a :: stk dst)
          have hs' : stk₃ src = segment ++ rest := by simp [stk₃, stk₂, hsd]
          have hc' : stk₃ counter = countTail := by simp [stk₃, stk₂, stk₁, hcs, hcd]
          have ht := ih countTail regs₂ stk₃ hs' hc' hlen
          have hst := countedTransferStacks_step counter src dst a segment rest countTail stk
            hcs hcd hsd
          have ht' : Trace p (4 * segment.length + 2) ⟨some loop, regs₂, stk₃⟩
              (countedTransferResult exit counter src dst value present (a :: segment) rest regs stk) := by
            simpa only [countedTransferResult, regs₂, regs₁, readRegs_reset, stk₃, stk₂, stk₁,
              hst] using ht
          have total : Trace p (4 * segment.length + 2 + 1 + 1 + 1 + 1)
              ⟨some loop, regs, stk⟩
              (countedTransferResult exit counter src dst value present (a :: segment) rest regs stk) := by
            refine .cons (b := ⟨some check, regs₁, stk₁⟩) ?_ ?_
            · simp [step, hloop, execInstr, hcounter, regs₁, stk₁]
            · refine .cons (b := ⟨some read, regs₁, stk₁⟩) ?_ ?_
              · simp [step, hcheck, execInstr, regs₁, readRegs_present]
              · refine .cons (b := ⟨some put, regs₂, stk₂⟩) ?_ ?_
                · simp [step, hread, execInstr, regs₂, stk₂, stk₁, hcs.symm, hsrc]
                · refine .cons (b := ⟨some loop, regs₂, stk₃⟩) ?_ ht'
                  simp [step, hput, execInstr, regs₂, stk₃, stk₂, stk₁,
                    readRegs_value, hvp, hsd.symm, hcd.symm]
          simpa only [List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_assoc] using total

theorem countedTransferProgram_trace {r s : ℕ} (counter src dst : Fin s)
    (value present : Fin r) (hcs : counter ≠ src) (hcd : counter ≠ dst) (hsd : src ≠ dst)
    (hvp : value ≠ present) (segment rest countWord : List Bool)
    (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (hsrc : stk src = segment ++ rest) (hcounter : stk counter = countWord)
    (hcount : countWord.length = segment.length) :
    Trace (countedTransferProgram counter src dst value present) (4 * segment.length + 2)
      ⟨some 0, regs, stk⟩
      (countedTransferResult 4 counter src dst value present segment rest regs stk) :=
  counted_transfer_trace _ counter src dst value present 0 1 2 3 4 hcs hcd hsd hvp
    rfl rfl rfl rfl segment rest countWord regs stk hsrc hcounter hcount

/-- Skip precisely the number of data bits supplied by a unary counter,
restoring the initially empty discard buffer. -/
theorem counted_skip_trace {r s l : ℕ} (p : Program r s l)
    (counter src tmp : Fin s) (value present : Fin r)
    (loop check read put clearLoop clearCheck exit : Fin l)
    (hcs : counter ≠ src) (hct : counter ≠ tmp) (hst : src ≠ tmp) (hvp : value ≠ present)
    (h₀ : p.code loop = .pop counter value present check)
    (h₁ : p.code check = .branch present read clearLoop)
    (h₂ : p.code read = .pop src value present put)
    (h₃ : p.code put = .push tmp value loop)
    (h₄ : p.code clearLoop = .pop tmp value present clearCheck)
    (h₅ : p.code clearCheck = .branch present clearLoop exit)
    (segment rest countWord : List Bool) (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (hsrc : stk src = segment ++ rest) (hcounter : stk counter = countWord)
    (hcount : countWord.length = segment.length) (htmp : stk tmp = []) :
    Trace p (6 * segment.length + 4) ⟨some loop, regs, stk⟩
      (countedSkipResult exit counter src value present rest regs stk) := by
  have t₁ := counted_transfer_trace p counter src tmp value present loop check read put clearLoop
    hcs hct hst hvp h₀ h₁ h₂ h₃ segment rest countWord regs stk hsrc hcounter hcount
  have t₂ := clear_trace p tmp value present clearLoop clearCheck exit h₄ h₅
    (readRegs regs value present none) (countedTransferStacks counter src tmp segment rest stk)
  have hlen : (countedTransferStacks counter src tmp segment rest stk tmp).length = segment.length := by
    simp [countedTransferStacks, htmp]
  have hfinal := clear_after_countedTransfer counter src tmp segment rest stk hct hst htmp
  have t₂' : Trace p (2 * segment.length + 2)
      (countedTransferResult clearLoop counter src tmp value present segment rest regs stk)
      (countedSkipResult exit counter src value present rest regs stk) := by
    simpa only [hlen, clearResult, countedTransferResult, countedSkipResult,
      readRegs_reset, hfinal] using t₂
  have total := t₁.trans t₂'
  convert total using 1 ; omega

theorem countedSkipProgram_trace {r s : ℕ} (counter src tmp : Fin s)
    (value present : Fin r) (hcs : counter ≠ src) (hct : counter ≠ tmp) (hst : src ≠ tmp)
    (hvp : value ≠ present) (segment rest countWord : List Bool)
    (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (hsrc : stk src = segment ++ rest) (hcounter : stk counter = countWord)
    (hcount : countWord.length = segment.length) (htmp : stk tmp = []) :
    Trace (countedSkipProgram counter src tmp value present) (6 * segment.length + 4)
      ⟨some 0, regs, stk⟩ (countedSkipResult 6 counter src value present rest regs stk) :=
  counted_skip_trace _ counter src tmp value present 0 1 2 3 4 5 6 hcs hct hst hvp
    rfl rfl rfl rfl rfl rfl segment rest countWord regs stk hsrc hcounter hcount htmp

theorem fanout_after_countedTransfer {s : ℕ} (counter src dst tmp : Fin s)
    (segment rest : List Bool) (stk : Stacks (Fin s))
    (hcs : counter ≠ src) (hcd : counter ≠ dst) (hct : counter ≠ tmp)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst)
    (hsrc : stk src = segment ++ rest) (htmp : stk tmp = []) :
    fanoutStacks tmp src dst (countedTransferStacks counter src tmp segment rest stk) =
      countedCopyStacks counter dst segment stk := by
  funext j
  by_cases hd : j = dst
  · subst j
    simp [fanoutStacks, countedTransferStacks, countedCopyStacks,
      hcd.symm, hsd.symm, htd.symm, htmp]
  · by_cases hs : j = src
    · subst j
      simp [fanoutStacks, countedTransferStacks, countedCopyStacks,
        hsd, hst, hcs.symm, htmp, hsrc]
    · by_cases ht : j = tmp
      · subst j
        simp [fanoutStacks, countedTransferStacks, countedCopyStacks, hst, htd,
          hct.symm, hst.symm, htmp]
      · by_cases hc : j = counter
        · subst j
          simp [fanoutStacks, countedTransferStacks, countedCopyStacks, hcs, hcd, hct]
        · simp [fanoutStacks, countedTransferStacks, countedCopyStacks, hd, hs, ht, hc]

/-- Counted preserving copy. Only the unary counter and destination change in
the final state; the source and temporary buffer are restored exactly. -/
theorem counted_copy_trace {r s l : ℕ} (p : Program r s l)
    (counter src dst tmp : Fin s) (value present : Fin r)
    (loop check read put copyLoop copyCheck copyPut₁ copyPut₂ exit : Fin l)
    (hcs : counter ≠ src) (hcd : counter ≠ dst) (hct : counter ≠ tmp)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst) (hvp : value ≠ present)
    (h₀ : p.code loop = .pop counter value present check)
    (h₁ : p.code check = .branch present read copyLoop)
    (h₂ : p.code read = .pop src value present put)
    (h₃ : p.code put = .push tmp value loop)
    (h₄ : p.code copyLoop = .pop tmp value present copyCheck)
    (h₅ : p.code copyCheck = .branch present copyPut₁ exit)
    (h₆ : p.code copyPut₁ = .push src value copyPut₂)
    (h₇ : p.code copyPut₂ = .push dst value copyLoop)
    (segment rest countWord : List Bool) (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (hsrc : stk src = segment ++ rest) (hcounter : stk counter = countWord)
    (hcount : countWord.length = segment.length) (htmp : stk tmp = []) :
    Trace p (8 * segment.length + 4) ⟨some loop, regs, stk⟩
      (countedCopyResult exit counter dst value present segment regs stk) := by
  have t₁ := counted_transfer_trace p counter src tmp value present loop check read put copyLoop
    hcs hct hst hvp h₀ h₁ h₂ h₃ segment rest countWord regs stk hsrc hcounter hcount
  have t₂ := fanout_trace p tmp src dst value present copyLoop copyCheck copyPut₁ copyPut₂ exit
    hst.symm htd hsd hvp h₄ h₅ h₆ h₇ (readRegs regs value present none)
    (countedTransferStacks counter src tmp segment rest stk)
  have hlen : (countedTransferStacks counter src tmp segment rest stk tmp).length = segment.length := by
    simp [countedTransferStacks, htmp]
  have hfinal := fanout_after_countedTransfer counter src dst tmp segment rest stk
    hcs hcd hct hsd hst htd hsrc htmp
  have t₂' : Trace p (4 * segment.length + 2)
      (countedTransferResult copyLoop counter src tmp value present segment rest regs stk)
      (countedCopyResult exit counter dst value present segment regs stk) := by
    simpa only [hlen, fanoutResult, countedTransferResult, countedCopyResult,
      readRegs_reset, hfinal] using t₂
  have total := t₁.trans t₂'
  convert total using 1 ; omega

theorem countedCopyProgram_trace {r s : ℕ} (counter src dst tmp : Fin s)
    (value present : Fin r) (hcs : counter ≠ src) (hcd : counter ≠ dst) (hct : counter ≠ tmp)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst) (hvp : value ≠ present)
    (segment rest countWord : List Bool) (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (hsrc : stk src = segment ++ rest) (hcounter : stk counter = countWord)
    (hcount : countWord.length = segment.length) (htmp : stk tmp = []) :
    Trace (countedCopyProgram counter src dst tmp value present) (8 * segment.length + 4)
      ⟨some 0, regs, stk⟩ (countedCopyResult 8 counter dst value present segment regs stk) :=
  counted_copy_trace _ counter src dst tmp value present 0 1 2 3 4 5 6 7 8
    hcs hcd hct hsd hst htd hvp rfl rfl rfl rfl rfl rfl rfl rfl
    segment rest countWord regs stk hsrc hcounter hcount htmp

/-! ## Indexed fixed-width records

The seven stacks are: source 0, output 1, unary index 2, unary width 3,
temporary counter 4, copy scratch 5, and data scratch 6. Their contents can be
arbitrarily long. The program always has exactly 31 control labels.
-/

end SubexponentialSAT.ArrayPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ArrayUpdatePrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Preserving access and update of packed arrays

The instruction tables have eight Boolean stacks. The record index and width
are unary stack data, so neither value affects the finite program control.
Stack 7 saves the preceding records in reverse order and restores them after
the selected record is read or replaced.
-/

namespace SubexponentialSAT.ArrayUpdatePrograms

open BitProgram StackRoutines ArrayPrograms StructuredCalls

theorem copy_eval {r s : ℕ} (src dst tmp : Fin s) (value present : Fin r)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst) (hvp : value ≠ present)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) (ht : stk tmp = []) :
    Eval (.call (copyProgram src dst tmp value present)) (7 * (stk src).length + 5)
      ⟨regs, stk⟩ ⟨readRegs regs value present none, copyStacks src dst stk⟩ := by
  apply Eval.call
  have t := halt_after_trace _
    (copyProgram_trace src dst tmp value present hsd hst htd hvp regs stk ht) 7 rfl rfl
  simpa [StructuredProgram.State.withPC, copyResult, copyProgram, Nat.add_assoc] using t

theorem transfer_eval {r s : ℕ} (src dst : Fin s) (value present : Fin r)
    (hsd : src ≠ dst) (hvp : value ≠ present)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) :
    Eval (.call (transferProgram src dst value present)) (3 * (stk src).length + 3)
      ⟨regs, stk⟩ ⟨readRegs regs value present none, transferStacks src dst stk⟩ := by
  apply Eval.call
  have t := halt_after_trace _
    (transferProgram_trace src dst value present hsd hvp regs stk) 3 rfl rfl
  simpa [StructuredProgram.State.withPC, transferResult, transferProgram, Nat.add_assoc] using t

theorem countedTransfer_eval {r s : ℕ} (counter src dst : Fin s)
    (value present : Fin r) (hcs : counter ≠ src) (hcd : counter ≠ dst)
    (hsd : src ≠ dst) (hvp : value ≠ present)
    (segment rest countWord : List Bool) (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (hs : stk src = segment ++ rest) (hc : stk counter = countWord)
    (hlen : countWord.length = segment.length) :
    Eval (.call (countedTransferProgram counter src dst value present))
      (4 * segment.length + 3) ⟨regs, stk⟩
      ⟨readRegs regs value present none, countedTransferStacks counter src dst segment rest stk⟩ := by
  apply Eval.call
  have t := halt_after_trace _ (countedTransferProgram_trace counter src dst value present
    hcs hcd hsd hvp segment rest countWord regs stk hs hc hlen) 4 rfl rfl
  simpa [StructuredProgram.State.withPC, countedTransferResult, countedTransferProgram,
    Nat.add_assoc] using t

theorem countedCopy_eval {r s : ℕ} (counter src dst tmp : Fin s)
    (value present : Fin r) (hcs : counter ≠ src) (hcd : counter ≠ dst)
    (hct : counter ≠ tmp) (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst)
    (hvp : value ≠ present) (segment rest countWord : List Bool)
    (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (hs : stk src = segment ++ rest) (hc : stk counter = countWord)
    (hlen : countWord.length = segment.length) (ht : stk tmp = []) :
    Eval (.call (countedCopyProgram counter src dst tmp value present))
      (8 * segment.length + 5) ⟨regs, stk⟩
      ⟨readRegs regs value present none, countedCopyStacks counter dst segment stk⟩ := by
  apply Eval.call
  have t := halt_after_trace _ (countedCopyProgram_trace counter src dst tmp value present
    hcs hcd hct hsd hst htd hvp segment rest countWord regs stk hs hc hlen ht) 8 rfl rfl
  simpa [StructuredProgram.State.withPC, countedCopyResult, countedCopyProgram,
    Nat.add_assoc] using t

theorem countedSkip_eval {r s : ℕ} (counter src tmp : Fin s)
    (value present : Fin r) (hcs : counter ≠ src) (hct : counter ≠ tmp)
    (hst : src ≠ tmp) (hvp : value ≠ present)
    (segment rest countWord : List Bool) (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (hs : stk src = segment ++ rest) (hc : stk counter = countWord)
    (hlen : countWord.length = segment.length) (ht : stk tmp = []) :
    Eval (.call (countedSkipProgram counter src tmp value present))
      (6 * segment.length + 5) ⟨regs, stk⟩
      ⟨readRegs regs value present none, countedSkipStacks counter src rest stk⟩ := by
  apply Eval.call
  have t := halt_after_trace _ (countedSkipProgram_trace counter src tmp value present
    hcs hct hst hvp segment rest countWord regs stk hs hc hlen ht) 6 rfl rfl
  simpa [StructuredProgram.State.withPC, countedSkipResult, countedSkipProgram,
    Nat.add_assoc] using t

theorem saveRecord_eval {r : ℕ} (value present : Fin r) (hvp : value ≠ present)
    (record rest widthWord : List Bool) (regs : Fin r → Bool) (stk : Stacks (Fin 8))
    (hs : stk 0 = record ++ rest) (hw : stk 3 = widthWord)
    (hlen : record.length = widthWord.length) (hc : stk 4 = []) (ht : stk 5 = []) :
    Eval (saveRecordCmd value present) (11 * widthWord.length + 8)
      ⟨regs, stk⟩ ⟨readRegs regs value present none, savedRecordStacks record rest stk⟩ := by
  have a := copy_eval (3 : Fin 8) 4 5 value present (by decide) (by decide) (by decide)
    hvp regs stk ht
  have b := countedTransfer_eval (4 : Fin 8) 0 7 value present
    (by decide) (by decide) (by decide) hvp record rest widthWord
    (readRegs regs value present none) (copyStacks 3 4 stk)
    (by simpa [copyStacks] using hs) (by simp [copyStacks, hw, hc]) hlen.symm
  have hfinal : countedTransferStacks 4 0 7 record rest (copyStacks 3 4 stk) =
      savedRecordStacks record rest stk := by
    funext j
    fin_cases j <;> simp [countedTransferStacks, copyStacks, savedRecordStacks, hc]
  have t := a.seq b
  dsimp [saveRecordCmd]
  convert t using 1 <;> simp [hw, hlen, readRegs_reset, hfinal] ; omega

theorem readIndex_eval {r : ℕ} (value present : Fin r) (regs : Fin r → Bool)
    (stk : Stacks (Fin 8)) :
    Eval (readIndexCmd value present) 1 ⟨regs, stk⟩ (afterIndexRead value present regs stk) := by
  exact .base (.atom _ _)

theorem saveBeforeLoop_eval {r : ℕ} (value present : Fin r) (hvp : value ≠ present)
    (earlier : List (List Bool)) (rest widthWord indexWord : List Bool)
    (regs : Fin r → Bool) (stk : Stacks (Fin 8))
    (hs : stk 0 = earlier.flatten ++ rest) (hw : stk 3 = widthWord)
    (hi : stk 2 = indexWord) (hiLen : indexWord.length = earlier.length)
    (hrows : ∀ row ∈ earlier, row.length = widthWord.length)
    (hc : stk 4 = []) (ht : stk 5 = []) :
    Eval (saveBeforeLoop value present) (earlier.length * (11 * widthWord.length + 10) + 1)
      (afterIndexRead value present regs stk)
      ⟨readRegs regs value present none, savedBeforeStacks earlier rest stk⟩ := by
  induction earlier generalizing indexWord regs stk with
  | nil =>
      have hi0 : indexWord = [] := List.length_eq_zero_iff.mp (by simpa using hiLen)
      have hnil : stk 2 = [] := hi.trans hi0
      have hst : savedBeforeStacks [] rest stk = Function.update stk 2 [] := by
        funext j
        fin_cases j <;> simp_all [savedBeforeStacks]
      simpa [saveBeforeLoop, afterIndexRead, hnil, hst] using
        (Eval.while_false (test := present)
          (body := .seq (saveRecordCmd value present) (readIndexCmd value present))
          (a := afterIndexRead value present regs stk)
          (by simp [afterIndexRead, hnil, readRegs_present]))
  | cons row earlier ih =>
      cases indexWord with
      | nil => simp at hiLen
      | cons bit indexTail =>
          have hrow : row.length = widthWord.length := hrows row (by simp)
          have htail : ∀ x ∈ earlier, x.length = widthWord.length := by
            intro x hx
            exact hrows x (by simp [hx])
          let regs₁ := readRegs regs value present (some bit)
          let regs₂ := readRegs regs₁ value present none
          let stk₁ := Function.update stk 2 indexTail
          let stk₂ := savedRecordStacks row (earlier.flatten ++ rest) stk₁
          have a := saveRecord_eval value present hvp row (earlier.flatten ++ rest) widthWord
            regs₁ stk₁ (by simpa [stk₁, List.flatten_cons, List.append_assoc] using hs)
            (by simpa [stk₁] using hw) hrow (by simpa [stk₁] using hc)
            (by simpa [stk₁] using ht)
          have b := readIndex_eval value present regs₂ stk₂
          have c := ih indexTail regs₂ stk₂
            (by simp [stk₂, savedRecordStacks])
            (by simpa [stk₂, stk₁, savedRecordStacks] using hw)
            (by simp [stk₂, stk₁, savedRecordStacks]) (by simpa using hiLen) htail
            (by simpa [stk₂, stk₁, savedRecordStacks] using hc)
            (by simpa [stk₂, stk₁, savedRecordStacks] using ht)
          have loop := Eval.while_true (test := present)
            (by simp [regs₁, readRegs_present]) (a.seq b) c
          have hfinal := savedBeforeStacks_cons row earlier rest indexTail stk
          dsimp [saveBeforeLoop]
          convert loop using 1 <;>
            simp [afterIndexRead, hi, stk₁, stk₂, regs₁, regs₂, readRegs_reset,
              hfinal ] ; ring

theorem saveBefore_eval {r : ℕ} (value present : Fin r) (hvp : value ≠ present)
    (earlier : List (List Bool)) (rest widthWord indexWord : List Bool)
    (regs : Fin r → Bool) (stk : Stacks (Fin 8))
    (hs : stk 0 = earlier.flatten ++ rest) (hw : stk 3 = widthWord)
    (hi : stk 2 = indexWord) (hiLen : indexWord.length = earlier.length)
    (hrows : ∀ row ∈ earlier, row.length = widthWord.length)
    (hc : stk 4 = []) (ht : stk 5 = []) :
    Eval (saveBeforeCmd value present) (earlier.length * (11 * widthWord.length + 10) + 2)
      ⟨regs, stk⟩ ⟨readRegs regs value present none, savedBeforeStacks earlier rest stk⟩ := by
  have t := (readIndex_eval value present regs stk).seq
    (saveBeforeLoop_eval value present hvp earlier rest widthWord indexWord regs stk
      hs hw hi hiLen hrows hc ht)
  convert t using 1
  all_goals try with_reducible_and_instances rfl
  omega

theorem readSelected_eval {r : ℕ} (value present : Fin r) (hvp : value ≠ present)
    (record rest widthWord : List Bool) (regs : Fin r → Bool) (stk : Stacks (Fin 8))
    (hs : stk 0 = record ++ rest) (hw : stk 3 = widthWord)
    (hlen : record.length = widthWord.length)
    (hc : stk 4 = []) (ht : stk 5 = []) (hb : stk 6 = []) :
    Eval (readSelectedCmd value present) (15 * widthWord.length + 10)
      ⟨regs, stk⟩
      ⟨readRegs regs value present none, Function.update stk 1 (record ++ stk 1)⟩ := by
  have a := copy_eval (3 : Fin 8) 4 5 value present (by decide) (by decide) (by decide)
    hvp regs stk ht
  have b := countedCopy_eval (4 : Fin 8) 0 1 6 value present
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hvp
    record rest widthWord (readRegs regs value present none) (copyStacks 3 4 stk)
    (by simpa [copyStacks] using hs) (by simp [copyStacks, hw, hc]) hlen.symm
    (by simpa [copyStacks] using hb)
  have hfinal : countedCopyStacks 4 1 record (copyStacks 3 4 stk) =
      Function.update stk 1 (record ++ stk 1) := by
    funext j
    fin_cases j <;> simp [countedCopyStacks, copyStacks, hc]
  have t := a.seq b
  dsimp [readSelectedCmd]
  convert t using 1 <;> simp [hw, hlen, readRegs_reset, hfinal] ; omega

theorem replaceSelected_eval {r : ℕ} (value present : Fin r) (hvp : value ≠ present)
    (record replacement rest widthWord : List Bool)
    (regs : Fin r → Bool) (stk : Stacks (Fin 8))
    (hs : stk 0 = record ++ rest) (hn : stk 1 = replacement) (hw : stk 3 = widthWord)
    (hlen : record.length = widthWord.length) (hnew : replacement.length = widthWord.length)
    (hc : stk 4 = []) (ht : stk 5 = []) (hb : stk 6 = []) :
    Eval (replaceSelectedCmd value present) (20 * widthWord.length + 15)
      ⟨regs, stk⟩
      ⟨readRegs regs value present none, Function.update stk 0 (replacement ++ rest)⟩ := by
  have a := copy_eval (3 : Fin 8) 4 5 value present (by decide) (by decide) (by decide)
    hvp regs stk ht
  have b := countedSkip_eval (4 : Fin 8) 0 6 value present
    (by decide) (by decide) (by decide) hvp record rest widthWord
    (readRegs regs value present none) (copyStacks 3 4 stk)
    (by simpa [copyStacks] using hs) (by simp [copyStacks, hw, hc]) hlen.symm
    (by simpa [copyStacks] using hb)
  have c := copy_eval (1 : Fin 8) 0 6 value present (by decide) (by decide) (by decide)
    hvp (readRegs (readRegs regs value present none) value present none)
    (countedSkipStacks 4 0 rest (copyStacks 3 4 stk))
    (by simpa [countedSkipStacks, copyStacks] using hb)
  have hfinal : copyStacks 1 0 (countedSkipStacks 4 0 rest (copyStacks 3 4 stk)) =
      Function.update stk 0 (replacement ++ rest) := by
    funext j
    fin_cases j <;> simp [countedSkipStacks, copyStacks, hc, hn]
  have t := a.seq (b.seq c)
  simp only [readRegs_reset, hfinal] at t
  dsimp [replaceSelectedCmd]
  convert t using 1 ;
    simp [hw, hlen, hnew, hn, countedSkipStacks, copyStacks] ; omega

theorem read_eval {r : ℕ} (value present : Fin r) (hvp : value ≠ present)
    (earlier : List (List Bool)) (record rest widthWord indexWord : List Bool)
    (regs : Fin r → Bool) (stk : Stacks (Fin 8))
    (hs : stk 0 = earlier.flatten ++ (record ++ rest)) (hw : stk 3 = widthWord)
    (hi : stk 2 = indexWord) (hiLen : indexWord.length = earlier.length)
    (hrows : ∀ row ∈ earlier, row.length = widthWord.length)
    (hlen : record.length = widthWord.length)
    (hc : stk 4 = []) (ht : stk 5 = []) (hb : stk 6 = []) (hp : stk 7 = []) :
    Eval (readCmd value present)
      (earlier.length * (14 * widthWord.length + 10) + 15 * widthWord.length + 15)
      ⟨regs, stk⟩ ⟨readRegs regs value present none, readStacks record stk⟩ := by
  have a := saveBefore_eval value present hvp earlier (record ++ rest) widthWord indexWord
    regs stk hs hw hi hiLen hrows hc ht
  have b := readSelected_eval value present hvp record rest widthWord
    (readRegs regs value present none) (savedBeforeStacks earlier (record ++ rest) stk)
    (by simp [savedBeforeStacks]) (by simpa [savedBeforeStacks] using hw) hlen
    (by simpa [savedBeforeStacks] using hc) (by simpa [savedBeforeStacks] using ht)
    (by simpa [savedBeforeStacks] using hb)
  have c := transfer_eval (7 : Fin 8) 0 value present (by decide) hvp
    (readRegs (readRegs regs value present none) value present none)
    (Function.update (savedBeforeStacks earlier (record ++ rest) stk) 1
      (record ++ savedBeforeStacks earlier (record ++ rest) stk 1))
  have hfinal : transferStacks 7 0
      (Function.update (savedBeforeStacks earlier (record ++ rest) stk) 1
        (record ++ savedBeforeStacks earlier (record ++ rest) stk 1)) =
      readStacks record stk := by
    funext j
    fin_cases j <;> simp [transferStacks, savedBeforeStacks, readStacks, hp, hs]
  have hf := uniform_flatten_length earlier widthWord.length hrows
  have t := a.seq (b.seq c)
  simp only [readRegs_reset, hfinal] at t
  dsimp [readCmd]
  convert t using 1 ;
    simp [savedBeforeStacks, hp, hf] ; ring

theorem replace_eval {r : ℕ} (value present : Fin r) (hvp : value ≠ present)
    (earlier : List (List Bool)) (record replacement rest widthWord indexWord : List Bool)
    (regs : Fin r → Bool) (stk : Stacks (Fin 8))
    (hs : stk 0 = earlier.flatten ++ (record ++ rest)) (hn : stk 1 = replacement)
    (hw : stk 3 = widthWord) (hi : stk 2 = indexWord) (hiLen : indexWord.length = earlier.length)
    (hrows : ∀ row ∈ earlier, row.length = widthWord.length)
    (hlen : record.length = widthWord.length) (hnew : replacement.length = widthWord.length)
    (hc : stk 4 = []) (ht : stk 5 = []) (hb : stk 6 = []) (hp : stk 7 = []) :
    Eval (replaceCmd value present)
      (earlier.length * (14 * widthWord.length + 10) + 20 * widthWord.length + 20)
      ⟨regs, stk⟩ ⟨readRegs regs value present none, replaceStacks earlier replacement rest stk⟩ := by
  have a := saveBefore_eval value present hvp earlier (record ++ rest) widthWord indexWord
    regs stk hs hw hi hiLen hrows hc ht
  have b := replaceSelected_eval value present hvp record replacement rest widthWord
    (readRegs regs value present none) (savedBeforeStacks earlier (record ++ rest) stk)
    (by simp [savedBeforeStacks]) (by simpa [savedBeforeStacks] using hn)
    (by simpa [savedBeforeStacks] using hw) hlen hnew
    (by simpa [savedBeforeStacks] using hc) (by simpa [savedBeforeStacks] using ht)
    (by simpa [savedBeforeStacks] using hb)
  have c := transfer_eval (7 : Fin 8) 0 value present (by decide) hvp
    (readRegs (readRegs regs value present none) value present none)
    (Function.update (savedBeforeStacks earlier (record ++ rest) stk) 0 (replacement ++ rest))
  have hfinal : transferStacks 7 0
      (Function.update (savedBeforeStacks earlier (record ++ rest) stk) 0 (replacement ++ rest)) =
      replaceStacks earlier replacement rest stk := by
    funext j
    fin_cases j <;> simp [transferStacks, savedBeforeStacks, replaceStacks, hp]
  have hf := uniform_flatten_length earlier widthWord.length hrows
  have t := a.seq (b.seq c)
  simp only [readRegs_reset, hfinal] at t
  dsimp [replaceCmd]
  convert t using 1 ;
    simp [savedBeforeStacks, hp, hf] ; ring

/-- Complete execution, including the final halt. -/
theorem readProgram_trace {r : ℕ} (value present : Fin r) (hvp : value ≠ present)
    (earlier : List (List Bool)) (record rest widthWord indexWord : List Bool)
    (regs : Fin r → Bool) (stk : Stacks (Fin 8))
    (hs : stk 0 = earlier.flatten ++ (record ++ rest)) (hw : stk 3 = widthWord)
    (hi : stk 2 = indexWord) (hiLen : indexWord.length = earlier.length)
    (hrows : ∀ row ∈ earlier, row.length = widthWord.length)
    (hlen : record.length = widthWord.length)
    (hc : stk 4 = []) (ht : stk 5 = []) (hb : stk 6 = []) (hp : stk 7 = []) :
    @Trace r 8 (size (readCmd value present) + 1) (readProgram value present)
      (earlier.length * (14 * widthWord.length + 10) + 15 * widthWord.length + 16)
      ⟨some (readProgram value present).entry, regs, stk⟩
      ⟨none, readRegs regs value present none, readStacks record stk⟩ := by
  have h := compiled_halt_trace
    (read_eval value present hvp earlier record rest widthWord indexWord regs stk
      hs hw hi hiLen hrows hlen hc ht hb hp) 0 1
  have hp' : compiled (readCmd value present) 0 1 = readProgram value present := by rfl
  rw [hp'] at h
  simpa [StructuredProgram.State.withPC, Nat.add_assoc] using h

/-- Complete execution replaces exactly one record and preserves its source word. -/
theorem replaceProgram_trace {r : ℕ} (value present : Fin r) (hvp : value ≠ present)
    (earlier : List (List Bool)) (record replacement rest widthWord indexWord : List Bool)
    (regs : Fin r → Bool) (stk : Stacks (Fin 8))
    (hs : stk 0 = earlier.flatten ++ (record ++ rest)) (hn : stk 1 = replacement)
    (hw : stk 3 = widthWord) (hi : stk 2 = indexWord) (hiLen : indexWord.length = earlier.length)
    (hrows : ∀ row ∈ earlier, row.length = widthWord.length)
    (hlen : record.length = widthWord.length) (hnew : replacement.length = widthWord.length)
    (hc : stk 4 = []) (ht : stk 5 = []) (hb : stk 6 = []) (hp : stk 7 = []) :
    @Trace r 8 (size (replaceCmd value present) + 1) (replaceProgram value present)
      (earlier.length * (14 * widthWord.length + 10) + 20 * widthWord.length + 21)
      ⟨some (replaceProgram value present).entry, regs, stk⟩
      ⟨none, readRegs regs value present none, replaceStacks earlier replacement rest stk⟩ := by
  have h := compiled_halt_trace
    (replace_eval value present hvp earlier record replacement rest widthWord indexWord regs stk
      hs hn hw hi hiLen hrows hlen hnew hc ht hb hp) 0 0
  have hp' : compiled (replaceCmd value present) 0 0 = replaceProgram value present := by rfl
  rw [hp'] at h
  simpa [StructuredProgram.State.withPC, Nat.add_assoc] using h

end SubexponentialSAT.ArrayUpdatePrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ArrayUpdateLifted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Caller-state interfaces for the persistent packed-array routines. -/

namespace SubexponentialSAT.ArrayUpdateLifted

open BitProgram StackRoutines StructuredCalls ArrayUpdatePrograms

theorem readProgramAt_trace {r s : ℕ} (ports : Fin 8 ↪ Fin s) (value present : Fin r)
    (hvp : value ≠ present) (earlier : List (List Bool))
    (record rest widthWord indexWord : List Bool) (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (hs : stk (ports 0) = earlier.flatten ++ (record ++ rest))
    (hw : stk (ports 3) = widthWord) (hi : stk (ports 2) = indexWord)
    (hiLen : indexWord.length = earlier.length)
    (hrows : ∀ row ∈ earlier, row.length = widthWord.length)
    (hlen : record.length = widthWord.length)
    (hc : stk (ports 4) = []) (ht : stk (ports 5) = [])
    (hb : stk (ports 6) = []) (hp : stk (ports 7) = []) :
    Trace (readProgramAt ports value present)
      (earlier.length * (14 * widthWord.length + 10) + 15 * widthWord.length + 16)
      ⟨some (readProgramAt ports value present).entry, regs, stk⟩
      ⟨none, readRegs regs value present none, readStacksAt ports record stk⟩ := by
  have trace := readProgram_trace value present hvp earlier record rest widthWord indexWord
    regs (fun i => stk (ports i)) hs hw hi hiLen hrows hlen hc ht hb hp
  have lifted := ProgramLinking.liftProgram_trace (readProgram value present) id ports
    (⟨none, regs, stk⟩ : Cfg r s 38) Function.injective_id ports.injective trace
  simpa [readProgramAt, ProgramLinking.embedCfg, ProgramLinking.relocatePc,
    ProgramLinking.liftProgram, extend_read, extend_restrict] using lifted

theorem replaceProgramAt_trace {r s : ℕ} (ports : Fin 8 ↪ Fin s) (value present : Fin r)
    (hvp : value ≠ present) (earlier : List (List Bool))
    (record replacement rest widthWord indexWord : List Bool)
    (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (hs : stk (ports 0) = earlier.flatten ++ (record ++ rest))
    (hn : stk (ports 1) = replacement) (hw : stk (ports 3) = widthWord)
    (hi : stk (ports 2) = indexWord) (hiLen : indexWord.length = earlier.length)
    (hrows : ∀ row ∈ earlier, row.length = widthWord.length)
    (hlen : record.length = widthWord.length) (hnew : replacement.length = widthWord.length)
    (hc : stk (ports 4) = []) (ht : stk (ports 5) = [])
    (hb : stk (ports 6) = []) (hp : stk (ports 7) = []) :
    Trace (replaceProgramAt ports value present)
      (earlier.length * (14 * widthWord.length + 10) + 20 * widthWord.length + 21)
      ⟨some (replaceProgramAt ports value present).entry, regs, stk⟩
      ⟨none, readRegs regs value present none, replaceStacksAt ports earlier replacement rest stk⟩ := by
  have trace := replaceProgram_trace value present hvp earlier record replacement rest widthWord
    indexWord regs (fun i => stk (ports i)) hs hn hw hi hiLen hrows hlen hnew hc ht hb hp
  have lifted := ProgramLinking.liftProgram_trace (replaceProgram value present) id ports
    (⟨none, regs, stk⟩ : Cfg r s 44) Function.injective_id ports.injective trace
  simpa [replaceProgramAt, ProgramLinking.embedCfg, ProgramLinking.relocatePc,
    ProgramLinking.liftProgram, extend_replace, extend_restrict] using lifted

theorem readProgramAt_eval {r s : ℕ} (ports : Fin 8 ↪ Fin s) (value present : Fin r)
    (hvp : value ≠ present) (earlier : List (List Bool))
    (record rest widthWord indexWord : List Bool) (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (hs : stk (ports 0) = earlier.flatten ++ (record ++ rest))
    (hw : stk (ports 3) = widthWord) (hi : stk (ports 2) = indexWord)
    (hiLen : indexWord.length = earlier.length)
    (hrows : ∀ row ∈ earlier, row.length = widthWord.length)
    (hlen : record.length = widthWord.length)
    (hc : stk (ports 4) = []) (ht : stk (ports 5) = [])
    (hb : stk (ports 6) = []) (hp : stk (ports 7) = []) :
    Eval (.call (readProgramAt ports value present))
      (earlier.length * (14 * widthWord.length + 10) + 15 * widthWord.length + 16)
      ⟨regs, stk⟩ ⟨readRegs regs value present none, readStacksAt ports record stk⟩ :=
  .call _ (readProgramAt_trace ports value present hvp earlier record rest widthWord indexWord
    regs stk hs hw hi hiLen hrows hlen hc ht hb hp)

theorem replaceProgramAt_eval {r s : ℕ} (ports : Fin 8 ↪ Fin s) (value present : Fin r)
    (hvp : value ≠ present) (earlier : List (List Bool))
    (record replacement rest widthWord indexWord : List Bool)
    (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (hs : stk (ports 0) = earlier.flatten ++ (record ++ rest))
    (hn : stk (ports 1) = replacement) (hw : stk (ports 3) = widthWord)
    (hi : stk (ports 2) = indexWord) (hiLen : indexWord.length = earlier.length)
    (hrows : ∀ row ∈ earlier, row.length = widthWord.length)
    (hlen : record.length = widthWord.length) (hnew : replacement.length = widthWord.length)
    (hc : stk (ports 4) = []) (ht : stk (ports 5) = [])
    (hb : stk (ports 6) = []) (hp : stk (ports 7) = []) :
    Eval (.call (replaceProgramAt ports value present))
      (earlier.length * (14 * widthWord.length + 10) + 20 * widthWord.length + 21)
      ⟨regs, stk⟩ ⟨readRegs regs value present none, replaceStacksAt ports earlier replacement rest stk⟩ :=
  .call _ (replaceProgramAt_trace ports value present hvp earlier record replacement rest widthWord
    indexWord regs stk hs hn hw hi hiLen hrows hlen hnew hc ht hb hp)

end SubexponentialSAT.ArrayUpdateLifted

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_CounterForPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A finite binary-counted callback loop

The loop bound lives on a little-endian Boolean stack.  Fixed finite subroutines
perform zero testing and decrement, and an arbitrary fixed command is the loop
body.  The body may overwrite every register.  All measured evaluations below
compile to traces of a finite instruction table; proof-level state embeddings
are never used as executable instructions.
-/

namespace SubexponentialSAT.CounterForPrograms

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram SubexponentialSAT.CounterPrograms

variable {R S : ℕ}

noncomputable def install (p : Ports R S) (d : Data R S)
    (b present flag : Bool) (xs ys : List Bool) : Data R S :=
  StructuredCalls.embedState p.register (stackPorts p) d (localData b present flag xs ys)

theorem install_self (p : Ports R S) (d : Data R S) :
    install p d (d.regs (p.register 0)) (d.regs (p.register 1))
      (d.regs (p.register 2)) (d.stacks p.counter) (d.stacks p.scratch) = d := by
  apply data_ext
  · change Function.extend p.register
      (counterRegs (d.regs (p.register 0)) (d.regs (p.register 1))
        (d.regs (p.register 2))) d.regs = d.regs
    have h : counterRegs (d.regs (p.register 0)) (d.regs (p.register 1))
        (d.regs (p.register 2)) = d.regs ∘ p.register := by
      first | done | (funext i; fin_cases i <;> rfl)
    rw [h, extend_restrict]
  · change Function.extend (stackPorts p)
      (counterStacks (d.stacks p.counter) (d.stacks p.scratch)) d.stacks = d.stacks
    have h : counterStacks (d.stacks p.counter) (d.stacks p.scratch) =
        d.stacks ∘ stackPorts p := by
      first | done | (funext i; fin_cases i <;> rfl)
    rw [h, extend_restrict]

@[simp] theorem install_register (p : Ports R S) (d : Data R S)
    (b present flag : Bool) (xs ys : List Bool) (i : Fin 3) :
    (install p d b present flag xs ys).regs (p.register i) =
      counterRegs b present flag i :=
  StructuredCalls.embedState_register _ _ _ _ p.register.injective i

@[simp] theorem install_counter (p : Ports R S) (d : Data R S)
    (b present flag : Bool) (xs ys : List Bool) :
    (install p d b present flag xs ys).stacks p.counter = xs :=
  StructuredCalls.embedState_stack _ _ _ _ (stackPorts p).injective 0

@[simp] theorem install_scratch (p : Ports R S) (d : Data R S)
    (b present flag : Bool) (xs ys : List Bool) :
    (install p d b present flag xs ys).stacks p.scratch = ys :=
  StructuredCalls.embedState_stack _ _ _ _ (stackPorts p).injective 1

noncomputable def decrementResult (p : Ports R S) (d : Data R S) : Data R S :=
  install p d false false (d.regs (p.register 2)) (ripple false (d.stacks p.counter)) []

noncomputable def zeroResult (p : Ports R S) (d : Data R S) : Data R S :=
  install p d false false (isZero (d.stacks p.counter)) (d.stacks p.counter) []

noncomputable def testResult (p : Ports R S) (d : Data R S) : Data R S :=
  (StructuredProgram.Atom.bnot (p.register 2) (p.register 2)).eval (zeroResult p d)

@[simp] theorem testResult_flag (p : Ports R S) (d : Data R S) :
    (testResult p d).regs (p.register 2) = !(isZero (d.stacks p.counter)) := by
  simp only [testResult, Atom.eval, State.ofCfg, Atom.instr, execInstr, Function.update_self]
  simp [zeroResult]

@[simp] theorem decrementResult_counter (p : Ports R S) (d : Data R S) :
    (decrementResult p d).stacks p.counter = ripple false (d.stacks p.counter) :=
  install_counter p d _ _ _ _ _

@[simp] theorem decrementResult_scratch (p : Ports R S) (d : Data R S) :
    (decrementResult p d).stacks p.scratch = [] := install_scratch p d _ _ _ _ _

noncomputable def nextState (p : Ports R S) (d : Data R S) : Data R S :=
  testResult p (decrementResult p d)

end SubexponentialSAT.CounterForPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchNativeScan
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

open BitProgram StructuredCalls
attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod

abbrev clear (i : Fin 24) : Cmd 19 24 := .call (StackRoutines.clearProgram i 16 17)

end SubexponentialSAT.SqrtLog.IrreducibleSearchFactorControl

/-! Fixed first-success scan using the concrete saved factor checker. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PairPreparationProgram
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

abbrev Data := State 16 34

end SubexponentialSAT.Subexp.PairPreparationProgram

end OAI.Algorithms
end


