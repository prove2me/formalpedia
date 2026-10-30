-- Prove2me | Definitions.Def_OAIQ081S052
-- name    : OAIQ081S052
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:40:16.055866+00:00
-- url     : https://prove2.me/theorems/920e51e2-2a9a-4407-9404-5fe15211f34f
-- title:
--   Definitions bundle OAIQ081S052 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 82 declarations of OpenAI's Lean: 48 definitions and 34 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidence.neutralScope`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.capacity`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.cut`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.inputCapacity`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.suppliedScope`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram.modelBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram.ready`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier.uKey`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.coefficientTriple`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar.stepBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.copiedSources`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.repeatAt`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.resetThree`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.arrayProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.arrayRepresented`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.binaryProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.binaryRepresented`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.evaluate`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.initialRun`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.integerRun`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.iterateRun`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.minusOneRun`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.naturalRun`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.newtonRun`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.oneCode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.tableCode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.tableConstructionRun`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.tableRun`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.zeroCode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram.emit`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram.finish`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram.lookup`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram.select`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram.selectJ`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Field.bound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.ValidKey`, `OAI.Algorithms.SubexponentialSAT.Subexp.IncidencePlanSpec.incidentAt` and 8 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_HeadIdentifierProgramSemantics`, `SubexponentialSAT_SqrtLog_HighIncidenceNeutral`, `SubexponentialSAT_SqrtLog_HighIncidenceProgramOrder`, `SubexponentialSAT_SqrtLog_HighIncidenceProgramPrepare`, `SubexponentialSAT_SqrtLog_HighIncidenceProgramPrepareBounds`, `SubexponentialSAT_SqrtLog_HighIncidenceProgramSemantics`, `SubexponentialSAT_SqrtLog_HornerProgramLoop`, `SubexponentialSAT_SqrtLog_HornerProgramModel`, `SubexponentialSAT_SqrtLog_HornerProgramServices`, `SubexponentialSAT_SqrtLog_IdempotentApplyProgramCore`, `SubexponentialSAT_SqrtLog_IdempotentApplyProgramMultiplierKeyCore`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramArrays`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramRepeat`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarMachine`, `SubexponentialSAT_SqrtLog_IdempotentProgramArrays`, `SubexponentialSAT_SqrtLog_IdempotentProgramBinary`, `SubexponentialSAT_SqrtLog_IdempotentProgramCore`, `SubexponentialSAT_SqrtLog_IdempotentProgramOutput`, `SubexponentialSAT_SqrtLog_IdempotentTableEntryProgram`, `SubexponentialSAT_SqrtLog_IdempotentTableEntryProgramLookup`, `SubexponentialSAT_SqrtLog_LeafParametersProgramField`, `SubexponentialSAT_SqrtLog_MomentsProgramValidity`, `SubexponentialSAT_SubexpFactorCountSetup`, `SubexponentialSAT_SubexpIncidencePlanScan`, `SubexponentialSAT_SubexpParameterProgram`, `SubexponentialSAT_SubexpScopeMembershipProgram`, `SubexponentialSAT_Subexp_BlockCopyProgram`, `SubexponentialSAT_Subexp_IncidencePlanSpec`, `SubexponentialSAT_Subexp_TupleProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S023`, `OAIQ081S024`, `OAIQ081S025`, `OAIQ081S026`, `OAIQ081S027`, `OAIQ081S028`, `OAIQ081S029`, `OAIQ081S030`, `OAIQ081S031`, `OAIQ081S032` and `OAIQ081S033` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S069`, `OAIQ081S070`, `OAIQ081S075`, `OAIQ081S076`, `OAIQ081S077`, `OAIQ081S078` and `OAIQ081S080`; the statement `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeResourceBounds.measured_polylog`; the proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.eventually_forwardHighMask_guards`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S023
import Definitions.Def_OAIQ081S024
import Definitions.Def_OAIQ081S025
import Definitions.Def_OAIQ081S026
import Definitions.Def_OAIQ081S027
import Definitions.Def_OAIQ081S028
import Definitions.Def_OAIQ081S029
import Definitions.Def_OAIQ081S030
import Definitions.Def_OAIQ081S031
import Definitions.Def_OAIQ081S032
import Definitions.Def_OAIQ081S033

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_TupleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control Cartesian tuple generation

Alphabet words, tuple payloads, and iteration depths are stack data.  The
instruction tables below do not depend on any of their lengths.
-/

namespace SubexponentialSAT.Subexp.TupleProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-! The fixed ABI uses ten Boolean registers and nine Boolean stacks:
0 prior tuples, 1 saved alphabet, 2 current reversed tuple, 3 alphabet cursor,
4 reversed word, 5 output, 6 copied tuple, 7 copy scratch, 8 unary depth.
Registers 0--2 and 3--5 belong to the two framed iterators, 6--7 are scratch,
and 8--9 belong to the eventual depth loop. -/

abbrev readDepth : Cmd 10 9 := RecordPrograms.atom (.pop 8 8 9)

end SubexponentialSAT.Subexp.TupleProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_BlockCopyProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed bit program for copying a local table into every block

Stack 0 contains the encoded local table, stack 1 the output suffix, stack 2
is empty scratch, and stack 3 contains the unary number of blocks.  The same
finite program handles all table lengths and block counts.  It preserves the
local table and prefixes one copy per block to the output.  This is the compact
block-major representation of the repeated local basis/complement arrays;
scattering their coordinates through the packing is a separate operation.
-/

namespace SubexponentialSAT.Subexp.BlockCopyProgram

open BitProgram StructuredCalls StackRoutines

theorem popCount_eval (n : ℕ) (value active : Bool) (table output : List Bool) :
    Eval popCount 1 (data value active table output (List.replicate n true))
      (loopState n table output) := by
  have h : (StructuredProgram.Atom.pop (3 : Fin 4) (0 : Fin 3) 2).eval
      (data value active table output (List.replicate n true)) =
      loopState n table output := by
    apply state_ext
    · funext j
      cases n <;> fin_cases j <;>
        simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg,
          execInstr, readRegs, data, loopState, List.replicate_succ]
    · funext j
      cases n <;> fin_cases j <;>
        simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg,
          execInstr, data, loopState, List.replicate_succ]
  rw [← h]
  exact .base (.atom _ _)

theorem copyTable_eval (value active : Bool) (table output counter : List Bool) :
    Eval copyTable (7 * table.length + 5)
      (data value active table output counter)
      (data false active table (table ++ output) counter) := by
  apply Eval.call
  have h := halt_after_trace _
    (copyProgram_trace (0 : Fin 4) 1 2 (0 : Fin 3) 1
      (by decide) (by decide) (by decide) (by decide)
      (data value active table output counter).regs
      (data value active table output counter).stacks (by rfl)) 7 rfl rfl
  have hr : readRegs (data value active table output counter).regs 0 1 none =
      (data false active table (table ++ output) counter).regs := by
    funext j
    fin_cases j <;> simp [data, readRegs]
  have hs : copyStacks (0 : Fin 4) 1 (data value active table output counter).stacks =
      (data false active table (table ++ output) counter).stacks := by
    funext j
    fin_cases j <;> simp [data, copyStacks]
  simp only [copyResult] at h
  rw [hr, hs] at h
  simpa only [data, Matrix.cons_val_zero, StructuredProgram.State.withPC,
    copyProgram, Nat.add_assoc, Nat.reduceAdd] using h

theorem body_eval (n : ℕ) (table output : List Bool) :
    Eval body (7 * table.length + 6) (loopState (n + 1) table output)
      (loopState n table (table ++ output)) := by
  have h := Eval.seq (copyTable_eval true true table output (List.replicate n true))
    (popCount_eval n false true table (table ++ output))
  simpa only [body, loopState, Nat.add_assoc] using h

/-- Exact loop cost: every copied bit executes the already verified copy
routine, and every iteration includes the counter pop and loop guard. -/
theorem loop_eval (n : ℕ) (table output : List Bool) :
    Eval loop (n * (7 * table.length + 7) + 1)
      (loopState n table output)
      (loopState 0 table (copies n table ++ output)) := by
  induction n generalizing output with
  | zero =>
      simpa only [loop, Nat.zero_mul, Nat.zero_add, copies_zero, List.nil_append] using
        (Eval.while_false (test := (2 : Fin 3)) (body := body)
          (a := loopState 0 table output) rfl)
  | succ n ih =>
      have h := Eval.while_true (test := (2 : Fin 3)) (body := body)
        (a := loopState (n + 1) table output) (by rfl)
        (body_eval n table output) (ih (table ++ output))
      have hn : (7 * table.length + 6) + (n * (7 * table.length + 7) + 1) + 1 =
          (n + 1) * (7 * table.length + 7) + 1 := by ring
      simpa only [loop, hn, copies_succ, List.append_assoc] using h

theorem command_eval (n : ℕ) (table output : List Bool) :
    Eval command (n * (7 * table.length + 7) + 2)
      (initialState n table output)
      (data false false table (copies n table ++ output) []) := by
  have h := Eval.seq (popCount_eval n false false table output) (loop_eval n table output)
  have hn : 1 + (n * (7 * table.length + 7) + 1) =
      n * (7 * table.length + 7) + 2 := by omega
  simpa only [command, initialState, loopState, hn] using h

end SubexponentialSAT.Subexp.BlockCopyProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpFactorCountSetup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Preserving setup of a factor-local assignment count

The fixed program copies a unary arity, counts the copy into a binary exponent,
and invokes the actual preserving power routine.  The base and unary arity are
retained verbatim.  The number of bits in either input is runtime data.
-/

namespace SubexponentialSAT.SubexpFactorCountSetup

open BitProgram StructuredCalls StackRoutines

abbrev lengthProgram : Program 8 13 14 :=
  ProgramLinking.liftProgram CounterPrograms.lengthProgram lengthRegisters lengthPorts

end SubexponentialSAT.SubexpFactorCountSetup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpParameterProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual finite programs for the growing packing parameters

Numbers are little-endian Boolean stacks, with leading zeroes allowed. The
programs below manipulate only bits and stacks; natural-number quantities in
their specifications and cost bounds are not machine registers.
-/

namespace SubexponentialSAT.SubexpParameterProgram

open SubexponentialSAT.BitProgram
open SubexponentialSAT.CounterPrograms

def runAtoms {r s : ℕ} : List (StructuredProgram.Atom r s) →
    StructuredProgram.State r s → StructuredProgram.State r s
  | [], d => d
  | op :: ops, d => runAtoms ops (op.eval d)

theorem atoms_eval {r s : ℕ} (ops : List (StructuredProgram.Atom r s))
    (d : StructuredProgram.State r s) :
    StructuredProgram.Eval (atoms ops) ops.length d (runAtoms ops d) := by
  induction ops generalizing d with
  | nil => exact .skip d
  | cons op ops ih =>
      simpa only [atoms, runAtoms, List.length_cons, Nat.add_comm 1] using
        StructuredProgram.Eval.seq (.atom op d) (ih (op.eval d))

/-! ## Consume a most-significant zero prefix and the leading one -/

def trimCfg (pc : Option (Fin 6)) (b present : Bool) (xs : List Bool) : Cfg 3 3 6 :=
  ⟨pc, counterRegs b present false, lengthStacks [] xs []⟩

theorem trim_finish (b present : Bool) (xs : List Bool) :
    Trace trimProgram 3 (trimCfg (some 3) b present xs) (trimCfg none false false xs) := by
  refine .cons (b := trimCfg (some 4) false present xs) ?_
    (.cons (b := trimCfg (some 5) false false xs) ?_ (.cons ?_ (.refl _)))
  all_goals simp [step, trimCfg, execInstr]

theorem trim_trace (xs : List Bool) (b present : Bool) :
    Trace trimProgram (trimCost xs) (trimCfg (some 0) b present xs)
      (trimCfg none false false (trimTail xs)) := by
  induction xs generalizing b present with
  | nil =>
      refine .cons (b := trimCfg (some 1) false false []) ?_
        (.cons ?_ (trim_finish false false []))
      all_goals simp [step, trimCfg, execInstr, readRegs]
  | cons a xs ih =>
      cases a with
      | false =>
          refine .cons (b := trimCfg (some 1) false true xs) ?_
            (.cons (b := trimCfg (some 2) false true xs) ?_
              (.cons ?_ (ih false true)))
          all_goals simp [step, trimCfg, execInstr, readRegs]
      | true =>
          refine .cons (b := trimCfg (some 1) true true xs) ?_
            (.cons (b := trimCfg (some 2) true true xs) ?_
              (.cons ?_ (trim_finish true true xs)))
          all_goals simp [step, trimCfg, execInstr, readRegs]

theorem trim_complete_trace (xs : List Bool) :
    Trace trimProgram (trimCost xs) (initial trimProgram xs)
      (terminal trimProgram (trimTail xs)) := by
  have hi : initial trimProgram xs = trimCfg (some 0) false false xs := by
    simp [initial, trimCfg ]
    constructor <;> funext i <;> fin_cases i <;> simp [counterRegs, lengthStacks]
  have ht : terminal trimProgram (trimTail xs) = trimCfg none false false (trimTail xs) := by
    simp [terminal, trimCfg ]
    constructor <;> funext i <;> fin_cases i <;> simp [counterRegs, lengthStacks]
  rw [hi, ht]
  exact trim_trace xs false false

theorem trim_complete_runs (xs : List Bool) :
    RunsIn trimProgram (3 * xs.length + 6) (initial trimProgram xs)
      (terminal trimProgram (trimTail xs)) :=
  ⟨trimCost xs, trimCost_le xs, trim_complete_trace xs⟩

/-! ## Concrete input reversal -/

theorem reverseTransfer_trace (xs : List Bool) :
    Trace reverseTransfer (3 * xs.length + 3) (initial reverseTransfer xs)
      (terminal reverseTransfer xs.reverse) := by
  have h := StackRoutines.transferProgram_trace (r := 3) (s := 3)
    0 1 0 1 (by decide) (by decide) (fun _ => false)
    (fun i => if i = 0 then xs else [])
  have ht : StackRoutines.transferResult (3 : Fin 4) (0 : Fin 3) 1 (0 : Fin 3) 1
      (fun _ => false) (fun i => if i = 0 then xs else []) =
      {terminal reverseTransfer xs.reverse with pc := some 3} := by
    simp [StackRoutines.transferResult, StackRoutines.transferStacks, readRegs]
    first | done | (funext i; fin_cases i <;> simp)
  have hh : Trace reverseTransfer 1
      {terminal reverseTransfer xs.reverse with pc := some 3}
      (terminal reverseTransfer xs.reverse) := by
    refine .cons ?_ (.refl _)
    simp [step, execInstr, terminal]
  rw [ht] at h
  change Trace reverseTransfer (3 * xs.length + 2) (initial reverseTransfer xs)
    {terminal reverseTransfer xs.reverse with pc := some 3} at h
  simpa only [Nat.add_assoc] using h.trans hh

theorem enter_terminal_eq_initial {r s l m : ℕ}
    (p : Program r s l) (q : Program r s m) (h : p.outputStack = q.inputStack)
    (word : List Bool) :
    ProgramLinking.enter q (terminal p word) = initial q word := by
  simp [ProgramLinking.enter, initial, h]

/-! ## Reindex and call the checked binary word-length counter -/

theorem lift_equiv_initial {r s l : ℕ} (p : Program r s l) (e : Fin s ≃ Fin s)
    (frame : Cfg r s l) (word : List Bool) :
    ProgramLinking.embedCfg id e id none frame (initial p word) =
      initial (ProgramLinking.liftProgram p id e) word := by
  simp [ProgramLinking.embedCfg, ProgramLinking.relocatePc, initial, extend_equiv]
  funext b
  simp only [e.symm_apply_eq]

theorem lift_equiv_terminal {r s l : ℕ} (p : Program r s l) (e : Fin s ≃ Fin s)
    (frame : Cfg r s l) (word : List Bool) :
    ProgramLinking.embedCfg id e id none frame (terminal p word) =
      terminal (ProgramLinking.liftProgram p id e) word := by
  simp [ProgramLinking.embedCfg, ProgramLinking.relocatePc, terminal, extend_equiv]
  funext b
  simp only [e.symm_apply_eq]

end SubexponentialSAT.SubexpParameterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadIdentifierProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram
open SubexponentialSAT BitProgram StructuredCalls

/-- Position-major one-hot words are read at the paid runtime index t*r+g. -/
theorem encodeWord_getD {r Q : ℕ} (w : MulticolorTypes.Word r Q) (t : Fin Q) (g : Fin r) :
    (Subexp.ReadPlan.encodeWord w).getD (t.val*r+g.val) false=decide (w t=g) := by
  let f : Fin (Q*r) → Bool := fun i =>
    decide (w (finProdFinEquiv.symm i).1=(finProdFinEquiv.symm i).2)
  have he : List.ofFn f=(List.ofFn fun i : Fin Q =>
      List.ofFn fun j : Fin r => f (finProdFinEquiv (i,j))).flatten := by
    simpa only [finProdFinEquiv,Equiv.coe_fn_mk,Nat.add_comm,Nat.mul_comm] using List.ofFn_mul f
  have hf (i : Fin Q) (j : Fin r) : f (finProdFinEquiv (i,j))=decide (w i=j) := by
    change decide (w (finProdFinEquiv.symm (finProdFinEquiv (i,j))).1=
      (finProdFinEquiv.symm (finProdFinEquiv (i,j))).2)=_
    rw [Equiv.symm_apply_apply]
  have he' : List.ofFn f=Subexp.ReadPlan.encodeWord w := by
    simpa only [hf,Subexp.ReadPlan.encodeWord] using he
  have hi : (finProdFinEquiv (t,g)).val=t.val*r+g.val := by
    simp [finProdFinEquiv]
    ring
  rw [← he',← hi]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using
    (finProdFinEquiv (t,g)).isLt)]
  simpa only [List.getElem_ofFn] using hf t g

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceNeutral
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Neutral unary factors cover exactly the otherwise unused coordinates. -/
namespace SubexponentialSAT.SqrtLog.HighIncidence

open scoped BigOperators

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

def neutralScope (scope : E → Finset V) : E ⊕ uncovered scope → Finset V
  | .inl e => scope e
  | .inr v => {v.val}

end SubexponentialSAT.SqrtLog.HighIncidence

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpScopeMembershipProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A concrete scope-membership subroutine for incidence-plan preparation.
The reversed scope record occupies stack 8 and the reversed query stack 2.
Stacks 0,1,3,4 are empty work ports; all remaining stacks are framed.
-/
namespace SubexponentialSAT.SubexpScopeMembershipProgram

open BitProgram StructuredCalls

abbrev clear (i : Fin 10) : Cmd 10 10 := .call (StackRoutines.clearProgram i 0 1)

end SubexponentialSAT.SubexpScopeMembershipProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_IncidencePlanSpec
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Ordered incidence plans from finite scope lists

The numeric producer records incident factors in their input order. The
typed refinement uses the rank in that same list as the local slot.
-/

namespace SubexponentialSAT.Subexp.IncidencePlanSpec

/-- The finite typed pattern obtained by testing membership in the actual
scope lists. Repeated entries and their inner order do not change incidence. -/
def pattern (D : ℕ) (scopes : List (List ℕ)) :
    SubexponentialSAT.Factor.Pattern (Fin D) (Fin scopes.length) where
  scope e := Finset.univ.filter fun v => v.val ∈ scopes.get e

@[simp] theorem mem_pattern_scope (D : ℕ) (scopes : List (List ℕ))
    (v : Fin D) (e : Fin scopes.length) :
    v ∈ (pattern D scopes).scope e ↔ v.val ∈ scopes.get e := by
  simp [pattern]

open SubexponentialSAT.SlotAssignment

theorem incident_mem (D : ℕ) (scopes : List (List ℕ)) (v : Fin D)
    (e : Incident (pattern D scopes) v) :
    e.val.val ∈ incidentIndices scopes v.val :=
  (mem_incidentIndices scopes v.val e.val).mpr
    ((mem_pattern_scope D scopes v e.val).mp e.property)

/-- Lookup by occurrence rank in the list emitted by the numeric producer. -/
def incidentAt (D : ℕ) (scopes : List (List ℕ)) (v : Fin D)
    (i : Fin (degree scopes v.val)) : Incident (pattern D scopes) v := by
  let e := (incidentIndices scopes v.val).get i
  have he : e ∈ incidentIndices scopes v.val := List.get_mem _ _
  have hlt : e < scopes.length := incidentIndex_lt scopes v.val e he
  refine ⟨⟨e, hlt⟩, ?_⟩
  exact (mem_pattern_scope D scopes v ⟨e, hlt⟩).mpr
    ((mem_incidentIndices scopes v.val ⟨e, hlt⟩).mp he)

/-- Incident factors and their explicitly computed occurrence ranks. -/
def incidentEquiv (D : ℕ) (scopes : List (List ℕ)) (v : Fin D) :
    Incident (pattern D scopes) v ≃ Fin (degree scopes v.val) where
  toFun e := ⟨(incidentIndices scopes v.val).idxOf e.val.val,
    List.idxOf_lt_length_iff.mpr (incident_mem D scopes v e)⟩
  invFun := incidentAt D scopes v
  left_inv e := by
    apply Subtype.ext
    apply Fin.ext
    exact List.getElem_idxOf (List.idxOf_lt_length_iff.mpr (incident_mem D scopes v e))
  right_inv i := by
    apply Fin.ext
    exact (incidentIndices_nodup scopes v.val).idxOf_getElem i.val i.isLt

theorem card_incident (D : ℕ) (scopes : List (List ℕ)) (v : Fin D) :
    Fintype.card (Incident (pattern D scopes) v) = degree scopes v.val := by
  simpa only [Fintype.card_fin] using Fintype.card_congr (incidentEquiv D scopes v)

end SubexponentialSAT.Subexp.IncidencePlanSpec

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpIncidencePlanScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed finite scan of encoded scopes. No slot map is supplied as input:
the local slot order is the encounter order of incident factors. -/
namespace SubexponentialSAT.SubexpIncidencePlanScan

open BitProgram StructuredCalls
open SubexpIncidencePlanPrimitives

def ports : RecordPrograms.Ports 10 10 where
  tag := 7
  present := 8
  found := 9
  source := 6
  payload := 8
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

end SubexponentialSAT.SubexpIncidencePlanScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical mask is exactly the finite incidence cutoff on original
variables. The theorem counts zero-degree variables in the ambient dimension. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram
open scoped BigOperators

abbrev suppliedScope (n : ℕ) (scopes : List (List ℕ)) :=
  (Subexp.IncidencePlanSpec.pattern n scopes).scope

theorem degree_suppliedScope (n : ℕ) (scopes : List (List ℕ)) (v : Fin n) :
    Incidence.degree (suppliedScope n scopes) v = degree scopes v.val := by
  have h := Subexp.IncidencePlanSpec.card_incident n scopes v
  rw [SlotAssignment.card_incident] at h
  exact h

end SubexponentialSAT.SqrtLog.HighIncidenceProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramOrder
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical mask traverses original coordinates in descending order.
This explicit order, rather than an arbitrary finite-type equivalence,
identifies each odometer position with its actual original variable. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Order

theorem physical_mask (scopes : List (List ℕ)) (cut n : ℕ) :
    highPrefix scopes cut n = (coordinates n).map
      (fun v => decide (v ∈ HighIncidence.high (suppliedScope n scopes) cut)) := by
  rw [highPrefix_range]
  simp only [HighIncidence.high, Finset.mem_filter, Finset.mem_univ, true_and,
    degree_suppliedScope, coordinates]
  rw [← List.map_coe_finRange n, ← List.map_reverse, List.map_map]
  rfl

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Order

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramPrepare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Complete physical preparation from explicit scopes and binary n,t.
The input contains neither scope counts, mass, cutoff, nor unary loop fuel.
All are computed by fixed finite programs. The output mask retains all n
original coordinates and is in descending original-coordinate order. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

def cut (scopes : List (List ℕ)) (n t : List Bool) :=
  (mass scopes * BinaryArithmetic.toNat t) ⌈/⌉ BinaryArithmetic.toNat n

def budget (scopes : List (List ℕ)) (n t : List Bool) :=
  (SubexpScopeCountSetup.countBudget (records scopes) + 1) +
  MassPreserve.bound (scopeBits scopes) + (SubexpFactorCountSetup.countBudget (mass scopes) + 1) +
  Cutoff.bound (List.replicate (mass scopes) false) t n +
  unarySized (cut scopes n t) (mass scopes + t.length + 2) + 2 +
  unarySized (BinaryArithmetic.toNat n) n.length + scanBudget scopes (BinaryArithmetic.toNat n) (cut scopes n t) + 1

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramPrepareBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Closed polynomial cost and dimension bound for the complete prefix.
The bound is polynomial in encoded scope length, numeric ambient n and t,
and the lengths of their binary input words; it does not assume precomputed
statistics or claim polynomiality solely in the binary lengths of n,t. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

def capacity (scopes : List (List ℕ)) (n t : List Bool) :=
  (scopeBits scopes).length + mass scopes + scopes.length + BinaryArithmetic.toNat n + BinaryArithmetic.toNat t +
    n.length + t.length + 2

def inputCapacity (scopes : List (List ℕ)) (n t : List Bool) :=
  (scopeBits scopes).length + BinaryArithmetic.toNat n + BinaryArithmetic.toNat t + n.length + t.length + 2

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HornerProgramLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HornerProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpConvolutionControl
open CRTLocalProgram (LowFrame lowFrame_update lowFrame_refl)

def ready {C : Type*} (base : Store) (encode : C → List Bool)
    (cs : List C) (a : C) (count : List Bool) : Store :=
  Function.update (Function.update (Function.update base 246 (backward encode cs))
    240 (encode a)) 248 count

end SubexponentialSAT.SqrtLog.HornerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HornerProgramServices
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fully discharged native binary services for arbitrary coefficient-vector
length. Shared by Horner, local CRT and dense polynomial services. -/
namespace SubexponentialSAT.SqrtLog.HornerProgram.Services

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem mulBudget_polynomial (B d : ℕ) :
    mulBudget B d ≤ 50000 * (d+1)^3 * (B+1)^2 := by
  have h := RingScan.serviceMulBudget_le B d
  unfold mulBudget
  ring_nf at *
  omega

end SubexponentialSAT.SqrtLog.HornerProgram.Services

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HornerProgramModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native Horner evaluation in the actual arbitrary-degree unramified
RingModel. The instruction table is independent of precision, extension
degree and polynomial length. Ring caches are explicit runtime inputs. -/
namespace SubexponentialSAT.SqrtLog.HornerProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def modelBudget (n t d : ℕ) : ℕ :=
  budget n (d * baseWidth 3 t)
    (Services.mulBudget (baseWidth 3 t) d) (Services.addBudget (baseWidth 3 t) d)

end SubexponentialSAT.SqrtLog.HornerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Executable Newton control over a supplied represented coefficient ring.
The measured counters below charge every callback and seven control events.
They are an intermediate interface, not a primitive bit-runtime certificate;
the supplied callbacks must be refined by actual serialized-array services. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open SubexponentialSAT.SubexpSymbolicCost

variable {C R : Type*} [CommRing R]

/-- Seven ring callbacks implement `3 e^2 - 2 e^3`, without division. -/
def newtonRun (ops : RingProgram C) (e : C) : C × ℕ :=
  let square := ops.mulRun e e
  let cube := ops.mulRun square.1 e
  let twiceSquare := ops.addRun square.1 square.1
  let threeSquare := ops.addRun twiceSquare.1 square.1
  let twiceCube := ops.addRun cube.1 cube.1
  let minusCube := ops.negRun twiceCube.1
  let out := ops.addRun threeSquare.1 minusCube.1
  (out.1, square.2 + cube.2 + twiceSquare.2 + threeSquare.2 +
    twiceCube.2 + minusCube.2 + out.2 + 7)

@[simp] theorem newtonRun_correct (ops : RepresentedRing C R) (e : C) :
    ops.decode (newtonRun ops.program e).1 = Idempotent.newton (ops.decode e) := by
  simp only [newtonRun, ops.mul_correct,
    ops.add_correct, ops.neg_correct, Idempotent.newton]
  ring

/-- A bounded recursion: exactly `n` Newton steps. -/
def iterateRun (ops : RingProgram C) (e : C) : ℕ → C × ℕ
  | 0 => (e, 1)
  | n + 1 =>
      let prev := iterateRun ops e n
      let out := newtonRun ops prev.1
      (out.1, prev.2 + out.2 + 1)

@[simp] theorem iterateRun_correct (ops : RepresentedRing C R) (e : C) (n : ℕ) :
    ops.decode (iterateRun ops.program e n).1 = Idempotent.iterate (ops.decode e) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change ops.decode (newtonRun ops.program (iterateRun ops.program e n).1).1 = _
      rw [newtonRun_correct, ih]
      rfl

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramArrays
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete coefficient arrays and their functional evaluation theorem.
The coefficient primitives remain an explicit `RepresentedRing`; all
nonconstant loops in these definitions have displayed finite bounds. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open scoped BigOperators
open SubexponentialSAT.SubexpSymbolicCost

variable {C A R : Type*} [CommRing A] [CommRing R]

/-- Construct a small natural coefficient by actual additions. -/
def naturalRun (ops : RingProgram C) : ℕ → C × ℕ
  | 0 => ops.zeroRun
  | n+1 =>
      let prev := naturalRun ops n
      let one := ops.oneRun
      let out := ops.addRun prev.1 one.1
      (out.1, prev.2 + one.2 + out.2 + 1)

def integerRun (ops : RingProgram C) : ℤ → C × ℕ
  | .ofNat n => naturalRun ops n
  | .negSucc n =>
      let pos := naturalRun ops (n+1)
      let out := ops.negRun pos.1
      (out.1, pos.2 + out.2 + 1)

@[simp] theorem naturalRun_correct (ops : RepresentedRing C A) (n : ℕ) :
    ops.decode (naturalRun ops.program n).1 = (n : A) := by
  induction n with
  | zero => simpa [naturalRun, RepresentedRing.program] using ops.zero_correct
  | succ n ih =>
      change ops.decode (ops.addRun (naturalRun ops.program n).1 ops.oneRun.1).1 = _
      rw [ops.add_correct, ih, ops.one_correct]
      simp

@[simp] theorem integerRun_correct (ops : RepresentedRing C A) (z : ℤ) :
    ops.decode (integerRun ops.program z).1 = (z : A) := by
  cases z with
  | ofNat n => simp [integerRun]
  | negSucc n =>
      change ops.decode (ops.negRun (naturalRun ops.program (n+1)).1).1 = _
      rw [ops.neg_correct, naturalRun_correct]
      simp

/-- The table is generated by small-integer arithmetic, not polynomial division. -/
def tableRun (ops : RingProgram C) {t : ℕ} (i j k : Fin (3*t)) : C × ℕ :=
  integerRun ops (hadicTable i j k)

/-- The table is materialized once; later uses read stored coefficient codes. -/
def tableConstructionRun (ops : RingProgram C) (t : ℕ) :
    (Fin (3*t) → Fin (3*t) → Fin (3*t) → C) × ℕ :=
  let entries := List.Vector.ofFn fun k : Fin (3*t) =>
    List.Vector.ofFn fun i : Fin (3*t) =>
      List.Vector.ofFn fun j : Fin (3*t) => tableRun ops i j k
  (fun i j k => (((entries.get k).get i).get j).1,
    (∑ k : Fin (3*t), ∑ i : Fin (3*t), ∑ j : Fin (3*t),
      (((entries.get k).get i).get j).2) + (3*t)^3 + 1)

def tableCode (ops : RingProgram C) {t : ℕ} :
    Fin (3*t) → Fin (3*t) → Fin (3*t) → C :=
  (tableConstructionRun ops t).1

@[simp] theorem tableCode_apply (ops : RingProgram C) {t : ℕ}
    (i j k : Fin (3*t)) : tableCode ops i j k = (tableRun ops i j k).1 := by
  simp [tableCode, tableConstructionRun]

def zeroCode (ops : RingProgram C) (t : ℕ) : Fin (3*t) → C :=
  fun _ => ops.zeroRun.1

def oneCode (ops : RingProgram C) (t : ℕ) : Fin (3*t) → C :=
  fun k => if k.val = 0 then ops.oneRun.1 else ops.zeroRun.1

abbrev evaluate (ops : RepresentedRing C A) (φ : A →+* R) (t : ℕ)
    (x : R) (v : Fin (3*t) → C) : R :=
  RingProgram.denote ops φ (hadicBasis t x) v

@[simp] theorem evaluate_zero (ops : RepresentedRing C A) (φ : A →+* R)
    (t : ℕ) (x : R) : evaluate ops φ t x (zeroCode ops.program t) = 0 := by
  simp [evaluate, RingProgram.denote, zeroCode, ops.zero_correct]

theorem evaluate_one (ops : RepresentedRing C A) (φ : A →+* R)
    (t : ℕ) (x : R) (ht : hValue x ^ t = 0) :
    evaluate ops φ t x (oneCode ops.program t) = 1 := by
  have h := atomInteger_eval t 0 0 1 x (by omega) ht
  simpa [evaluate, RingProgram.denote, oneCode, atomInteger,
    RepresentedRing.program, apply_ite, ops.zero_correct, ops.one_correct] using h

theorem tableCode_correct (ops : RepresentedRing C A) (φ : A →+* R)
    (t : ℕ) (x : R) (ht : hValue x ^ t = 0) (i j : Fin (3*t)) :
    hadicBasis t x i * hadicBasis t x j =
      ∑ k, φ (ops.decode (tableCode ops.program i j k)) * hadicBasis t x k := by
  simpa only [tableCode_apply, tableRun, integerRun_correct, map_intCast] using
    hadicTable_correct t x ht i j

/-- Actual array arithmetic is the bounded triple loop of `RingProgram.mulRun`.
The evaluation parameter and its nilpotence proof affect only correctness. -/
def arrayProgram (ops : RingProgram C) (t : ℕ) : RingProgram (Fin (3*t) → C) :=
  RingProgram.program ops (tableCode ops) (zeroCode ops t) (oneCode ops t)

def arrayRepresented (ops : RepresentedRing C A) (φ : A →+* R)
    (t : ℕ) (x : R) (ht : hValue x ^ t = 0) :
    RepresentedRing (Fin (3*t) → C) R :=
  RingProgram.represented ops φ (hadicBasis t x) (tableCode ops.program)
    (zeroCode ops.program t) (oneCode ops.program t)
    (tableCode_correct ops φ t x ht) (evaluate_zero ops φ t x) (evaluate_one ops φ t x ht)

@[simp] theorem arrayRepresented_program (ops : RepresentedRing C A) (φ : A →+* R)
    (t : ℕ) (x : R) (ht : hValue x ^ t = 0) :
    (arrayRepresented ops φ t x ht).program = arrayProgram ops.program t := rfl

@[simp] theorem arrayRepresented_decode (ops : RepresentedRing C A) (φ : A →+* R)
    (t : ℕ) (x : R) (ht : hValue x ^ t = 0) (v : Fin (3*t) → C) :
    (arrayRepresented ops φ t x ht).decode v = evaluate ops φ t x v := rfl

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramOutput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open scoped BigOperators
open SubexponentialSAT.SubexpSymbolicCost

variable {C A R : Type*} [CommRing A] [CommRing R]

/-- The initial H-adic vector is `(2u,-3u,u)` in its first digit. -/
def initialRun (ops : RingProgram C) (t : ℕ) (u : C) : (Fin (3*t) → C) × ℕ :=
  let zero := ops.zeroRun
  let twice := ops.addRun u u
  let three := ops.addRun twice.1 u
  let minusThree := ops.negRun three.1
  (fun k => if k.val = 0 then twice.1 else if k.val = 1 then minusThree.1
    else if k.val = 2 then u else zero.1,
    zero.2 + twice.2 + three.2 + minusThree.2 + 3*t + 4)

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Algebraic invariant for the native descending Horner application. Each
coefficient digit has three entries, and no power is recomputed by expansion. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram

open scoped BigOperators

variable {C A R : Type*} [CommRing A] [CommRing R]

def coefficientTriple (t : ℕ) (code : RingProgram.Code C (3*t)) (s : Fin t) : Triple C :=
  ⟨code (IdempotentProgram.digitIndex s 0),
   code (IdempotentProgram.digitIndex s 1),
   code (IdempotentProgram.digitIndex s 2)⟩

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramMultiplierKeyCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Source component: IdempotentApplyProgramMultiplierKey. -/

/-! Construction and application of the U monomial by actual native instructions. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier
open BitProgram StructuredCalls
open HashCircuitProgram.Native


/-- The monomial U, with empty Boolean support. -/
def uKey (n : ℕ) : Squarefree.Index (Fin n) := ⟨1,0,∅⟩

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier


end OAI.Algorithms
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

abbrev resetThree : Cmd 8 41 := .base (SubexpParameterProgram.atoms
  [.set 0 false, .set 1 false, .set 2 false])

theorem resetThree_eval (d : Data) : Eval resetThree 3 d (resetData d) := by
  exact .base (SubexpParameterProgram.atoms_eval _ d)

abbrev repeatAt (source target scratch count : Fin 41) : Cmd 8 41 :=
  .seq resetThree (.call (ProgramLinking.liftProgram Subexp.BlockCopyProgram.program
    repeatRegisters (repeatPorts source target scratch count)))

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

def copiedSources (target : Fin 41) : List (Fin 41) → Data → Data
  | [], d => d
  | source :: rest, d => copiedSources target rest (afterCopy d source target 0 1)

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

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

def stepBudget : ℕ := 6000*(baseWidth p t+1)^2+25*baseWidth p t+21

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramBinary
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Negation through multiplication by a cached negative unit. This permits
the native implementation to use only addition and multiplication services. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open SubexponentialSAT.SubexpSymbolicCost

variable {C A R : Type*} [CommRing A] [CommRing R]

def binaryProgram (ops : RingProgram C) (minusOne : C) : RingProgram C :=
  { ops with negRun := fun x => ops.mulRun minusOne x }

def binaryRepresented (ops : RepresentedRing C R) (minusOne : C)
    (hm : ops.decode minusOne = -1) : RepresentedRing C R :=
  { ops with
    negRun := fun x => ops.mulRun minusOne x
    neg_correct := by intro x; rw [ops.mul_correct, hm]; ring }

@[simp] theorem binaryRepresented_program (ops : RepresentedRing C R) (minusOne : C)
    (hm : ops.decode minusOne = -1) :
    (binaryRepresented ops minusOne hm).program = binaryProgram ops.program minusOne := rfl

/-- This array is constructed once and cached on the native constant port. -/
def minusOneRun (ops : RingProgram C) (t : ℕ) : (Fin (3*t) → C) × ℕ :=
  RingProgram.negRun ops (oneCode ops t)

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentTableEntryProgramLookup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram

open BitProgram StructuredCalls

abbrev emit (c : Fin 6) : Cmd 8 4 := .base
  (SubexpParameterProgram.atoms
    [.set 5 (codeBits c 0), .set 6 (codeBits c 1), .set 7 (codeBits c 2)])

def lookup : List (Fin 6) → Cmd 8 4
  | [] => emit 0
  | c :: cs => .seq (.base (.atom (.pop 2 0 1))) (.ite 1 (lookup cs) (emit c))

end SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentTableEntryProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native table-entry selector. The only input magnitudes are unary
stack data. Output registers 5,6,7 encode the six possible small coefficients. -/
namespace SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram

open BitProgram StructuredCalls

abbrev selectJ (a : ℕ) : Cmd 8 4 :=
  .ite 5 (lookup (coefficientsAt (a+1)))
    (.ite 6 (lookup (coefficientsAt (a+2))) (lookup (coefficientsAt a)))

abbrev select : Cmd 8 4 :=
  .ite 3 (selectJ 1) (.ite 4 (selectJ 2) (selectJ 0))

abbrev finish : Cmd 8 4 := .ite 7 (emit 0) select
abbrev command : Cmd 8 4 := .seq scanI (.seq scanJ (.seq subtract finish))
def program := compiled command 0 2

end SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram

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

def bound (exponent : List Bool) : ℕ :=
  PowerPrograms.runtimeBound [true,true] exponent + 9 * exponent.length + 19

theorem bound_polynomial (exponent : List Bool) :
    bound exponent ≤ 1000 * (BinaryArithmetic.toNat exponent + exponent.length + 2)^2 := by
  dsimp [bound,PowerPrograms.runtimeBound,PowerPrograms.workBound,PowerPrograms.callbackBound]
  nlinarith

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Field

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramValidity
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

namespace Product

def ValidKey {n : ℕ} (vars : Finset (Fin n)) (u J : ℕ) (a : Squarefree.Index (Fin n)) : Prop :=
  a.Kept u J ∧ a.Valid ∧ a.vars ⊆ vars

end Product
end SubexponentialSAT.SqrtLog.MomentsProgram

end OAI.Algorithms
end


