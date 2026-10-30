-- Prove2me | Definitions.Def_OAIQ081S046
-- name    : OAIQ081S046
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:35:52.795274+00:00
-- url     : https://prove2.me/theorems/d000a460-ce94-41c2-b38b-06067489ed9a
-- title:
--   Definitions bundle OAIQ081S046 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 106 declarations of OpenAI's Lean: 22 definitions, 1 inductive type or structure and 83 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.DensePolynomialLoop.WordStep`, `OAI.Algorithms.SubexponentialSAT.DensePolynomialLoop.addWords`, `OAI.Algorithms.SubexponentialSAT.DensePolynomialLoop.addWordsTotal`, `OAI.Algorithms.SubexponentialSAT.ExecCNFMembership.callback`, `OAI.Algorithms.SubexponentialSAT.ExecCNFMembership.clear`, `OAI.Algorithms.SubexponentialSAT.ExecCNFMembership.clearProgram`, `OAI.Algorithms.SubexponentialSAT.ExecCNFMembership.membership`, `OAI.Algorithms.SubexponentialSAT.ExecCNFMembership.membershipProgram`, `OAI.Algorithms.SubexponentialSAT.ExecCNFSubset.callback`, `OAI.Algorithms.SubexponentialSAT.ExecCNFSubset.clear`, `OAI.Algorithms.SubexponentialSAT.ExecCNFSubset.clearProgram`, `OAI.Algorithms.SubexponentialSAT.ExecCNFSubset.memberCall`, `OAI.Algorithms.SubexponentialSAT.ExecCNFSubset.memberProgram`, `OAI.Algorithms.SubexponentialSAT.ExecCNFSubset.subset`, `OAI.Algorithms.SubexponentialSAT.ExecClauseDedupProgram.Clean`, `OAI.Algorithms.SubexponentialSAT.ExecClauseFiltersProgram.Data`, `OAI.Algorithms.SubexponentialSAT.ExecClauseFiltersProgram.state`, `OAI.Algorithms.SubexponentialSAT.ExecClauseRelationsProgram.combined`, `OAI.Algorithms.SubexponentialSAT.RecordPrograms.CallbackContract`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchCandidateControl.Data`, `OAI.Algorithms.SubexponentialSAT.SubexpFlatAdd.ready`, `OAI.Algorithms.SubexponentialSAT.SubexpNormalizeProgram.discardRecordProgram`, `OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives.afterCounted`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_CounterPrograms`, `SubexponentialSAT_DensePolynomialLoop`, `SubexponentialSAT_ExecCNFMembership`, `SubexponentialSAT_ExecCNFRecords`, `SubexponentialSAT_ExecCNFSubset`, `SubexponentialSAT_ExecClauseCost`, `SubexponentialSAT_ExecClauseCost39Lift`, `SubexponentialSAT_ExecClauseDedupProgram`, `SubexponentialSAT_ExecClauseFiltersProgram`, `SubexponentialSAT_ExecClauseRelationsProgram`, `SubexponentialSAT_ModularArithmetic`, `SubexponentialSAT_ModularDivisionPrograms`, `SubexponentialSAT_ModularPrograms`, `SubexponentialSAT_ModularRingCore`, `SubexponentialSAT_ModularRingPrograms`, `SubexponentialSAT_ProgramLinking`, `SubexponentialSAT_ProgramStateFrames`, `SubexponentialSAT_RecordPrograms`, `SubexponentialSAT_SqrtLog_IrreducibleSearchNativeScan`, `SubexponentialSAT_StackRoutines`, `SubexponentialSAT_StructuredCalls`, `SubexponentialSAT_SubexpFlatAdd`, `SubexponentialSAT_SubexpLiftRing`, `SubexponentialSAT_SubexpNormalizeProgram`, `SubexponentialSAT_SubexpScalarMachine`, `SubexponentialSAT_SubexpScanPrimitives`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S023`, `OAIQ081S024` and `OAIQ081S025` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S066`, `OAIQ081S067`, `OAIQ081S068`, `OAIQ081S070`, `OAIQ081S071`, `OAIQ081S073`, `OAIQ081S074`, `OAIQ081S076`, `OAIQ081S077`, `OAIQ081S078`, `OAIQ081S079`, `OAIQ081S080` and `OAIQ081S081`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S023
import Definitions.Def_OAIQ081S024
import Definitions.Def_OAIQ081S025

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ProgramLinking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Finite program relocation and linking

Every linked block is an instruction table inside one finite program.  A block's
halt can be replaced by a jump to a caller-specified continuation.  The proofs
below transfer actual instruction traces, including that final instruction, and
preserve all ambient registers and stacks outside the block's assigned ports.

The finite sizes and maps are fixed when the linked program is constructed; they
do not inspect the unbounded input stacks.
-/

namespace SubexponentialSAT.ProgramLinking

open BitProgram

variable {r s l R S L : ℕ}

theorem liftProgram_runsIn (p : Program r s l) (register : Fin r → Fin R)
    (stack : Fin s → Fin S) (frame : Cfg R S l)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    {n : ℕ} {a b : Cfg r s l} (h : RunsIn p n a b) :
    RunsIn (liftProgram p register stack) n
      (embedCfg register stack id none frame a) (embedCfg register stack id none frame b) :=
  relocate_runsIn p _ register stack id none frame hregister hstack (fun _ => rfl) h

/-- A trace ending at an active label has not executed any halt instruction.
Thus the target may give all source halt labels an arbitrary continuation body. -/
theorem relocate_trace_before_halt (p : Program r s l) (q : Program R S L)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L)) (frame : Cfg R S L)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (hcode : ∀ pc, p.code pc ≠ .halt →
      q.code (label pc) = relocateInstr register stack label returnPc (p.code pc))
    {n : ℕ} {a b : Cfg r s l} (h : Trace p n a b) (hb : b.pc ≠ none) :
    Trace q n (embedCfg register stack label returnPc frame a)
      (embedCfg register stack label returnPc frame b) := by
  induction h with
  | refl => exact .refl _
  | @cons n a c b hs ht ih =>
      have hlocal : ∀ pc, a.pc = some pc →
          q.code (label pc) = relocateInstr register stack label returnPc (p.code pc) := by
        intro pc hpc
        apply hcode pc
        intro hhalt
        have hc : c = execInstr .halt a := by
          simpa [step, hpc, hhalt] using hs.symm
        have hcpc : c.pc = none := by simp [hc, execInstr]
        exact hb (trace_from_halted p ht hcpc)
      exact .cons
        (relocate_step_at p q register stack label returnPc frame hregister hstack hlocal hs)
        (ih hb)

/-- Designated-exit version: the exit's instruction can be replaced without
charging a step until the caller actually executes that instruction. -/
theorem relocate_trace_to_exit (p : Program r s l) (q : Program R S L)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L)) (frame : Cfg R S L)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (exit : Fin l) (hexit : p.code exit = .halt)
    (hcode : ∀ pc, pc ≠ exit →
      q.code (label pc) = relocateInstr register stack label returnPc (p.code pc))
    {n : ℕ} {a b : Cfg r s l} (h : Trace p n a b) (hb : b.pc = some exit) :
    Trace q n (embedCfg register stack label returnPc frame a)
      (embedCfg register stack label returnPc frame b) := by
  apply relocate_trace_before_halt p q register stack label returnPc frame
    hregister hstack ?_ h (by simp [hb])
  intro pc hpc
  apply hcode pc
  intro heq
  exact hpc (heq ▸ hexit)

/-! ## Concrete disjoint linking -/

end SubexponentialSAT.ProgramLinking

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_CounterPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Executable binary counters on Boolean stacks

The head of a stack is the least-significant bit.  Leading zeroes are allowed:
there is no hidden normalization precondition, and zero testing scans the bits.
The arithmetic functions below specify the results of finite instruction-table
programs; the machine execution theorems appear after the specifications.
-/

namespace SubexponentialSAT.CounterPrograms


open SubexponentialSAT.BitProgram


/-! ## Deriving a binary counter from an input list -/

theorem length_increment_trace (b p : Bool) (data count : List Bool) :
    Trace lengthProgram (rippleCost true count)
      (lengthCfg 2 b p false data count [])
      (lengthCfg 12 false false false data (ripple true count) []) := by
  have h := ProgramLinking.relocate_trace_to_exit (rippleProgram true) lengthProgram
    id Fin.succ lengthLabel none (lengthCfg 0 false false false data [] [])
    Function.injective_id (Fin.succ_injective 2) 10 rfl length_increment_code
    (ripple_trace true b p false count []) rfl
  simpa [lengthLabel] using h

theorem length_iteration (b p a : Bool) (data count : List Bool) (B : ℕ)
    (hB : count.length ≤ B) :
    RunsIn lengthProgram (8 * B + 10)
      (lengthCfg 0 b p false (a :: data) count [])
      (lengthCfg 0 false false false data (ripple true count) []) := by
  have hprefix : Trace lengthProgram 2
      (lengthCfg 0 b p false (a :: data) count [])
      (lengthCfg 2 a true false data count []) :=
    .cons (length_step0_cons b p a data count)
      (.cons (length_step1 a true data count) (.refl _))
  have hsuffix : Trace lengthProgram 1
      (lengthCfg 12 false false false data (ripple true count) [])
      (lengthCfg 0 false false false data (ripple true count) []) :=
    .cons (length_step12 data (ripple true count)) (.refl _)
  refine ⟨2 + rippleCost true count + 1, ?_,
    (hprefix.trans (length_increment_trace a true data count)).trans hsuffix⟩
  have hcost := rippleCost_le true count
  omega

/-- General accumulating count: a pre-existing binary counter gains exactly
one for each consumed input bit. `B` is a proved width bound, not machine state. -/
theorem length_accumulate (data count : List Bool) (B : ℕ)
    (hB : count.length + data.length ≤ B) (b p : Bool) :
    ∃ output : List Bool,
      value output = value count + data.length ∧ output.length ≤ count.length + data.length ∧
      RunsIn lengthProgram (data.length * (8 * B + 10) + 2)
        (lengthCfg 0 b p false data count [])
        (lengthCfg 13 false false false [] output []) := by
  induction data generalizing count b p with
  | nil =>
      refine ⟨count, by simp, by simp, ?_⟩
      refine ⟨2, by simp, ?_⟩
      exact .cons (length_step0_nil b p count)
        (.cons (length_step1 false false [] count) (.refl _))
  | cons a data ih =>
      have hlen := ripple_length_le true count
      have hnext : (ripple true count).length + data.length ≤ B := by
        simp only [List.length_cons] at hB
        omega
      obtain ⟨output, hvalue, hsize, hrun⟩ :=
        ih (ripple true count) hnext false false
      have hcount : count.length ≤ B := by omega
      have hprefix := length_iteration b p a data count B hcount
      refine ⟨output, ?_, ?_, ?_⟩
      · rw [value_increment] at hvalue
        simp only [List.length_cons]
        omega
      · simp only [List.length_cons]
        omega
      · convert hprefix.trans hrun using 1
        all_goals try with_reducible_and_instances rfl
        simp only [List.length_cons]
        ring

/-- The utility accepted by callers whose current value/presence bits are dirty.
Only the accumulator bit must start false; both live data bits are overwritten. -/
theorem length_correct_from (b p : Bool) (data : List Bool) :
    ∃ output : List Bool, value output = data.length ∧ output.length ≤ data.length ∧
      RunsIn lengthProgram (data.length * (8 * data.length + 10) + 3)
        (lengthCfg 0 b p false data [] []) (terminal lengthProgram output) := by
  obtain ⟨output, hvalue, hsize, hrun⟩ :=
    length_accumulate data [] data.length (by simp) b p
  have hhalt : RunsIn lengthProgram 1
      (lengthCfg 13 false false false [] output []) (terminal lengthProgram output) :=
    ⟨1, le_rfl, .cons (length_halt_step output) (.refl _)⟩
  refine ⟨output, by simpa using hvalue, by simpa using hsize, ?_⟩
  convert hrun.trans hhalt using 1
  all_goals try with_reducible_and_instances rfl

/-- A fixed finite program produces the binary representation of the raw input
length with a proved polynomial bound on actual primitive source instructions. -/
theorem length_correct (data : List Bool) :
    ∃ output : List Bool, value output = data.length ∧ output.length ≤ data.length ∧
      RunsIn lengthProgram (data.length * (8 * data.length + 10) + 3)
        (initial lengthProgram data) (terminal lengthProgram output) := by
  simpa only [initial_length_eq] using length_correct_from false false data

end SubexponentialSAT.CounterPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ModularArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Binary long division with finite-bit operations

The executable functions below inspect Bool/list constructors only: they do not
call Nat division, multiplication, comparison, or subtraction on encoded values.
Natural arithmetic appears solely in specifications and event-count proofs.
The event count is not asserted to be a primitive Turing-machine runtime.
-/

namespace SubexponentialSAT.ModularArithmetic

open SubexponentialSAT.BinaryArithmetic

/-! A measured finite-control subtraction transducer. -/

/-! Instrumentation with events carrying only finitely many Boolean values.
The logs record every padding/subtraction cell and each shift/selection.
They are not a primitive-machine simulation certificate. -/

theorem reduceLogged_correct (m xs : List Bool) (hm : 0 < BinaryArithmetic.toNat m) :
    BinaryArithmetic.toNat (reduceLogged m xs).1 = BinaryArithmetic.toNat xs % BinaryArithmetic.toNat m := by
  rw [reduceLogged_value]
  exact reduce_correct m xs hm

/-! Modular addition and multiplication combine the concrete binary
arithmetic runs with the concrete long-division run. -/

theorem addModRun_correct (m xs ys : List Bool) (hm : 0 < BinaryArithmetic.toNat m) :
    BinaryArithmetic.toNat (addModRun m xs ys).1 = (BinaryArithmetic.toNat xs + BinaryArithmetic.toNat ys) % BinaryArithmetic.toNat m := by
  simp only [addModRun, reduceLogged_correct _ _ hm]
  rw [(SubexponentialSAT.BinaryArithmetic.addRun_correct_and_cost false xs ys).1]
  simp

/-! An explicit finite ring expression for geometric correction. Its
operation-node count is a ring-operation bound, separately from bit costs. -/

end SubexponentialSAT.ModularArithmetic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpLiftRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Uniform coefficient representations for the growing-parameter argument

Every base residue has an explicit little-endian word of width
`mu * (Nat.log 2 p + 1)`. The polynomial quotient uses one such word per
basis coefficient. These bounds keep p and mu visible. Binary modular
operations below use the existing bit/list algorithms and normalize back
to the prescribed width; their counters are source-level finite events,
not a claimed Turing-machine simulation.
-/

namespace SubexponentialSAT.SubexpLiftRing

open SubexponentialSAT.BinaryArithmetic

theorem addBaseRun_value (B : ℕ) (modulus xs ys : List Bool)
    (hm : 0 < BinaryArithmetic.toNat modulus) (hcap : BinaryArithmetic.toNat modulus ≤ 2 ^ B) :
    BinaryArithmetic.toNat (addBaseRun B modulus xs ys).1 = (BinaryArithmetic.toNat xs + BinaryArithmetic.toNat ys) % BinaryArithmetic.toNat modulus := by
  rw [addBaseRun, normalizeBits_value]
  · exact ModularArithmetic.addModRun_correct modulus xs ys hm
  · rw [ModularArithmetic.addModRun_correct modulus xs ys hm]
    exact (Nat.mod_lt _ hm).trans_le hcap

end SubexponentialSAT.SubexpLiftRing

end OAI.Algorithms
end

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

theorem reverseProgram_trace {r s : ℕ} (src tmp₁ tmp₂ : Fin s) (value present : Fin r)
    (h₁ : src ≠ tmp₁) (h₂ : src ≠ tmp₂) (h₁₂ : tmp₁ ≠ tmp₂) (hvp : value ≠ present)
    (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (htmp₁ : stk tmp₁ = []) (htmp₂ : stk tmp₂ = []) :
    Trace (reverseProgram src tmp₁ tmp₂ value present) (9 * (stk src).length + 6)
      ⟨some 0, regs, stk⟩ (reverseResult 9 src value present regs stk) := by
  let p := reverseProgram src tmp₁ tmp₂ value present
  let regs₁ := readRegs regs value present none
  let regs₂ := readRegs regs₁ value present none
  let stk₁ := transferStacks src tmp₁ stk
  let stk₂ := transferStacks tmp₁ tmp₂ stk₁
  have t₁ := transfer_trace p src tmp₁ value present 0 1 2 3 h₁ hvp
    rfl rfl rfl regs stk
  have t₂ := transfer_trace p tmp₁ tmp₂ value present 3 4 5 6 h₁₂ hvp
    rfl rfl rfl regs₁ stk₁
  have t₃ := transfer_trace p tmp₂ src value present 6 7 8 9 h₂.symm hvp
    rfl rfl rfl regs₂ stk₂
  have hlen₁ : (stk₁ tmp₁).length = (stk src).length := by
    simp [stk₁, transferStacks, htmp₁]
  have hlen₂ : (stk₂ tmp₂).length = (stk src).length := by
    simp [stk₂, stk₁, transferStacks, h₁₂.symm, h₂.symm, htmp₁, htmp₂]
  have hfinal := three_transfers_eq_reverse src tmp₁ tmp₂ stk h₁ h₂ h₁₂ htmp₁ htmp₂
  have total := (t₁.trans t₂).trans t₃
  have total' : Trace p
      ((3 * (stk src).length + 2 + (3 * (stk src).length + 2)) +
        (3 * (stk src).length + 2))
      ⟨some 0, regs, stk⟩ (reverseResult 9 src value present regs stk) := by
    simpa only [hlen₁, hlen₂, transferResult, reverseResult, regs₂, regs₁,
      readRegs_reset, stk₂, stk₁, hfinal] using total
  convert total' using 1 ; omega

end SubexponentialSAT.StackRoutines

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

theorem embedState_register_frame {r s R S : ℕ}
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (frame : State R S) (d : State r s) (i : Fin R)
    (hi : ¬ ∃ j, register j = i) :
    (embedState register stack frame d).regs i = frame.regs i :=
  Function.extend_apply' _ _ _ hi

theorem embedState_stack_frame {r s R S : ℕ}
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (frame : State R S) (d : State r s) (i : Fin S)
    (hi : ¬ ∃ j, stack j = i) :
    (embedState register stack frame d).stacks i = frame.stacks i :=
  Function.extend_apply' _ _ _ hi

end SubexponentialSAT.StructuredCalls

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpScanPrimitives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete stack operations used by the serialized coefficient scanner. -/

namespace SubexponentialSAT.SubexpScanPrimitives

open BitProgram StructuredCalls

theorem copy_eval {r s : ℕ} (d : State r s) (src dst tmp : Fin s) (v p : Fin r)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst) (hvp : v ≠ p)
    (htmp : d.stacks tmp = []) :
    Eval (.call (StackRoutines.copyProgram src dst tmp v p))
      (7 * (d.stacks src).length + 5) d (afterCopy d src dst v p) := by
  apply Eval.call
  have ht := StackRoutines.copyProgram_trace src dst tmp v p hsd hst htd hvp
    d.regs d.stacks htmp
  have hh := StackRoutines.halt_after_trace _ ht 7 rfl rfl
  simpa [afterCopy, StackRoutines.copyResult, StructuredProgram.State.withPC,
    StackRoutines.copyProgram, Nat.add_assoc] using hh

theorem transfer_eval {r s : ℕ} (d : State r s) (src dst : Fin s) (v p : Fin r)
    (hsd : src ≠ dst) (hvp : v ≠ p) :
    Eval (.call (StackRoutines.transferProgram src dst v p))
      (3 * (d.stacks src).length + 3) d (afterTransfer d src dst v p) := by
  apply Eval.call
  have ht := StackRoutines.transferProgram_trace src dst v p hsd hvp d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ ht 3 rfl rfl
  simpa [afterTransfer, StackRoutines.transferResult, StructuredProgram.State.withPC,
    StackRoutines.transferProgram, Nat.add_assoc] using hh

def afterCounted {r s : ℕ} (d : State r s) (counter src dst : Fin s) (v p : Fin r)
    (bits rest : List Bool) : State r s :=
  ⟨readRegs d.regs v p none,
    ArrayPrograms.countedTransferStacks counter src dst bits rest d.stacks⟩

end SubexponentialSAT.SubexpScanPrimitives

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_DensePolynomialLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed streaming array loop, parameterized by a finite word program
and an actual trace theorem for one word. The concrete modular-word
instantiation is supplied in DensePolynomialPrograms. -/

namespace SubexponentialSAT.DensePolynomialLoop

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpLiftRing SubexpQuarticRing

structure WordStep (B : ℕ) where
  cmd : Cmd 8 20
  modulus : List Bool
  add : Word B → Word B → Word B
  cost : ℕ
  run : ∀ (regs : Fin 8 → Bool) (x y : Word B)
    (left right width packed : List Bool) (frame : Fin 6 → List Bool),
    width.length = B → ∃ n ≤ cost, ∃ regs',
      Eval cmd n (ready regs modulus (x.val ++ left) (y.val ++ right) width packed frame)
        (ready regs' modulus left right width ((add x y).val.reverse ++ packed) frame)

variable {B : ℕ} (step : WordStep B)

def addWords : List (Word B) → List (Word B) → List (Word B)
  | x :: xs, y :: ys => step.add x y :: addWords xs ys
  | _, _ => []

def addWordsTotal : List (Word (B)) → List (Word (B)) →
    List (Word (B))
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => (step.add x y) :: addWordsTotal xs ys


end SubexponentialSAT.DensePolynomialLoop

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCNFRecords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control skipping of framed CNF records

The program below has three Boolean registers, one Boolean stack, and eleven
fixed labels. It consumes an escaped frame or one tagged list item without
materializing the payload. The payload may itself encode a list of literals,
a clause, or a more deeply nested record. Every bound is proved for actual
`BitProgram.step` traces, rather than assigned to a semantic list operation.
-/

namespace SubexponentialSAT.ExecCNFRecords
open SubexponentialSAT.BitProgram

theorem restoreCaptured_trace (input output scratch : List Bool) (v p : Bool) :
    Trace restoreCapturedProgram (3 * scratch.length + 3)
      (copyCfg (some 0) v p input output scratch)
      (copyCfg none false false input (scratch.reverse ++ output) []) := by
  have h := StackRoutines.transferProgram_trace (r := 2) (s := 3)
    2 1 0 1 (by decide) (by decide) (ParserProgram.pair v p) (ports input output scratch)
  have ht : Trace restoreCapturedProgram (3 * scratch.length + 2)
      (copyCfg (some 0) v p input output scratch)
      (copyCfg (some 3) false false input (scratch.reverse ++ output) []) := by
    simpa [restoreCapturedProgram, copyCfg, StackRoutines.transferResult,
      StackRoutines.transferStacks, readRegs] using h
  have hh : step restoreCapturedProgram
      (copyCfg (some 3) false false input (scratch.reverse ++ output) []) =
      some (copyCfg none false false input (scratch.reverse ++ output) []) := by
    simp [step, copyCfg, execInstr]
  simpa [Nat.add_assoc] using ht.trans (.cons hh (.refl _))

/-- Raw-frame entry 4 copies a frame, including its escapes and delimiter. -/
theorem copy_frame_trace (bits rest output : List Bool) (v p : Bool) :
    Trace copyProgram (13 * bits.length + 11)
      (copyCfg (some 4) v p (Encoding.frame bits ++ rest) output [])
      (copyCfg none false false rest (Encoding.frame bits ++ output) []) := by
  have hp : Trace captureProgram (7 * bits.length + 5)
      (copyCfg (some 4) v p (Encoding.frame bits ++ rest) output [])
      (copyCfg none false true rest output (Encoding.frame bits).reverse) := by
    simpa using capture_frame_trace bits rest output [] v p
  have hq : Trace restoreCapturedProgram (3 * (Encoding.frame bits).length + 3)
      (ProgramLinking.enter restoreCapturedProgram
        (copyCfg (l := 12) none false true rest output (Encoding.frame bits).reverse))
      (copyCfg none false false rest (Encoding.frame bits ++ output) []) := by
    simpa [ProgramLinking.enter, restoreCapturedProgram, StackRoutines.transferProgram, copyCfg]
      using restoreCaptured_trace rest output (Encoding.frame bits).reverse false true
  have h := ProgramLinking.link_trace captureProgram restoreCapturedProgram hp rfl hq
  have hc : (7 * bits.length + 5) + (3 * (Encoding.frame bits).length + 3) =
      13 * bits.length + 11 := by
    simp only [Encoding.length_frame]
    omega
  have hfour : Fin.castAdd 4 (4 : Fin 12) = (4 : Fin 16) := rfl
  simpa only [hc, copyProgram, ProgramLinking.relabelCfg, ProgramLinking.relocatePc,
    copyCfg, hfour]
    using h

end SubexponentialSAT.ExecCNFRecords

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecClauseCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Explicit costs for the executable clause loops

These routines return their result together with the number of charged events
in the displayed recursive execution. A recursive list-case inspection costs
one event; a literal equality test costs one further event. These are list-loop
and comparison units, **not** primitive bit-machine transitions. In particular,
`DecidableEq α` is an equality interface, not a unit-cost bit implementation.
No cost is attached to an arbitrary uninstrumented function.
-/

namespace SubexponentialSAT.ExecClauseCost

universe u v
variable {α : Type u} {β : Type v}

open SubexponentialSAT.BitProgram

theorem bitEquality_runsIn (r : Fin 5 → Bool) (xs ys : List Bool) :
    ∃ c : Cfg 5 2 10,
      RunsIn bitEqualityProgram (9 * (xs.length + 1)) (bitEqualityStart r xs ys) c ∧
      c.pc = none ∧ c.regs 4 = decide (xs = ys) := by
  obtain ⟨n, hn, c, hc, hpc, hout⟩ := bitEquality_runs r xs ys
  exact ⟨c, ⟨n, hn, hc⟩, hpc, hout⟩


/-- The additional size postcondition permits the caller to charge cleanup. -/
theorem bitEquality_runsIn_bounded (r : Fin 5 → Bool) (xs ys : List Bool) :
    ∃ c : Cfg 5 2 10,
      RunsIn bitEqualityProgram (9 * (xs.length + 1)) (bitEqualityStart r xs ys) c ∧
      c.pc = none ∧ c.regs 4 = decide (xs = ys) ∧
      (c.stacks 0).length ≤ xs.length ∧ (c.stacks 1).length ≤ ys.length := by
  obtain ⟨c, ⟨n, hn, ht⟩, hpc, hout⟩ := bitEquality_runsIn r xs ys
  refine ⟨c, ⟨n, hn, ht⟩, hpc, hout, ?_, ?_⟩
  · simpa [bitEqualityStart, bitStacks] using bitEquality_trace_length_le ht 0
  · simpa [bitEqualityStart, bitStacks] using bitEquality_trace_length_le ht 1


end SubexponentialSAT.ExecClauseCost

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecClauseCost39Lift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms
namespace SubexponentialSAT.ExecClauseCost
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem embed_restricted {r s R S : ℕ}
    (reg : Fin r → Fin R) (stk : Fin s → Fin S)
    (hr : Function.Injective reg) (hs : Function.Injective stk)
    (frame : State R S) :
    embedState reg stk frame ⟨frame.regs ∘ reg, frame.stacks ∘ stk⟩ = frame := by
  cases frame with
  | mk regs stkValues =>
    unfold embedState
    congr 1
    · funext i
      by_cases h : ∃ j, reg j = i
      · obtain ⟨j, rfl⟩ := h
        exact hr.extend_apply _ _ _
      · exact Function.extend_apply' _ _ _ h
    · funext i
      by_cases h : ∃ j, stk j = i
      · obtain ⟨j, rfl⟩ := h
        exact hs.extend_apply _ _ _
      · exact Function.extend_apply' _ _ _ h

end SubexponentialSAT.ExecClauseCost

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_RecordPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A reusable actual iterator over the project's framed-record representation.
The callback is a fixed structured program, whose executions are measured in the
same semantics as the parser and iterator. It is never an atomic semantic oracle.
-/

namespace SubexponentialSAT.RecordPrograms

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-- The contract describes measured executions of the fixed callback code.
Only the actual parser and callback execute; the predicate and budget are specs. -/
abbrev CallbackContract {r s : ℕ} (p : Ports r s) (callback : Cmd r s)
    (test : List Bool → Bool) (cost : List Bool → ℕ) (invariant : State r s → Prop) : Prop :=
  ∀ (bits tail : List Bool) (base : State r s), invariant base →
    ∃ (n : ℕ) (next : State r s), n ≤ cost bits ∧ invariant next ∧
      Eval callback n (state p base false true false tail bits.reverse)
        (state p next false true (test bits) tail [])

theorem embed_parserState {r s : ℕ} (p : Ports r s) (base : State r s)
    (v pr f v' pr' : Bool) (src out src' out' : List Bool) :
    embedState (registerMap p) (stackMap p) (state p base v pr f src out)
      (parserState v' pr' src' out') = state p base v' pr' f src' out' := by
  unfold embedState parserState
  change StructuredProgram.State.mk
    (Function.extend (ParserProgram.pair p.tag p.present) (ParserProgram.pair v' pr') _)
    (Function.extend (ParserProgram.pair p.source p.payload) (ParserProgram.pair src' out') _) = _
  rw [extend_pair _ _ p.tag_ne_present, extend_pair _ _ p.source_ne_payload]
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    by_cases ht : i = p.tag <;> by_cases hp : i = p.present <;> by_cases hf : i = p.found <;>
      simp_all [state, Function.update_apply, p.found_ne_tag, p.found_ne_present,
        p.tag_ne_present]
  · funext i
    by_cases hs : i = p.source <;> by_cases hp : i = p.payload <;>
      simp_all [state, Function.update_apply]

/-- The callback receives the reversed payload, with every auxiliary port framed. -/
theorem reader_eval {r s : ℕ} (p : Ports r s) (base : State r s)
    (bits tail out : List Bool) (v pr f : Bool) :
    Eval (reader p) (6 * bits.length + 4)
      (state p base v pr f (Encoding.frame bits ++ tail) out)
      (state p base false true f tail (bits.reverse ++ out)) := by
  have h := eval_call_lifted ParserProgram.frameProgram (registerMap p) (stackMap p)
    (state p base v pr f (Encoding.frame bits ++ tail) out)
    (registerMap_injective p) (stackMap_injective p)
    (a := parserState v pr (Encoding.frame bits ++ tail) out)
    (b := parserState false true tail (bits.reverse ++ out))
    (ParserProgram.frame_trace bits tail out v pr)
  simpa only [embed_parserState, reader] using h

theorem set_found_eval {r s : ℕ} (p : Ports r s) (base : State r s)
    (v pr f f' : Bool) (src out : List Bool) :
    Eval (atom (.set p.found f')) 1 (state p base v pr f src out)
      (state p base v pr f' src out) := by
  have h : (StructuredProgram.Atom.set p.found f').eval (state p base v pr f src out) =
      state p base v pr f' src out := by
    simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, state]
  rw [← h]
  exact .base (.atom _ _)

theorem set_tag_eval {r s : ℕ} (p : Ports r s) (base : State r s)
    (v pr f v' : Bool) (src out : List Bool) :
    Eval (atom (.set p.tag v')) 1 (state p base v pr f src out)
      (state p base v' pr f src out) := by
  have h : (StructuredProgram.Atom.set p.tag v').eval (state p base v pr f src out) =
      state p base v' pr f src out := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      by_cases ht : i = p.tag <;> by_cases hp : i = p.present <;> by_cases hf : i = p.found <;>
        simp_all [ StructuredProgram.Atom.instr, execInstr,
          state, p.found_ne_tag, p.tag_ne_present,
          Ne.symm p.tag_ne_present]
    · rfl
  rw [← h]
  exact .base (.atom _ _)

theorem pop_eval {r s : ℕ} (p : Ports r s) (base : State r s)
    (v pr f b : Bool) (src out : List Bool) :
    Eval (atom (.pop p.source p.tag p.present)) 1 (state p base v pr f (b :: src) out)
      (state p base b true f src out) := by
  have h : (StructuredProgram.Atom.pop p.source p.tag p.present).eval
      (state p base v pr f (b :: src) out) = state p base b true f src out := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      by_cases ht : i = p.tag <;> by_cases hp : i = p.present <;> by_cases hf : i = p.found <;>
        simp_all [ StructuredProgram.Atom.instr, execInstr,
          readRegs, state, p.found_ne_tag, p.found_ne_present,
          p.tag_ne_present, p.source_ne_payload]
    · funext i
      by_cases hs : i = p.source <;> by_cases hp : i = p.payload <;>
        simp_all [ StructuredProgram.Atom.instr, execInstr,
          state, p.source_ne_payload, Ne.symm p.source_ne_payload]
  rw [← h]
  exact .base (.atom _ _)

theorem pop_list_eval {r s : ℕ} (p : Ports r s) (base : State r s)
    (records : List (List Bool)) (suffix : List Bool) (v pr : Bool) :
    Eval (atom (.pop p.source p.tag p.present)) 1
      (state p base v pr false (Encoding.encodeList id records ++ suffix) [])
      (afterTag p base records suffix) := by
  cases records with
  | nil => simpa [Encoding.encodeList, afterTag] using pop_eval p base v pr false false suffix []
  | cons bits rest =>
      simpa [Encoding.encodeList, afterTag, List.append_assoc] using
        pop_eval p base v pr false true
          (Encoding.frame bits ++ (Encoding.encodeList id rest ++ suffix)) []

/-- Measured loop execution, including the final failed loop guard. -/
theorem loop_run {r s : ℕ} (p : Ports r s) (callback : Cmd r s)
    (test : List Bool → Bool) (cost : List Bool → ℕ) (invariant : State r s → Prop)
    (contract : CallbackContract p callback test cost invariant)
    (records : List (List Bool)) (suffix : List Bool) (base : State r s)
    (valid : invariant base) :
    ∃ (n : ℕ) (next : State r s), n ≤ 1 + budget cost records ∧ invariant next ∧
      Eval (loop p callback) n (afterTag p base records suffix)
        (state p next false true (records.any test) (unread test records suffix) []) := by
  induction records generalizing base with
  | nil =>
      refine ⟨1, base, by simp [budget], valid, ?_⟩
      apply Eval.while_false
      simp [afterTag]
  | cons bits rest ih =>
      let tail := Encoding.encodeList id rest ++ suffix
      obtain ⟨n, middle, hn, hmiddle, hcallback⟩ := contract bits tail base valid
      have hreader : Eval (reader p) (6 * bits.length + 4)
          (afterTag p base (bits :: rest) suffix)
          (state p base false true false tail bits.reverse) := by
        simpa [afterTag, tail] using reader_eval p base bits tail [] true true false
      have hguard : (afterTag p base (bits :: rest) suffix).regs p.tag = true := by
        simp [afterTag]
      cases ht : test bits with
      | true =>
          have hbranch : Eval
              (.ite p.found (atom (.set p.tag false)) (atom (.pop p.source p.tag p.present))) 2
              (state p middle false true (test bits) tail [])
              (state p middle false true true tail []) := by
            rw [ht]
            apply Eval.ite_true (by simp)
            exact set_tag_eval p middle false true true false tail []
          have hbody := Eval.seq hreader (Eval.seq hcallback hbranch)
          have hfinish : Eval (loop p callback) 1
              (state p middle false true true tail [])
              (state p middle false true true tail []) :=
            Eval.while_false (by simp)
          have hrun := Eval.while_true hguard hbody hfinish
          refine ⟨(6 * bits.length + 4 + (n + 2)) + 1 + 1, middle, ?_, hmiddle, ?_⟩
          · simp only [budget]
            omega
          · simpa [loop, body, unread, ht, tail] using hrun
      | false =>
          have hbranch : Eval
              (.ite p.found (atom (.set p.tag false)) (atom (.pop p.source p.tag p.present))) 2
              (state p middle false true (test bits) tail [])
              (afterTag p middle rest suffix) := by
            rw [ht]
            apply Eval.ite_false (by simp)
            exact pop_list_eval p middle rest suffix false true
          have hbody := Eval.seq hreader (Eval.seq hcallback hbranch)
          obtain ⟨m, next, hm, hnext, hrest⟩ := ih middle hmiddle
          have hrun := Eval.while_true hguard hbody hrest
          refine ⟨(6 * bits.length + 4 + (n + 2)) + m + 1, next, ?_, hnext, ?_⟩
          · simp only [budget]
            omega
          · simpa [loop, body, unread, ht] using hrun

/-- One fixed iterator handles all record counts and payload lengths. The
bound sums genuine callback executions and parser/guard instructions. -/
theorem iterate_run {r s : ℕ} (p : Ports r s) (callback : Cmd r s)
    (test : List Bool → Bool) (cost : List Bool → ℕ) (invariant : State r s → Prop)
    (contract : CallbackContract p callback test cost invariant)
    (records : List (List Bool)) (suffix : List Bool) (base : State r s)
    (valid : invariant base) (v pr f : Bool) :
    ∃ (n : ℕ) (next : State r s), n ≤ 3 + budget cost records ∧ invariant next ∧
      Eval (iterate p callback) n
        (state p base v pr f (Encoding.encodeList id records ++ suffix) [])
        (state p next false true (records.any test) (unread test records suffix) []) := by
  obtain ⟨n, next, hn, hnext, hloop⟩ := loop_run p callback test cost invariant contract
    records suffix base valid
  refine ⟨1 + (1 + n), next, by omega, hnext, ?_⟩
  exact Eval.seq (set_found_eval p base v pr f false _ [])
    (Eval.seq (pop_list_eval p base records suffix v pr) hloop)

end SubexponentialSAT.RecordPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCNFMembership
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Encoded CNF membership building blocks

Fixed ports: source 0, reversed current payload 1, preserved reversed query 2,
query copy 3, and temporary stack 4. Register 4 is the answer; registers 5 and
6 are the outer-list tag and presence flag. Registers 0--3 are work bits.
-/

namespace SubexponentialSAT.ExecCNFMembership

open SubexponentialSAT.BitProgram
open SubexponentialSAT.StructuredCalls

theorem copyQuery_eval (d : Data) (htmp : d.stacks 4 = []) :
    Eval copyQuery (7 * (d.stacks 2).length + 5) d (copied d) := by
  have h := StackRoutines.copyProgram_trace (r := 7) (s := 5)
    2 3 4 0 1 (by decide) (by decide) (by decide) (by decide) d.regs d.stacks htmp
  have hh : step copyQueryProgram
      (StackRoutines.copyResult 7 2 3 0 1 d.regs d.stacks) =
      some ((copied d).withPC none) := by
    simp [step, StackRoutines.copyResult,
      copied, StructuredProgram.State.withPC, execInstr]
  apply Eval.call
  change Computation.Trace (step copyQueryProgram) (7 * (d.stacks 2).length + 5)
    (d.withPC (some 0)) ((copied d).withPC none)
  exact h.trans (.cons hh (.refl _))

/-- Clearing is an actual two-instruction loop followed by a halt/return. -/
abbrev clearProgram (port : Fin 5) : Program 7 5 3 := StackRoutines.clearProgram port 0 1

abbrev clear (port : Fin 5) : Cmd 7 5 := .call (clearProgram port)


/-- Compare the parsed reversed payload against a fresh copy of the query,
then clear both inspected work strings, including early-mismatch residuals. -/
abbrev callback : Cmd 7 5 :=
  .seq copyQuery
    (.seq (.call SubexponentialSAT.ExecClauseCost.membershipEqProgram) (.seq (clear 1) (clear 3)))


/-- The emitted bit is in stack 1. The encoded source is scanned destructively,
while stack 2 retains the reversed runtime query. -/
abbrev membership : Cmd 7 5 :=
  .seq (RecordPrograms.iterate ports callback) (RecordPrograms.atom (.push 1 4))

theorem emit_eval (base : Data) (answer : Bool) (source : List Bool) :
    Eval (RecordPrograms.atom (.push 1 4)) 1
      (RecordPrograms.state ports base false true answer source [])
      (RecordPrograms.state ports base false true answer source [answer]) := by
  have h : (StructuredProgram.Atom.push (r := 7) (s := 5) 1 4).eval
      (RecordPrograms.state ports base false true answer source []) =
      RecordPrograms.state ports base false true answer source [answer] := by
    simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr,
      RecordPrograms.state ]
  rw [← h]
  exact .base (.atom _ _)

/-- This instruction table has fixed size, independent of both runtime inputs. -/
def membershipProgram := compiled membership 0 1

end SubexponentialSAT.ExecCNFMembership

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCNFSubset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual encoded clause subset testing

The fixed program uses ten Boolean registers and eight Boolean stacks. The
source clause is scanned destructively on stack 0. Stack 2 preserves the entire
encoded target clause. All comparisons use the proved encoded membership
program, after a real preserving copy of the target.
-/
namespace SubexponentialSAT.ExecCNFSubset
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev clearProgram (port : Fin 8) : Program 10 8 3 := StackRoutines.clearProgram port 0 1

abbrev clear (port : Fin 8) : Cmd 10 8 := .call (clearProgram port)

def memberProgram := ProgramLinking.liftProgram
  ExecCNFMembership.membershipProgram memberReg memberStack

abbrev memberCall : Cmd 10 8 := .call memberProgram

theorem embed_restricted {r s R S : ℕ}
    (reg : Fin r → Fin R) (stk : Fin s → Fin S)
    (hr : Function.Injective reg) (hs : Function.Injective stk)
    (frame : State R S) :
    embedState reg stk frame ⟨frame.regs ∘ reg, frame.stacks ∘ stk⟩ = frame := by
  cases frame with
  | mk regs stkValues =>
    unfold embedState
    congr 1
    · funext i
      by_cases h : ∃ j, reg j = i
      · obtain ⟨j, rfl⟩ := h
        exact hr.extend_apply _ _ _
      · exact Function.extend_apply' _ _ _ h
    · funext i
      by_cases h : ∃ j, stk j = i
      · obtain ⟨j, rfl⟩ := h
        exact hs.extend_apply _ _ _
      · exact Function.extend_apply' _ _ _ h

/-- Each source literal invokes a real copy, encoded membership scan, and three
cleanup loops. The instruction sequence is independent of both clauses. -/
abbrev callback : Cmd 10 8 :=
  .seq copyTarget (.seq memberCall
    (.seq (RecordPrograms.atom (.bnot 9 4)) (.seq (clear 3) (.seq (clear 4) (clear 1)))))

abbrev subset : Cmd 10 8 := .seq (RecordPrograms.iterate ports callback) finish

end SubexponentialSAT.ExecCNFSubset

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNormalizeProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Concrete syntax routines for CNF normalization

This module begins the machine implementation of normalization with the
complement-query operation used in tautology testing. `negateProgram` is one
fixed finite instruction table. It scans a unary literal code in pairs and
emits the code with its polarity flipped. Unbounded data stays on the stacks.

The theorems count actual `BitProgram.step` transitions. Full formula
deduplication, tautology filtering, and absorption are separate obligations;
this routine is not presented as the completed normalization algorithm.
-/

namespace SubexponentialSAT.SubexpNormalizeProgram

open BitProgram
open ParserProgram (cfg)

/-! ## Actual record-filter output step

The predicate's result occupies register 2. The following fixed callback
consumes the reversed record on stack 3, prepends its framed representation to
stack 2 exactly when selected, and resets the iterator's flags. Its two other
stacks are preserved. Computing the selection bit is a separate operation.
-/

abbrev discardRecordProgram : Program 3 4 3 := StackRoutines.clearProgram 3 0 1

/-! ## A complete record-order reversal pass

Prepending accepted records reverses their order. This second, unconditional
pass restores the order required by `List.filter` and the executable
sparsifier. It reverses the records, never the bits within a record.
-/

/-! ## Exact-order contract for the full normalization filter

The selection callback in the following theorem is a fixed structured
program with measured executions. No procedure is manufactured from the
mathematical predicate. Once that callback is supplied, the theorem tracks
the output of the actual generic record iterator, including record order.
-/

end SubexponentialSAT.SubexpNormalizeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecClauseRelationsProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Preserving encoded clause relations

Two invocations of the concrete subset tester compute equivalence and strict
inclusion. The original encoded clauses occupy stacks 8 and 9 throughout;
stacks 0 through 7 are empty workspace at both boundaries. Registers 10 and
11 return equivalence and strict inclusion, respectively.
-/

namespace SubexponentialSAT.ExecClauseRelationsProgram

open BitProgram StructuredCalls

def combined (d : Data) : Data :=
  (StructuredProgram.Atom.band 11 11 9).eval
    ((StructuredProgram.Atom.bnot 9 9).eval ((StructuredProgram.Atom.band 10 11 9).eval d))

@[simp] theorem combined_stacks (d : Data) : (combined d).stacks = d.stacks := rfl

@[simp] theorem combined_equivalent (d : Data) :
    (combined d).regs 10 = (d.regs 11 && d.regs 9) := by
  simp [combined, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr]

@[simp] theorem combined_strict (d : Data) :
    (combined d).regs 11 = (d.regs 11 && !d.regs 9) := by
  simp [combined, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr]

@[simp] theorem combined_reverse (d : Data) : (combined d).regs 9 = !d.regs 9 := by
  simp [combined, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr]

end SubexponentialSAT.ExecClauseRelationsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecClauseFiltersProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Exact-order clause filters on encoded formulas

The relation scanner occupies stacks 0--12. The outer record pass uses stack
13 for unread records, stack 14 for the reversed output record list, and stack
15 for the reversed current payload. Two stack transfers put a clause into the
scanner and return it to the existing frame emitter.
-/


namespace SubexponentialSAT.ExecClauseFiltersProgram

open BitProgram StructuredCalls
open ExecClauseRelationScan (Clause Formula Mode encodeClause encodeFormula test)

abbrev Data := StructuredProgram.State 15 16

def state (regs : Regs) (query answer master source output payload : List Bool) : Data :=
  ⟨regs, ![[], [], [], [], [], [], [], [], [], query, [], answer, master,
    source, output, payload]⟩

end SubexponentialSAT.ExecClauseFiltersProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecClauseDedupProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed program for last-occurrence clause deduplication

The current clause is compared with the unread suffix using actual set
equivalence of its literal records. The suffix copy is cleared after each
query, and the final record reversal restores the prescribed clause order.
-/

namespace SubexponentialSAT.ExecClauseDedupProgram

open BitProgram StructuredCalls
open ExecClauseRelationScan (Clause Formula encodeClause encodeFormula)
open ExecClauseFiltersProgram (Regs Data state reset flags)

def Clean (d : Data) : Prop := ∀ i : Fin 13, d.stacks (workPort i) = []

@[simp] theorem clean_state (base : Data) (v pr f : Bool) (src payload : List Bool) :
    Clean (RecordPrograms.state ports base v pr f src payload) ↔ Clean base := by
  simp [Clean, RecordPrograms.state, ports]

@[simp] theorem state_output (base : Data) (v pr f : Bool) (src payload : List Bool) :
    (RecordPrograms.state ports base v pr f src payload).stacks 14 = base.stacks 14 := by
  simp [RecordPrograms.state, ports]

end SubexponentialSAT.ExecClauseDedupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ModularPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Finite Boolean-stack programs for modular arithmetic

The programs in this file use only a fixed finite collection of labels,
Boolean registers, and Boolean stacks. The operand width and modulus are data.
-/

namespace SubexponentialSAT.ModularPrograms

open SubexponentialSAT.BitProgram SubexponentialSAT.ModularArithmetic

/-! Preserve a candidate word while subtracting a modulus from its copy. -/

theorem embed_subtract (pc : Option (Fin 13)) (regs : Fin 8 → Bool)
    (saved left right output : List Bool) :
    SubexponentialSAT.ProgramLinking.embedCfg id subtractionPorts id none
      (⟨none, regs, wideStacks saved [] [] []⟩ : Cfg 8 5 13)
      (subtractCfg pc regs left right output) =
      (⟨pc, regs, wideStacks saved left right output⟩ : Cfg 8 5 13) := by
  classical
  suffices hpc :
      (SubexponentialSAT.ProgramLinking.embedCfg id subtractionPorts id none
        (⟨none, regs, wideStacks saved [] [] []⟩ : Cfg 8 5 13)
        (subtractCfg pc regs left right output)).pc = pc by
    suffices hregs :
        (SubexponentialSAT.ProgramLinking.embedCfg id subtractionPorts id none
          (⟨none, regs, wideStacks saved [] [] []⟩ : Cfg 8 5 13)
          (subtractCfg pc regs left right output)).regs = regs by
      suffices hstk :
          (SubexponentialSAT.ProgramLinking.embedCfg id subtractionPorts id none
            (⟨none, regs, wideStacks saved [] [] []⟩ : Cfg 8 5 13)
            (subtractCfg pc regs left right output)).stacks =
              wideStacks saved left right output by
        cases he : SubexponentialSAT.ProgramLinking.embedCfg id subtractionPorts id none
            (⟨none, regs, wideStacks saved [] [] []⟩ : Cfg 8 5 13)
            (subtractCfg pc regs left right output)
        simp_all
      funext k
      fin_cases k
      · exact SubexponentialSAT.ProgramLinking.embedCfg_stack_frame id subtractionPorts id none
          _ _ 0 (by decide)
      · simpa [subtractionPorts, subtractCfg, wideStacks, operandStacks] using
          SubexponentialSAT.ProgramLinking.embedCfg_stack id subtractionPorts id none
            (⟨none, regs, wideStacks saved [] [] []⟩ : Cfg 8 5 13)
            (subtractCfg pc regs left right output) subtractionPorts_injective (1 : Fin 3)
      · simpa [subtractionPorts, subtractCfg, wideStacks, operandStacks] using
          SubexponentialSAT.ProgramLinking.embedCfg_stack id subtractionPorts id none
            (⟨none, regs, wideStacks saved [] [] []⟩ : Cfg 8 5 13)
            (subtractCfg pc regs left right output) subtractionPorts_injective (0 : Fin 3)
      · simpa [subtractionPorts, subtractCfg, wideStacks, operandStacks] using
          SubexponentialSAT.ProgramLinking.embedCfg_stack id subtractionPorts id none
            (⟨none, regs, wideStacks saved [] [] []⟩ : Cfg 8 5 13)
            (subtractCfg pc regs left right output) subtractionPorts_injective (2 : Fin 3)
      · exact SubexponentialSAT.ProgramLinking.embedCfg_stack_frame id subtractionPorts id none
          _ _ 4 (by decide)
    simp [SubexponentialSAT.ProgramLinking.embedCfg ]
  cases pc <;> rfl

theorem subtractWide_correct (regs : Fin 8 → Bool)
    (saved xs ys : List Bool) (hlen : xs.length = ys.length) :
    ∃ finalRegs : Fin 8 → Bool,
      Trace subtractWideProgram (12 * xs.length + 3)
        ⟨some 0, regs, wideStacks saved xs ys []⟩
        ⟨none, finalRegs, wideStacks saved [] [] (subCarry (regs 0) xs ys).1.reverse⟩ ∧
      finalRegs 0 = (subCarry (regs 0) xs ys).2 := by
  obtain ⟨finalRegs, hrun, hborrow⟩ := subtract_correct regs xs ys [] hlen
  have hw := SubexponentialSAT.ProgramLinking.relocate_trace subtractProgram subtractWideProgram
    id subtractionPorts id none
    (⟨none, regs, wideStacks saved [] [] []⟩ : Cfg 8 5 13)
    Function.injective_id subtractionPorts_injective (fun _ => rfl) hrun
  refine ⟨finalRegs, ?_, hborrow⟩
  have hstart := embed_subtract (some 0) regs saved xs ys []
  rw [hstart] at hw
  have hend :
      SubexponentialSAT.ProgramLinking.embedCfg id subtractionPorts id none
        (⟨none, regs, wideStacks saved [] [] []⟩ : Cfg 8 5 13)
        (subtractCfg none finalRegs [] [] ((subCarry (regs 0) xs ys).1.reverse ++ [])) =
        (⟨none, finalRegs, wideStacks saved [] [] (subCarry (regs 0) xs ys).1.reverse⟩ :
          Cfg 8 5 13) := by
    have h := embed_subtract none finalRegs saved [] []
      (subCarry (regs 0) xs ys).1.reverse
    simpa [SubexponentialSAT.ProgramLinking.embedCfg, subtractCfg] using h
  rwa [hend] at hw

theorem copyAndSubtract_correct (regs : Fin 8 → Bool)
    (candidate modulus : List Bool) (hlen : candidate.length = modulus.length) :
    ∃ finalRegs : Fin 8 → Bool,
      Trace copyAndSubtractProgram (19 * candidate.length + 8)
        ⟨some 0, regs, wideStacks candidate [] modulus []⟩
        ⟨none, finalRegs, wideStacks candidate [] []
          (subCarry (regs 0) candidate modulus).1.reverse⟩ ∧
      finalRegs 0 = (subCarry (regs 0) candidate modulus).2 := by
  have hc := SubexponentialSAT.StackRoutines.copyProgram_trace
    (0 : Fin 5) 2 4 (1 : Fin 8) 3 (by decide) (by decide) (by decide)
    (by decide) regs (wideStacks candidate [] modulus []) (by simp [wideStacks])
  have hh := SubexponentialSAT.StackRoutines.halt_after_trace copyCandidateProgram hc
    (7 : Fin 8) rfl rfl
  have hh' : Trace copyCandidateProgram (7 * candidate.length + 5)
      ⟨some 0, regs, wideStacks candidate [] modulus []⟩
      ⟨none, readRegs regs 1 3 none, wideStacks candidate candidate modulus []⟩ := by
    simpa [SubexponentialSAT.StackRoutines.copyResult, copy_candidate, wideStacks, Nat.add_assoc]
      using hh
  obtain ⟨finalRegs, hs, hb⟩ := subtractWide_correct
    (readRegs regs 1 3 none) candidate candidate modulus hlen
  have hs' : Trace subtractWideProgram (12 * candidate.length + 3)
      (SubexponentialSAT.ProgramLinking.enter subtractWideProgram
        (⟨none, readRegs regs 1 3 none,
          wideStacks candidate candidate modulus []⟩ : Cfg 8 5 8))
      ⟨none, finalRegs, wideStacks candidate [] []
        (subCarry (regs 0) candidate modulus).1.reverse⟩ := by
    simpa [SubexponentialSAT.ProgramLinking.enter, subtractWideProgram, readRegs] using hs
  have ht := SubexponentialSAT.ProgramLinking.link_trace copyCandidateProgram
    subtractWideProgram hh' rfl hs'
  refine ⟨finalRegs, ?_, ?_⟩
  · convert ht using 1
    · omega
    · rfl
    · rfl
  · simpa [readRegs] using hb

theorem selectDifference_borrow (regs : Fin 8 → Bool)
    (candidate difference : List Bool) (hborrow : regs 0 = true) :
    Trace selectDifferenceProgram (2 * difference.length + 4)
      ⟨some 0, regs, wideStacks candidate [] [] difference⟩
      ⟨none, readRegs regs 1 3 none, wideStacks candidate [] [] []⟩ := by
  have hc := SubexponentialSAT.StackRoutines.clear_trace selectDifferenceProgram
    (3 : Fin 5) (1 : Fin 8) 3 1 2 9 rfl rfl
    regs (wideStacks candidate [] [] difference)
  have hh := SubexponentialSAT.StackRoutines.halt_after_trace selectDifferenceProgram hc
    (9 : Fin 10) rfl rfl
  have ht := SubexponentialSAT.Computation.Trace.cons
    (a := (⟨some 0, regs, wideStacks candidate [] [] difference⟩ : Cfg 8 5 10))
    (by simp [step, execInstr, hborrow]) hh
  simpa [SubexponentialSAT.StackRoutines.clearResult, clear_difference, wideStacks, Nat.add_assoc]
    using ht

theorem selectDifference_noBorrow (regs : Fin 8 → Bool)
    (candidate difference : List Bool) (hborrow : regs 0 = false) :
    Trace selectDifferenceProgram (2 * candidate.length + 3 * difference.length + 6)
      ⟨some 0, regs, wideStacks candidate [] [] difference⟩
      ⟨none, readRegs regs 1 3 none, wideStacks difference.reverse [] [] []⟩ := by
  have hc := SubexponentialSAT.StackRoutines.clear_trace selectDifferenceProgram
    (0 : Fin 5) (1 : Fin 8) 3 3 4 5 rfl rfl
    regs (wideStacks candidate [] [] difference)
  have hc' : Trace selectDifferenceProgram (2 * candidate.length + 2)
      ⟨some 3, regs, wideStacks candidate [] [] difference⟩
      ⟨some 5, readRegs regs 1 3 none, wideStacks [] [] [] difference⟩ := by
    simpa [SubexponentialSAT.StackRoutines.clearResult, clear_candidate, wideStacks] using hc
  have hm := SubexponentialSAT.StackRoutines.transfer_trace selectDifferenceProgram
    (3 : Fin 5) 0 (1 : Fin 8) 3 5 6 7 9 (by decide) (by decide)
    rfl rfl rfl (readRegs regs 1 3 none) (wideStacks [] [] [] difference)
  have hh := SubexponentialSAT.StackRoutines.halt_after_trace selectDifferenceProgram hm
    (9 : Fin 10) rfl rfl
  have hh' : Trace selectDifferenceProgram (3 * difference.length + 3)
      ⟨some 5, readRegs regs 1 3 none, wideStacks [] [] [] difference⟩
      ⟨none, readRegs regs 1 3 none, wideStacks difference.reverse [] [] []⟩ := by
    simpa [SubexponentialSAT.StackRoutines.transferResult, transfer_difference, wideStacks,
      SubexponentialSAT.StackRoutines.readRegs_reset, Nat.add_assoc] using hh
  have ht := SubexponentialSAT.Computation.Trace.cons
    (a := (⟨some 0, regs, wideStacks candidate [] [] difference⟩ : Cfg 8 5 10))
    (by simp [step, execInstr, hborrow]) (hc'.trans hh')
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  omega

theorem conditionalSubtract_correct (regs : Fin 8 → Bool) (hzero : regs 0 = false)
    (candidate modulus : List Bool) (hlen : candidate.length = modulus.length) :
    ∃ finalRegs : Fin 8 → Bool,
      RunsIn conditionalSubtractProgram (24 * candidate.length + 14)
        ⟨some 0, regs, wideStacks candidate [] modulus []⟩
        ⟨none, finalRegs,
          wideStacks (conditionalDifference candidate modulus) [] [] []⟩ ∧
      finalRegs 0 = (subCarry false candidate modulus).2 := by
  obtain ⟨midRegs, hp, hb⟩ := copyAndSubtract_correct regs candidate modulus hlen
  rw [hzero] at hp hb
  refine ⟨readRegs midRegs 1 3 none, ?_, ?_⟩
  · cases hd : (subCarry false candidate modulus).2
    · have hs := selectDifference_noBorrow midRegs candidate
        (subCarry false candidate modulus).1.reverse (hb.trans hd)
      have ht := SubexponentialSAT.ProgramLinking.link_trace copyAndSubtractProgram
        selectDifferenceProgram hp rfl hs
      refine ⟨19 * candidate.length + 8 +
        (2 * candidate.length + 3 * (subCarry false candidate modulus).1.reverse.length + 6),
        ?_, ?_⟩
      · simp only [List.length_reverse, subCarry_length _ _ _ hlen]
        omega
      · simpa [conditionalSubtractProgram, conditionalDifference, hd,
          SubexponentialSAT.ProgramLinking.relabelCfg, SubexponentialSAT.ProgramLinking.relocatePc]
          using ht
    · have hs := selectDifference_borrow midRegs candidate
        (subCarry false candidate modulus).1.reverse (hb.trans hd)
      have ht := SubexponentialSAT.ProgramLinking.link_trace copyAndSubtractProgram
        selectDifferenceProgram hp rfl hs
      refine ⟨19 * candidate.length + 8 +
        (2 * (subCarry false candidate modulus).1.reverse.length + 4), ?_, ?_⟩
      · simp only [List.length_reverse, subCarry_length _ _ _ hlen]
        omega
      · simpa [conditionalSubtractProgram, conditionalDifference, hd,
          SubexponentialSAT.ProgramLinking.relabelCfg, SubexponentialSAT.ProgramLinking.relocatePc]
          using ht
  · simpa [readRegs] using hb

end SubexponentialSAT.ModularPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ModularDivisionPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A finite binary long-division program

The modulus and dividend are Boolean words stored on stacks. Every routine below
has a fixed finite table, independently of the lengths and values of these words.
-/

namespace SubexponentialSAT.ModularDivisionPrograms

open SubexponentialSAT.BitProgram SubexponentialSAT.ModularArithmetic SubexponentialSAT.ModularPrograms
open SubexponentialSAT.ProgramLinking SubexponentialSAT.StackRoutines

theorem embed_ports {s S l : ℕ}
    (port : Fin s → Fin S) (hinj : Function.Injective port)
    (pc : Option (Fin l)) (regs frameRegs : Fin 8 → Bool)
    (localStk : Fin s → List Bool) (frame target : Fin S → List Bool)
    (hport : ∀ i, target (port i) = localStk i)
    (hframe : ∀ i, (¬ ∃ j, port j = i) → target i = frame i) :
    embedCfg id port id none (⟨none, frameRegs, frame⟩ : Cfg 8 S l)
      ⟨pc, regs, localStk⟩ = ⟨pc, regs, target⟩ := by
  apply cfg_ext
  · cases pc <;> rfl
  · simp [embedCfg]
  · funext i
    classical
    by_cases hi : ∃ j, port j = i
    · obtain ⟨j, rfl⟩ := hi
      exact (embedCfg_stack id port id none _ _ hinj j).trans (hport j).symm
    · exact (embedCfg_stack_frame id port id none _ _ i hi).trans (hframe i hi).symm

theorem sequence_trace {r s l m n k : ℕ}
    (p : Program r s l) (q : Program r s m)
    (ra rb rc : Fin r → Bool) (sa sb sc : Fin s → List Bool)
    (hp : Trace p n ⟨some p.entry, ra, sa⟩ ⟨none, rb, sb⟩)
    (hq : Trace q k ⟨some q.entry, rb, sb⟩ ⟨none, rc, sc⟩) :
    Trace (link p q) (n + k)
      ⟨some (link p q).entry, ra, sa⟩ ⟨none, rc, sc⟩ := by
  exact link_trace p q hp rfl hq

theorem sequence_runs {r s l m n k : ℕ}
    (p : Program r s l) (q : Program r s m)
    (ra rb rc : Fin r → Bool) (sa sb sc : Fin s → List Bool)
    (hp : RunsIn p n ⟨some p.entry, ra, sa⟩ ⟨none, rb, sb⟩)
    (hq : RunsIn q k ⟨some q.entry, rb, sb⟩ ⟨none, rc, sc⟩) :
    RunsIn (link p q) (n + k)
      ⟨some (link p q).entry, ra, sa⟩ ⟨none, rc, sc⟩ := by
  exact link_runsIn p q hp rfl hq

theorem embed_padding (pc : Option (Fin 5)) (regs frameRegs : Fin 8 → Bool)
    (candidate modulus input shape word output : List Bool) :
    embedCfg id paddingPorts id none
      (⟨none, frameRegs, resting candidate modulus input⟩ : Cfg 8 7 5)
      (paddingCfg pc regs shape word output) =
      ⟨pc, regs, seven candidate modulus input word shape output []⟩ := by
  apply embed_ports paddingPorts paddingPorts_injective
  · intro i
    fin_cases i <;> rfl
  · intro i hi
    fin_cases i
    · rfl
    · exact False.elim (hi ⟨1, rfl⟩)
    · exact False.elim (hi ⟨0, rfl⟩)
    · exact False.elim (hi ⟨2, rfl⟩)
    · rfl
    · rfl
    · rfl

theorem paddingWide_correct (regs : Fin 8 → Bool)
    (candidate modulus input shape word : List Bool)
    (hlen : word.length ≤ shape.length) :
    ∃ finalRegs : Fin 8 → Bool,
      Trace paddingWideProgram (4 * shape.length + 3)
        ⟨some 0, regs, seven candidate modulus input word shape [] []⟩
        ⟨none, finalRegs,
          seven candidate modulus input [] [] (padTo shape word).reverse []⟩ := by
  obtain ⟨finalRegs, ht, _⟩ := padding_correct regs shape word [] hlen
  have hw := liftProgram_trace paddingProgram id paddingPorts
    (⟨none, regs, resting candidate modulus input⟩ : Cfg 8 7 5)
    Function.injective_id paddingPorts_injective ht
  rw [embed_padding, embed_padding] at hw
  exact ⟨finalRegs, by simpa [paddingWideProgram] using hw⟩

theorem embed_conditional (pc : Option (Fin 31)) (regs frameRegs : Fin 8 → Bool)
    (candidate modulus input left right output : List Bool) :
    embedCfg id conditionalPorts id none
      (⟨none, frameRegs, resting [] modulus input⟩ : Cfg 8 7 31)
      ⟨pc, regs, wideStacks candidate left right output⟩ =
      ⟨pc, regs, seven candidate modulus input right left output []⟩ := by
  apply embed_ports conditionalPorts conditionalPorts_injective
  · intro i
    fin_cases i <;> rfl
  · intro i hi
    fin_cases i
    · exact False.elim (hi ⟨0, rfl⟩)
    · exact False.elim (hi ⟨1, rfl⟩)
    · exact False.elim (hi ⟨2, rfl⟩)
    · exact False.elim (hi ⟨3, rfl⟩)
    · exact False.elim (hi ⟨4, rfl⟩)
    · rfl
    · rfl

theorem conditionalWide_correct (regs : Fin 8 → Bool) (hzero : regs 0 = false)
    (candidate modulus input padded : List Bool)
    (hlen : candidate.length = padded.length) :
    ∃ finalRegs : Fin 8 → Bool,
      RunsIn conditionalWideProgram (24 * candidate.length + 14)
        ⟨some 0, regs, seven candidate modulus input padded [] [] []⟩
        ⟨none, finalRegs,
          resting (conditionalDifference candidate padded) modulus input⟩ := by
  obtain ⟨finalRegs, ht, _⟩ := conditionalSubtract_correct regs hzero candidate padded hlen
  have hw := liftProgram_runsIn conditionalSubtractProgram id conditionalPorts
    (⟨none, regs, resting [] modulus input⟩ : Cfg 8 7 31)
    Function.injective_id conditionalPorts_injective ht
  rw [embed_conditional, embed_conditional] at hw
  exact ⟨finalRegs, hw⟩

theorem preparePadding_correct (regs : Fin 8 → Bool)
    (candidate modulus input : List Bool) (hlen : modulus.length ≤ candidate.length) :
    ∃ finalRegs : Fin 8 → Bool,
      Trace preparePaddingProgram (14 * candidate.length + 7 * modulus.length + 16)
        ⟨some 0, regs, resting candidate modulus input⟩
        ⟨none, finalRegs,
          seven candidate modulus input (padTo candidate modulus) [] [] []⟩ := by
  let r1 := readRegs regs 1 3 none
  have hc1 := copyProgram_trace (0 : Fin 7) 2 4 (1 : Fin 8) 3
    (by decide) (by decide) (by decide) (by decide)
    regs (resting candidate modulus input) (by rfl)
  have hh1 := halt_after_trace copyShapeProgram hc1 (7 : Fin 8) rfl rfl
  have h1 : Trace copyShapeProgram (7 * candidate.length + 5)
      ⟨some 0, regs, resting candidate modulus input⟩
      ⟨none, r1, seven candidate modulus input [] candidate [] []⟩ := by
    simp only [copyResult, copy_shape] at hh1
    simpa [r1, resting, seven, Nat.add_assoc] using hh1
  have hc2 := copyProgram_trace (5 : Fin 7) 1 4 (1 : Fin 8) 3
    (by decide) (by decide) (by decide) (by decide)
    r1 (seven candidate modulus input [] candidate [] []) (by rfl)
  have hh2 := halt_after_trace copyModulusProgram hc2 (7 : Fin 8) rfl rfl
  have h2 : Trace copyModulusProgram (7 * modulus.length + 5)
      ⟨some 0, r1, seven candidate modulus input [] candidate [] []⟩
      ⟨none, r1, seven candidate modulus input modulus candidate [] []⟩ := by
    simp only [copyResult, copy_modulus] at hh2
    simpa [r1, readRegs_reset, seven, Nat.add_assoc] using hh2
  obtain ⟨r2, h3⟩ := paddingWide_correct r1 candidate modulus input candidate modulus hlen
  let r3 := readRegs r2 1 3 none
  have hc4 := transferProgram_trace (3 : Fin 7) 1 (1 : Fin 8) 3
    (by decide) (by decide) r2
    (seven candidate modulus input [] [] (padTo candidate modulus).reverse [])
  have hh4 := halt_after_trace movePaddingProgram hc4 (3 : Fin 4) rfl rfl
  have h4 : Trace movePaddingProgram (3 * candidate.length + 3)
      ⟨some 0, r2, seven candidate modulus input [] [] (padTo candidate modulus).reverse []⟩
      ⟨none, r3, seven candidate modulus input (padTo candidate modulus) [] [] []⟩ := by
    simp only [transferResult, move_padding] at hh4
    simpa [r3, seven, padTo_length, Nat.add_assoc] using hh4
  have h12 := sequence_trace copyShapeProgram copyModulusProgram _ _ _ _ _ _ h1 h2
  have h123 := sequence_trace _ paddingWideProgram _ _ _ _ _ _ h12 h3
  have h1234 := sequence_trace _ movePaddingProgram _ _ _ _ _ _ h123 h4
  refine ⟨r3, ?_⟩
  convert h1234 using 1
  · ring
  · apply cfg_ext
    · congr 1
    · rfl
    · rfl

theorem resetBorrow_correct (regs : Fin 8 → Bool) (stk : Fin 7 → List Bool) :
    Trace resetBorrowProgram 2
      ⟨some 0, regs, stk⟩ ⟨none, Function.update regs 0 false, stk⟩ := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, execInstr, resetBorrowProgram]

theorem reductionStep_correct (regs : Fin 8 → Bool)
    (candidate modulus input : List Bool) (hlen : modulus.length ≤ candidate.length) :
    ∃ finalRegs : Fin 8 → Bool,
      RunsIn reductionStepProgram (38 * candidate.length + 7 * modulus.length + 32)
        ⟨some 0, regs, resting candidate modulus input⟩
        ⟨none, finalRegs,
          resting (conditionalDifference candidate (padTo candidate modulus)) modulus input⟩ := by
  obtain ⟨r1, h1⟩ := preparePadding_correct regs candidate modulus input hlen
  have h2 := resetBorrow_correct r1
    (seven candidate modulus input (padTo candidate modulus) [] [] [])
  obtain ⟨r3, h3⟩ := conditionalWide_correct (Function.update r1 0 false) (by simp)
    candidate modulus input (padTo candidate modulus) (padTo_length _ _).symm
  have h12 := sequence_trace preparePaddingProgram resetBorrowProgram _ _ _ _ _ _ h1 h2
  have h123 := sequence_runs _ conditionalWideProgram _ _ _ _ _ _
    ⟨_, le_rfl, h12⟩ h3
  refine ⟨r3, ?_⟩
  convert h123 using 1
  · ring
  · apply cfg_ext
    · congr 1
    · rfl
    · rfl

theorem loop_step_code :
    CodeEmbedding reductionStepProgram divisionLoopProgram
      id id (Fin.natAdd 4) (some 0) := by
  intro pc
  simp [divisionLoopProgram]

theorem divisionLoop_iteration (regs : Fin 8 → Bool)
    (candidate modulus input : List Bool) (b : Bool)
    (hlen : modulus.length ≤ candidate.length) :
    ∃ finalRegs : Fin 8 → Bool,
      RunsIn divisionLoopProgram (38 * (candidate.length + 1) + 7 * modulus.length + 35)
        ⟨some 0, regs, resting candidate modulus (b :: input)⟩
        ⟨some 0, finalRegs, resting (shiftReduce modulus candidate b) modulus input⟩ := by
  obtain ⟨finalRegs, hrun⟩ := reductionStep_correct
    (readRegs regs 1 3 (some b)) (b :: candidate) modulus input (by simpa using hlen.trans (Nat.le_succ _))
  have hw := relocate_runsIn reductionStepProgram divisionLoopProgram
    id id (Fin.natAdd 4) (some 0)
    (⟨none, regs, resting candidate modulus input⟩ : Cfg 8 7 62)
    Function.injective_id Function.injective_id loop_step_code hrun
  have hw' : RunsIn divisionLoopProgram
      (38 * (candidate.length + 1) + 7 * modulus.length + 32)
      ⟨some 4, readRegs regs 1 3 (some b), resting (b :: candidate) modulus input⟩
      ⟨some 0, finalRegs, resting (shiftReduce modulus candidate b) modulus input⟩ := by
    simpa [embedCfg_id, relabelCfg, relocatePc, shiftReduce, conditionalDifference] using hw
  have hh := divisionLoop_head regs candidate modulus input b
  have ht := (SubexponentialSAT.Computation.RunsIn.trans
    (⟨3, le_rfl, hh⟩ : RunsIn divisionLoopProgram 3 _ _) hw')
  refine ⟨finalRegs, ?_⟩
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  omega

theorem reduceFrom_reverse (modulus input : List Bool) :
    reduceFrom modulus (padTo modulus []) input.reverse = reduce modulus input := by
  induction input with
  | nil => rfl
  | cons b bs ih =>
    simp [List.reverse_cons, reduceFrom_append, reduceFrom, reduce, ih]

theorem divisionLoop_correct (regs : Fin 8 → Bool)
    (candidate modulus input : List Bool) (hlen : modulus.length ≤ candidate.length) :
    ∃ finalRegs : Fin 8 → Bool,
      RunsIn divisionLoopProgram
        (50 * (input.length + 1) * (candidate.length + modulus.length + input.length + 1))
        ⟨some 0, regs, resting candidate modulus input⟩
        ⟨none, finalRegs, resting (reduceFrom modulus candidate input) modulus []⟩ := by
  induction input generalizing regs candidate with
  | nil =>
    refine ⟨readRegs regs 1 3 none, 3, ?_, divisionLoop_exit regs candidate modulus⟩
    simp only [List.length_nil]
    omega
  | cons b bs ih =>
    obtain ⟨r1, h1⟩ := divisionLoop_iteration regs candidate modulus bs b hlen
    have hlen' : modulus.length ≤ (shiftReduce modulus candidate b).length := by
      rw [shiftReduce_length]
      omega
    obtain ⟨r2, h2⟩ := ih r1 (shiftReduce modulus candidate b) hlen'
    refine ⟨r2, ?_⟩
    apply (h1.trans h2).mono
    simp only [List.length_cons, shiftReduce_length]
    nlinarith

theorem copy_initial (modulus input : List Bool) :
    copyStacks (5 : Fin 7) 2 (resting [] modulus input) =
      seven [] modulus input [] modulus [] [] := by
  funext i
  fin_cases i <;> simp [copyStacks, resting, seven]

theorem move_initial (modulus input : List Bool) :
    transferStacks (3 : Fin 7) 0
      (seven [] modulus input [] [] (padTo modulus []).reverse []) =
      resting (padTo modulus []) modulus input := by
  funext i
  fin_cases i <;> simp [transferStacks, resting, seven]

theorem reverse_input (candidate modulus input : List Bool) :
    reverseStacks (6 : Fin 7) (resting candidate modulus input) =
      resting candidate modulus input.reverse := by
  funext i
  fin_cases i <;> simp [reverseStacks, resting, seven]

theorem initialize_correct (regs : Fin 8 → Bool) (modulus input : List Bool) :
    ∃ finalRegs : Fin 8 → Bool,
      Trace initializeProgram (14 * modulus.length + 9 * input.length + 18)
        ⟨some 0, regs, resting [] modulus input⟩
        ⟨none, finalRegs, resting (padTo modulus []) modulus input.reverse⟩ := by
  let r1 := readRegs regs 1 3 none
  have hc1 := copyProgram_trace (5 : Fin 7) 2 4 (1 : Fin 8) 3
    (by decide) (by decide) (by decide) (by decide)
    regs (resting [] modulus input) (by rfl)
  have hh1 := halt_after_trace copyInitialModulusProgram hc1 (7 : Fin 8) rfl rfl
  have h1 : Trace copyInitialModulusProgram (7 * modulus.length + 5)
      ⟨some 0, regs, resting [] modulus input⟩
      ⟨none, r1, seven [] modulus input [] modulus [] []⟩ := by
    simp only [copyResult, copy_initial] at hh1
    simpa [r1, resting, seven, Nat.add_assoc] using hh1
  obtain ⟨r2, h2⟩ := paddingWide_correct r1 [] modulus input modulus [] (by simp)
  let r3 := readRegs r2 1 3 none
  have hc3 := transferProgram_trace (3 : Fin 7) 0 (1 : Fin 8) 3
    (by decide) (by decide) r2 (seven [] modulus input [] [] (padTo modulus []).reverse [])
  have hh3 := halt_after_trace moveInitialRemainderProgram hc3 (3 : Fin 4) rfl rfl
  have h3 : Trace moveInitialRemainderProgram (3 * modulus.length + 3)
      ⟨some 0, r2, seven [] modulus input [] [] (padTo modulus []).reverse []⟩
      ⟨none, r3, resting (padTo modulus []) modulus input⟩ := by
    simp only [transferResult, move_initial] at hh3
    simpa [r3, seven, padTo_length, Nat.add_assoc] using hh3
  have hc4 := reverseProgram_trace (6 : Fin 7) 1 2 (1 : Fin 8) 3
    (by decide) (by decide) (by decide) (by decide)
    r3 (resting (padTo modulus []) modulus input) (by rfl) (by rfl)
  have hh4 := halt_after_trace reverseInputProgram hc4 (9 : Fin 10) rfl rfl
  have h4 : Trace reverseInputProgram (9 * input.length + 7)
      ⟨some 0, r3, resting (padTo modulus []) modulus input⟩
      ⟨none, r3, resting (padTo modulus []) modulus input.reverse⟩ := by
    simp only [reverseResult, reverse_input] at hh4
    simpa [r3, readRegs_reset, resting, seven, Nat.add_assoc] using hh4
  have h12 := sequence_trace copyInitialModulusProgram paddingWideProgram _ _ _ _ _ _ h1 h2
  have h123 := sequence_trace _ moveInitialRemainderProgram _ _ _ _ _ _ h12 h3
  have h1234 := sequence_trace _ reverseInputProgram _ _ _ _ _ _ h123 h4
  refine ⟨r3, ?_⟩
  convert h1234 using 1
  · ring
  · apply cfg_ext
    · congr 1
    · rfl
    · rfl

theorem remainder_correct (regs : Fin 8 → Bool) (modulus input : List Bool) :
    ∃ finalRegs : Fin 8 → Bool,
      RunsIn remainderProgram (100 * (modulus.length + input.length + 1) ^ 2)
        ⟨some 0, regs, resting [] modulus input⟩
        ⟨none, finalRegs, resting (reduce modulus input) modulus []⟩ := by
  obtain ⟨r1, h1⟩ := initialize_correct regs modulus input
  obtain ⟨r2, h2⟩ := divisionLoop_correct r1 (padTo modulus []) modulus input.reverse
    (by rw [padTo_length])
  have ht := sequence_runs initializeProgram divisionLoopProgram _ _ _ _ _ _
    ⟨_, le_rfl, h1⟩ h2
  refine ⟨r2, ?_⟩
  have hbound :
      14 * modulus.length + 9 * input.length + 18 +
        50 * (input.reverse.length + 1) *
          ((padTo modulus []).length + modulus.length + input.reverse.length + 1) ≤
        100 * (modulus.length + input.length + 1) ^ 2 := by
    simp only [List.length_reverse, padTo_length]
    nlinarith [Nat.zero_le modulus.length, Nat.zero_le input.length]
  have ht' := ht.mono hbound
  have hstart :
      (⟨some 0, regs, resting [] modulus input⟩ : Cfg 8 7 89) =
        ⟨some (link initializeProgram divisionLoopProgram).entry, regs,
          resting [] modulus input⟩ := by
    apply cfg_ext
    · congr 1
    · rfl
    · rfl
  rw [hstart]
  simpa only [remainderProgram, reduceFrom_reverse] using ht'

end SubexponentialSAT.ModularDivisionPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ModularRingCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed Boolean-stack programs for arithmetic with a supplied binary modulus. -/

namespace SubexponentialSAT.ModularRingPrograms

open SubexponentialSAT.BitProgram SubexponentialSAT.ProgramLinking SubexponentialSAT.StackRoutines
open SubexponentialSAT.BinaryArithmetic SubexponentialSAT.ModularArithmetic SubexponentialSAT.ModularDivisionPrograms

theorem embed_ports {s S l : ℕ}
    (port : Fin s → Fin S) (hinj : Function.Injective port)
    (pc : Option (Fin l)) (regs frameRegs : Fin 8 → Bool)
    (localStk : Fin s → List Bool) (frame target : Fin S → List Bool)
    (hport : ∀ i, target (port i) = localStk i)
    (hframe : ∀ i, (¬ ∃ j, port j = i) → target i = frame i) :
    embedCfg id port id none (⟨none, frameRegs, frame⟩ : Cfg 8 S l)
      ⟨pc, regs, localStk⟩ = ⟨pc, regs, target⟩ := by
  apply cfg_ext
  · cases pc <;> rfl
  · simp [embedCfg]
  · funext i
    classical
    by_cases hi : ∃ j, port j = i
    · obtain ⟨j, rfl⟩ := hi
      exact (embedCfg_stack id port id none _ _ hinj j).trans (hport j).symm
    · exact (embedCfg_stack_frame id port id none _ _ i hi).trans (hframe i hi).symm

theorem sequence_runs {r s l m n k : ℕ}
    (p : Program r s l) (q : Program r s m)
    (ra rb rc : Fin r → Bool) (sa sb sc : Fin s → List Bool)
    (hp : RunsIn p n ⟨some p.entry, ra, sa⟩ ⟨none, rb, sb⟩)
    (hq : RunsIn q k ⟨some q.entry, rb, sb⟩ ⟨none, rc, sc⟩) :
    RunsIn (link p q) (n + k)
      ⟨some (link p q).entry, ra, sa⟩ ⟨none, rc, sc⟩ :=
  link_runsIn p q hp rfl hq

theorem embed_add (pc : Option (Fin 17)) (regs frameRegs : Fin 8 → Bool)
    (xs ys output modulus : List Bool) :
    embedCfg id addPorts id none
      (⟨none, frameRegs, resting [] modulus []⟩ : Cfg 8 7 17)
      ⟨pc, regs, SubexponentialSAT.BinaryPrograms.Add.stackState xs ys output⟩ =
      ⟨pc, regs, seven xs modulus [] ys output [] []⟩ := by
  apply embed_ports addPorts addPorts_injective
  · intro i; fin_cases i <;> rfl
  · intro i hi
    fin_cases i
    · exact False.elim (hi ⟨0, rfl⟩)
    · exact False.elim (hi ⟨1, rfl⟩)
    · exact False.elim (hi ⟨2, rfl⟩)
    · rfl
    · rfl
    · rfl
    · rfl

theorem addWide_correct (regs : Fin 8 → Bool) (hzero : regs 0 = false)
    (xs ys modulus : List Bool) :
    ∃ finalRegs,
      RunsIn addWideProgram (16 * (max xs.length ys.length + 1))
        ⟨some 0, regs, scalarInput xs ys modulus⟩
        ⟨none, finalRegs, resting (add xs ys) modulus []⟩ := by
  obtain ⟨finalRegs, hr⟩ := SubexponentialSAT.BinaryPrograms.Add.littleEndian_run regs xs ys
  have hw := liftProgram_runsIn SubexponentialSAT.BinaryPrograms.Add.littleEndianProgram id addPorts
    (⟨none, regs, resting [] modulus []⟩ : Cfg 8 7 17)
    Function.injective_id addPorts_injective hr
  rw [embed_add, embed_add, hzero] at hw
  exact ⟨finalRegs, hw⟩

theorem moveSum_correct (regs : Fin 8 → Bool) (word modulus : List Bool) :
    Trace moveSumProgram (6 * word.length + 6)
      ⟨some 0, regs, resting word modulus []⟩
      ⟨none, readRegs regs 1 3 none, resting [] modulus word⟩ := by
  have t1 := transferProgram_trace (0 : Fin 7) 2 (1 : Fin 8) 3
    (by decide) (by decide) regs (resting word modulus [])
  have h1 := halt_after_trace firstMoveProgram t1 (3 : Fin 4) rfl rfl
  simp only [transferResult, move_sum_first] at h1
  have t2 := transferProgram_trace (2 : Fin 7) 6 (1 : Fin 8) 3
    (by decide) (by decide) (readRegs regs 1 3 none)
    (seven [] modulus [] [] word.reverse [] [])
  have h2 := halt_after_trace secondMoveProgram t2 (3 : Fin 4) rfl rfl
  simp only [transferResult, move_sum_second, readRegs_reset] at h2
  have ht := link_trace firstMoveProgram secondMoveProgram h1 rfl h2
  convert ht using 1
  · simp [resting, seven]
    omega
  · simp [relabelCfg, relocatePc]
  · simp [relabelCfg, relocatePc]

theorem addMod_correct (regs : Fin 8 → Bool) (xs ys modulus : List Bool) :
    ∃ finalRegs,
      RunsIn addModProgram (600 * (modulus.length + xs.length + ys.length + 1) ^ 2)
        ⟨some 0, regs, scalarInput xs ys modulus⟩
        ⟨none, finalRegs, resting (reduce modulus (add xs ys)) modulus []⟩ := by
  let r1 := Function.update regs 0 false
  have h1 := resetBorrow_correct regs (scalarInput xs ys modulus)
  obtain ⟨r2, h2⟩ := addWide_correct r1 (by simp [r1]) xs ys modulus
  have h3 := moveSum_correct r2 (add xs ys) modulus
  obtain ⟨r4, h4⟩ := remainder_correct (readRegs r2 1 3 none) modulus (add xs ys)
  have h12 := sequence_runs resetBorrowProgram addWideProgram _ _ _ _ _ _
    ⟨2, le_rfl, h1⟩ h2
  have h123 := sequence_runs _ moveSumProgram _ _ _ _ _ _
    h12 ⟨_, le_rfl, h3⟩
  have ht := sequence_runs _ remainderProgram _ _ _ _ _ _ h123 h4
  refine ⟨r4, ht.mono ?_⟩
  have hlen := length_add xs ys
  have hmax : max xs.length ys.length ≤ xs.length + ys.length := max_le (by omega) (by omega)
  exact add_cost_bound _ _ _ _ _ hlen hmax

theorem addMod_value (regs : Fin 8 → Bool) (xs ys modulus : List Bool)
    (hm : 0 < BinaryArithmetic.toNat modulus) :
    ∃ finalRegs output,
      RunsIn addModProgram (600 * (modulus.length + xs.length + ys.length + 1) ^ 2)
        ⟨some 0, regs, scalarInput xs ys modulus⟩
        ⟨none, finalRegs, resting output modulus []⟩ ∧
      output.length ≤ modulus.length + xs.length + ys.length + 1 ∧
      BinaryArithmetic.toNat output = (BinaryArithmetic.toNat xs + BinaryArithmetic.toNat ys) % BinaryArithmetic.toNat modulus := by
  obtain ⟨finalRegs, hr⟩ := addMod_correct regs xs ys modulus
  refine ⟨finalRegs, reduce modulus (add xs ys), hr, ?_, ?_⟩
  · rw [reduce_length]
    have hl := length_add xs ys
    have hmax : max xs.length ys.length ≤ xs.length + ys.length := max_le (by omega) (by omega)
    omega
  · rw [reduce_correct _ _ hm, toNat_add]


end SubexponentialSAT.ModularRingPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ModularRingPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.ModularRingPrograms

open SubexponentialSAT.BitProgram SubexponentialSAT.ProgramLinking SubexponentialSAT.StackRoutines
open SubexponentialSAT.BinaryArithmetic SubexponentialSAT.ModularArithmetic SubexponentialSAT.ModularDivisionPrograms

/-! ## Restore a runtime-specified output width -/

open SubexponentialSAT.ModularPrograms

theorem paddingPrefix_exit (regs : Fin 8 → Bool) (input output : List Bool) :
    Trace paddingProgram 3
      (paddingCfg (some 0) regs [] input output)
      (paddingCfg none (readRegs regs 1 3 none) [] input output) := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, paddingProgram, execInstr,
    paddingCfg, readRegs, update_operand_left, Function.update_apply]

/-- The padding loop also handles a longer input: its unconsumed suffix remains
on the input stack, so a subsequent measured clear loop can remove it. -/
theorem paddingPrefix_correct (regs : Fin 8 → Bool) (shape input output : List Bool) :
    ∃ finalRegs,
      Trace paddingProgram (4 * shape.length + 3)
        (paddingCfg (some 0) regs shape input output)
        (paddingCfg none finalRegs [] (input.drop shape.length)
          ((padTo shape input).reverse ++ output)) := by
  induction shape generalizing regs input output with
  | nil =>
    exact ⟨readRegs regs 1 3 none, by simpa [padTo] using paddingPrefix_exit regs input output⟩
  | cons a shape ih =>
    cases input with
    | nil =>
      obtain ⟨rf, hr⟩ := ih (paddingRegs regs a []) [] (false :: output)
      refine ⟨rf, ?_⟩
      have ht := (padding_round regs a shape [] output).trans hr
      convert ht using 1 <;>
        simp [padTo, List.reverse_cons, List.append_assoc] ; omega
    | cons b bs =>
      obtain ⟨rf, hr⟩ := ih (paddingRegs regs a (b :: bs)) bs (b :: output)
      refine ⟨rf, ?_⟩
      have ht := (padding_round regs a shape (b :: bs) output).trans hr
      convert ht using 1 <;>
        simp [padTo, List.reverse_cons, List.append_assoc] ; omega

theorem padTo_value_of_lt (shape input : List Bool)
    (hvalue : BinaryArithmetic.toNat input < 2 ^ shape.length) :
    BinaryArithmetic.toNat (padTo shape input) = BinaryArithmetic.toNat input := by
  induction shape generalizing input with
  | nil =>
    simp only [List.length_nil, pow_zero] at hvalue
    have hz : BinaryArithmetic.toNat input = 0 := by omega
    simp [padTo, hz]
  | cons a shape ih =>
    cases input with
    | nil => exact padTo_correct _ [] (by simp)
    | cons b bs =>
      have htail : BinaryArithmetic.toNat bs < 2 ^ shape.length := by
        simp only [toNat_cons, List.length_cons, pow_succ] at hvalue
        omega
      simpa [padTo, toNat_cons] using congrArg (fun n => bitVal b + 2 * n) (ih bs htail)

theorem embed_seven {l : ℕ} (pc : Option (Fin l)) (regs frameRegs : Fin 8 → Bool)
    (base frameBase : Fin 7 → List Bool) (shape : List Bool) :
    embedCfg id sevenPorts id none
      (⟨none, frameRegs, extendSeven frameBase shape⟩ : Cfg 8 8 l)
      ⟨pc, regs, base⟩ = ⟨pc, regs, extendSeven base shape⟩ := by
  apply embed_ports sevenPorts sevenPorts_injective
  · intro i; fin_cases i <;> rfl
  · intro i hi
    fin_cases i
    · exact False.elim (hi ⟨0, rfl⟩)
    · exact False.elim (hi ⟨1, rfl⟩)
    · exact False.elim (hi ⟨2, rfl⟩)
    · exact False.elim (hi ⟨3, rfl⟩)
    · exact False.elim (hi ⟨4, rfl⟩)
    · exact False.elim (hi ⟨5, rfl⟩)
    · exact False.elim (hi ⟨6, rfl⟩)
    · rfl

theorem embed_normalize (pc : Option (Fin 5)) (regs frameRegs : Fin 8 → Bool)
    (input shape output modulus : List Bool) :
    embedCfg id normalizePorts id none
      (⟨none, frameRegs, normalizationState [] [] [] modulus⟩ : Cfg 8 8 5)
      (paddingCfg pc regs shape input output) =
      ⟨pc, regs, normalizationState input shape output modulus⟩ := by
  exact embed_ports normalizePorts normalizePorts_injective pc regs frameRegs
    (operandStacks shape input output) (normalizationState [] [] [] modulus)
    (normalizationState input shape output modulus)
    (normalization_port_value input shape output modulus)
    (normalization_port_frame input shape output modulus)

theorem normalizationPrefix_correct (regs : Fin 8 → Bool) (input shape modulus : List Bool) :
    ∃ finalRegs,
      Trace normalizationPrefixProgram (4 * shape.length + 3)
        ⟨some 0, regs, normalizationState input shape [] modulus⟩
        ⟨none, finalRegs,
          normalizationState (input.drop shape.length) [] (padTo shape input).reverse modulus⟩ := by
  obtain ⟨rf, hr⟩ := paddingPrefix_correct regs shape input []
  have hw := liftProgram_trace paddingProgram id normalizePorts
    (⟨none, regs, normalizationState [] [] [] modulus⟩ : Cfg 8 8 5)
    Function.injective_id normalizePorts_injective hr
  rw [embed_normalize, embed_normalize] at hw
  exact ⟨rf, by simpa using hw⟩

theorem shapeCopy_correct (regs : Fin 8 → Bool) (xs ys modulus : List Bool) :
    Trace shapeCopyProgram (7 * xs.length + 5)
      ⟨some 0, regs, extendSeven (scalarInput xs ys modulus) []⟩
      ⟨none, readRegs regs 1 3 none, extendSeven (scalarInput xs ys modulus) xs⟩ := by
  have tc := copyProgram_trace (0 : Fin 8) 7 3 (1 : Fin 8) 3
    (by decide) (by decide) (by decide) (by decide)
    regs (extendSeven (scalarInput xs ys modulus) []) (by rfl)
  have hh := halt_after_trace shapeCopyProgram tc (7 : Fin 8) rfl rfl
  simp only [copyResult, shape_copy] at hh
  simpa [extendSeven, scalarInput, seven, Nat.add_assoc] using hh

end SubexponentialSAT.ModularRingPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ProgramStateFrames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Reusable data projection and framing for genuine finite subroutine calls.
The projection/embedding functions specify states; executable code uses only
the fixed instruction-port relocation already proved by ProgramLinking. -/

namespace SubexponentialSAT.StructuredCalls

open SubexponentialSAT.BitProgram

@[simp] theorem embedState_project {r s R S : ℕ}
    (register : Fin r → Fin R) (stack : Fin s → Fin S) (d : State R S)
    (hr : Function.Injective register) (hs : Function.Injective stack) :
    embedState register stack d (projectState register stack d) = d := by
  apply embedState_eq_of_ports register stack d d _ hr hs
  · intro i; rfl
  · intro i hi; rfl
  · intro i; rfl
  · intro i hi; rfl

end SubexponentialSAT.StructuredCalls

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

/-! Fixed first-success scan using the concrete saved factor checker. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchCandidateControl

open BitProgram StructuredCalls
attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod

abbrev Data := State 22 28

end SubexponentialSAT.SqrtLog.IrreducibleSearchCandidateControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpScalarMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Exact machine refinement of the prepared scalar callbacks

The program output agrees as a Boolean list with the callback output, not
only modulo the coefficient modulus. Fixed width and binary-value uniqueness
give the final identification. The program tables are independent of p and mu.
-/

namespace SubexponentialSAT.SubexpScalarMachine

open SubexponentialSAT.BinaryArithmetic SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.BitProgram SubexponentialSAT.ModularRingPrograms SubexponentialSAT.ModularDivisionPrograms

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

theorem modulus_pos : 0 < BinaryArithmetic.toNat M.bits := by
  rw [M.value]
  exact pow_pos (Fact.out : p.Prime).pos μ

omit [Fact (Nat.Prime p)] in
theorem modulus_capacity : BinaryArithmetic.toNat M.bits ≤ 2^baseWidth p μ := by
  rw [M.value]
  exact modulus_le_width p μ

end SubexponentialSAT.SubexpScalarMachine

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpFlatAdd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Streaming addition of serialized quartic coefficients

There are four calls to the actual modular-word machine. Width is supplied as
stack data. No instruction table is generated from a coefficient or its width.
-/

namespace SubexponentialSAT.SubexpFlatAdd

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpLiftRing SubexpQuarticRing

abbrev ready (regs : Fin 8 → Bool) (modulus left right width packed : List Bool)
    (frame : Fin 6 → List Bool) : Data :=
  state regs [] [] modulus left right width [] [] packed frame

theorem take_left_state (regs : Fin 8 → Bool)
    (x modulus left right width packed : List Bool) (frame : Fin 6 → List Bool) :
    afterTake (ready regs modulus (x ++ left) right width packed frame) 8 0 0 1 x left =
      state (readRegs regs 0 1 none) x [] modulus left right width [] [] packed frame := by
  apply state_ext
  · rfl
  · funext i
    fin_cases i <;>
      simp [afterTake, ready, state, «stacks», Fin.addCases, Fin.coe_ofNat_eq_mod
        ]

theorem take_right_state (regs : Fin 8 → Bool)
    (x y modulus left right width packed : List Bool) (frame : Fin 6 → List Bool) :
    afterTake (state regs x [] modulus left (y ++ right) width [] [] packed frame)
        9 1 0 1 y right =
      state (readRegs regs 0 1 none) x y modulus left right width [] [] packed frame := by
  apply state_ext
  · rfl
  · funext i
    fin_cases i <;>
      simp [afterTake, state, «stacks», Fin.addCases, Fin.coe_ofNat_eq_mod
        ]

theorem transfer_sum_state (regs : Fin 8 → Bool)
    (x modulus left right width packed : List Bool) (frame : Fin 6 → List Bool) :
    afterTransfer (state regs x [] modulus left right width [] [] packed frame) 0 13 0 1 =
      ready (readRegs regs 0 1 none) modulus left right width (x.reverse ++ packed) frame := by
  apply state_ext
  · rfl
  · funext i
    fin_cases i <;>
      simp [afterTransfer, ready, state, «stacks», Fin.addCases, Fin.coe_ofNat_eq_mod,
        StackRoutines.transferStacks ]

end SubexponentialSAT.SubexpFlatAdd

end OAI.Algorithms
end


