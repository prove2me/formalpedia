-- Prove2me | Definitions.Def_OAIQ081S023
-- name    : OAIQ081S023
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:26:29.794335+00:00
-- url     : https://prove2.me/theorems/e6e4f5e0-5915-49f0-ba33-fcc0870dbed5
-- title:
--   Definitions bundle OAIQ081S023 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 84 declarations of OpenAI's Lean: 23 definitions, 2 inductive types or structures and 59 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.ArithmeticCalls.mulPorts`, `OAI.Algorithms.SubexponentialSAT.ArithmeticCalls.mulReady`, `OAI.Algorithms.SubexponentialSAT.ArithmeticCalls.multiplyAt`, `OAI.Algorithms.SubexponentialSAT.ArithmeticCalls.multiplyRaw`, `OAI.Algorithms.SubexponentialSAT.ArithmeticExpressionSupport.Data`, `OAI.Algorithms.SubexponentialSAT.ArithmeticExpressionSupport.atom`, `OAI.Algorithms.SubexponentialSAT.BinaryPrograms.Add.Config`, `OAI.Algorithms.SubexponentialSAT.BinaryPrograms.Add.cfg`, `OAI.Algorithms.SubexponentialSAT.BinaryPrograms.Add.readRegisters`, `OAI.Algorithms.SubexponentialSAT.BinaryPrograms.Add.roundRegisters`, `OAI.Algorithms.SubexponentialSAT.BinaryPrograms.Mul.Config`, `OAI.Algorithms.SubexponentialSAT.BinaryPrograms.Mul.cfg`, `OAI.Algorithms.SubexponentialSAT.BinaryPrograms.Mul.loopCfg`, `OAI.Algorithms.SubexponentialSAT.BinaryPrograms.Mul.program`, `OAI.Algorithms.SubexponentialSAT.BitProgram.RunsIn`, `OAI.Algorithms.SubexponentialSAT.ProgramLinking.CodeEmbedding`, `OAI.Algorithms.SubexponentialSAT.ProgramLinking.enter`, `OAI.Algorithms.SubexponentialSAT.StackRoutines.clearResult`, `OAI.Algorithms.SubexponentialSAT.StackRoutines.fanoutResult`, `OAI.Algorithms.SubexponentialSAT.StackRoutines.fanoutStacks`, `OAI.Algorithms.SubexponentialSAT.StackRoutines.transferResult`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.embedState`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.Atom.eval`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.Eval`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: [`SubexponentialSAT_ArithmeticCalls`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/ArithmeticCalls.lean), [`SubexponentialSAT_ArithmeticExpressionSupport`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/ArithmeticExpressionSupport.lean), [`SubexponentialSAT_BinaryPrograms`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/BinaryPrograms.lean), [`SubexponentialSAT_BitProgram`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/BitProgram.lean), [`SubexponentialSAT_Computation`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/Computation.lean), [`SubexponentialSAT_ListRegisterProgram`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/ListRegisterProgram.lean), [`SubexponentialSAT_ProgramFrames`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/ProgramFrames.lean), [`SubexponentialSAT_ProgramLinking`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/ProgramLinking.lean), [`SubexponentialSAT_StackRoutines`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/StackRoutines.lean), [`SubexponentialSAT_StructuredCalls`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/StructuredCalls.lean), [`SubexponentialSAT_StructuredProgram`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/StructuredProgram.lean).
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S000` and `OAIQ081S001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S045`, `OAIQ081S046`, `OAIQ081S047`, `OAIQ081S049`, `OAIQ081S050`, `OAIQ081S051`, `OAIQ081S052`, `OAIQ081S053`, `OAIQ081S054`, `OAIQ081S055`, `OAIQ081S056`, `OAIQ081S057`, `OAIQ081S058`, `OAIQ081S059`, `OAIQ081S060`, `OAIQ081S061`, `OAIQ081S062`, `OAIQ081S063`, `OAIQ081S064` and `OAIQ081S065`; the statement `OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryCountReconstruction_run_space_of_outputs_with_full_frame`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay` and `OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryCountReconstruction_run_space_of_outputs_with_full_frame`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S000
import Definitions.Def_OAIQ081S001

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Computation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Measured machine execution for the candidate SAT theorem

The definitions here use the transition semantics of mathlib's finite TM2 machines.
A bound is accompanied by an actual execution certificate; no cost is assigned to
an arbitrary mathematical function. TM2 counts executions of finite statements.
Each fixed statement contains finitely many primitive stack operations.
-/

namespace SubexponentialSAT.Computation

universe u v w

namespace RunsIn

variable {α : Type u} {step : α → Option α} {n m : ℕ} {a b c : α}

theorem trans (h₁ : RunsIn step n a b) (h₂ : RunsIn step m b c) :
    RunsIn step (n + m) a c := by
  obtain ⟨t₁, ht₁, tr₁⟩ := h₁
  obtain ⟨t₂, ht₂, tr₂⟩ := h₂
  exact ⟨t₁ + t₂, Nat.add_le_add ht₁ ht₂, tr₁.trans tr₂⟩

end RunsIn

end SubexponentialSAT.Computation

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_BitProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A first-order finite program language. Unbounded data lives only in Boolean
stacks; every register is one bit and all control labels are fixed finite data. -/

namespace SubexponentialSAT.BitProgram

abbrev RunsIn {r s l : ℕ} (p : Program r s l) := SubexponentialSAT.Computation.RunsIn (step p)

theorem step_code {r s l : ℕ} (p : Program r s l) (c : Cfg r s l)
    (label : Fin l) (instr : Instr r s l) (hp : c.pc = some label)
    (hc : p.code label = instr) : step p c = some (execInstr instr c) := by
  simp [step, hp, hc]

theorem readRegs_value {r : ℕ} (regs : Fin r → Bool)
    (value present : Fin r) (top : Option Bool) (h : value ≠ present) :
    readRegs regs value present top value = top.getD false := by
  simp [readRegs, h]

end SubexponentialSAT.BitProgram

end OAI.Algorithms
end

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

theorem embedCfg_register_frame (register : Fin r → Fin R)
    (stack : Fin s → Fin S) (label : Fin l → Fin L)
    (returnPc : Option (Fin L)) (frame : Cfg R S L) (c : Cfg r s l)
    (a : Fin R) (ha : ¬ ∃ b, register b = a) :
    (embedCfg register stack label returnPc frame c).regs a = frame.regs a :=
  Function.extend_apply' _ _ _ ha

theorem embedCfg_stack_frame (register : Fin r → Fin R)
    (stack : Fin s → Fin S) (label : Fin l → Fin L)
    (returnPc : Option (Fin L)) (frame : Cfg R S L) (c : Cfg r s l)
    (a : Fin S) (ha : ¬ ∃ b, stack b = a) :
    (embedCfg register stack label returnPc frame c).stacks a = frame.stacks a :=
  Function.extend_apply' _ _ _ ha

/-- Relocation commutes with every instruction, even when read value/presence
registers alias.  Injective port maps preserve exactly the source aliases. -/
theorem execInstr_relocate (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L)) (frame : Cfg R S L)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (instr : Instr r s l) (c : Cfg r s l) :
    execInstr (relocateInstr register stack label returnPc instr)
        (embedCfg register stack label returnPc frame c) =
      embedCfg register stack label returnPc frame (execInstr instr c) := by
  cases instr <;> cases returnPc <;>
    simp [relocateInstr, execInstr, embedCfg, relocatePc, readRegs,
      hregister.extend_apply, hstack.extend_apply,
      extend_update hregister, extend_update hstack, apply_ite]
  all_goals split <;> simp_all

/-- Code agreement is an ordinary equality of actual finite table entries. -/
abbrev CodeEmbedding (p : Program r s l) (q : Program R S L)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L)) : Prop :=
  ∀ pc, q.code (label pc) = relocateInstr register stack label returnPc (p.code pc)

theorem relocate_step_at (p : Program r s l) (q : Program R S L)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L)) (frame : Cfg R S L)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    {c c' : Cfg r s l}
    (hcode : ∀ pc, c.pc = some pc →
      q.code (label pc) = relocateInstr register stack label returnPc (p.code pc))
    (hstep : step p c = some c') :
    step q (embedCfg register stack label returnPc frame c) =
      some (embedCfg register stack label returnPc frame c') := by
  cases hpc : c.pc with
  | none => simp [step, hpc] at hstep
  | some pc =>
      have hc' : execInstr (p.code pc) c = c' := by
        simpa [step, hpc] using hstep
      simp only [step, embedCfg, hpc, relocatePc, Option.map_some]
      rw [hcode pc hpc]
      change some (execInstr (relocateInstr register stack label returnPc (p.code pc))
        (embedCfg register stack label returnPc frame c)) = _
      rw [execInstr_relocate register stack label returnPc frame hregister hstack, hc']
      rfl

theorem relocate_step (p : Program r s l) (q : Program R S L)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L)) (frame : Cfg R S L)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (hcode : CodeEmbedding p q register stack label returnPc)
    {c c' : Cfg r s l} (hstep : step p c = some c') :
    step q (embedCfg register stack label returnPc frame c) =
      some (embedCfg register stack label returnPc frame c') :=
  relocate_step_at p q register stack label returnPc frame hregister hstack
    (fun pc _ => hcode pc) hstep

/-- Complete block traces transfer with exactly the same number of steps.
In particular a source halt is the target's actual return-jump instruction. -/
theorem relocate_trace (p : Program r s l) (q : Program R S L)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L)) (frame : Cfg R S L)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (hcode : CodeEmbedding p q register stack label returnPc)
    {steps : ℕ} {c c' : Cfg r s l} (htrace : Trace p steps c c') :
    Trace q steps (embedCfg register stack label returnPc frame c)
      (embedCfg register stack label returnPc frame c') := by
  induction htrace with
  | refl c => exact .refl _
  | cons hs ht ih =>
      exact .cons
        (relocate_step p q register stack label returnPc frame hregister hstack hcode hs) ih

theorem relocate_runsIn (p : Program r s l) (q : Program R S L)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L)) (frame : Cfg R S L)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (hcode : CodeEmbedding p q register stack label returnPc)
    {bound : ℕ} {c c' : Cfg r s l} (htrace : RunsIn p bound c c') :
    RunsIn q bound (embedCfg register stack label returnPc frame c)
      (embedCfg register stack label returnPc frame c') := by
  obtain ⟨steps, hsteps, ht⟩ := htrace
  exact ⟨steps, hsteps,
    relocate_trace p q register stack label returnPc frame hregister hstack hcode ht⟩

theorem liftProgram_trace (p : Program r s l) (register : Fin r → Fin R)
    (stack : Fin s → Fin S) (frame : Cfg R S l)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    {n : ℕ} {a b : Cfg r s l} (h : Trace p n a b) :
    Trace (liftProgram p register stack) n
      (embedCfg register stack id none frame a) (embedCfg register stack id none frame b) :=
  relocate_trace p _ register stack id none frame hregister hstack (fun _ => rfl) h

/-! ## Concrete disjoint linking -/

theorem linkInto_leftCode {r' s' m : ℕ} (p : Program r s l) (q : Program r' s' m)
    (registerP : Fin r → Fin R) (stackP : Fin s → Fin S)
    (registerQ : Fin r' → Fin R) (stackQ : Fin s' → Fin S) :
    CodeEmbedding p (linkInto p q registerP stackP registerQ stackQ)
      registerP stackP (Fin.castAdd m) (some (Fin.natAdd l q.entry)) := by
  intro pc
  simp []

theorem linkInto_rightCode {r' s' m : ℕ} (p : Program r s l) (q : Program r' s' m)
    (registerP : Fin r → Fin R) (stackP : Fin s → Fin S)
    (registerQ : Fin r' → Fin R) (stackQ : Fin s' → Fin S) :
    CodeEmbedding q (linkInto p q registerP stackP registerQ stackQ)
      registerQ stackQ (Fin.natAdd l) none := by
  intro pc
  simp []

/-- Start another finite table with the current register and stack contents. -/
abbrev enter {m : ℕ} (q : Program r s m) (c : Cfg r s l) : Cfg r s m where
  pc := some q.entry
  regs := c.regs
  «stacks» := c.stacks

theorem link_left_trace {m : ℕ} (p : Program r s l) (q : Program r s m)
    {n : ℕ} {a b : Cfg r s l} (h : Trace p n a b) :
    Trace (link p q) n
      (relabelCfg (Fin.castAdd m) (some (Fin.natAdd l q.entry)) a)
      (relabelCfg (Fin.castAdd m) (some (Fin.natAdd l q.entry)) b) := by
  let frame := relabelCfg (Fin.castAdd m) (some (Fin.natAdd l q.entry)) a
  simpa only [embedCfg_id] using
    relocate_trace p (link p q) id id (Fin.castAdd m)
      (some (Fin.natAdd l q.entry)) frame Function.injective_id Function.injective_id
      (linkInto_leftCode p q id id id id) h

theorem link_right_trace {m : ℕ} (p : Program r s l) (q : Program r s m)
    {n : ℕ} {a b : Cfg r s m} (h : Trace q n a b) :
    Trace (link p q) n
      (relabelCfg (Fin.natAdd l) none a) (relabelCfg (Fin.natAdd l) none b) := by
  let frame := relabelCfg (Fin.natAdd l) none a
  simpa only [embedCfg_id] using
    relocate_trace q (link p q) id id (Fin.natAdd l) none frame
      Function.injective_id Function.injective_id (linkInto_rightCode p q id id id id) h

/-- No dispatcher or subroutine oracle is added: the replaced halt itself is
the one-step return jump, so the composed trace length is exactly the sum. -/
theorem link_trace {m : ℕ} (p : Program r s l) (q : Program r s m)
    {n₁ n₂ : ℕ} {a b : Cfg r s l} {c : Cfg r s m}
    (hp : Trace p n₁ a b) (hb : b.pc = none)
    (hq : Trace q n₂ (enter q b) c) :
    Trace (link p q) (n₁ + n₂)
      (relabelCfg (Fin.castAdd m) (some (Fin.natAdd l q.entry)) a)
      (relabelCfg (Fin.natAdd l) none c) := by
  have boundary : relabelCfg (Fin.castAdd m) (some (Fin.natAdd l q.entry)) b =
      relabelCfg (Fin.natAdd l) none (enter q b) := by
    simp [relabelCfg, relocatePc, hb]
  have hp' := link_left_trace p q hp
  rw [boundary] at hp'
  exact hp'.trans (link_right_trace p q hq)

theorem link_runsIn {m : ℕ} (p : Program r s l) (q : Program r s m)
    {n₁ n₂ : ℕ} {a b : Cfg r s l} {c : Cfg r s m}
    (hp : RunsIn p n₁ a b) (hb : b.pc = none)
    (hq : RunsIn q n₂ (enter q b) c) :
    RunsIn (link p q) (n₁ + n₂)
      (relabelCfg (Fin.castAdd m) (some (Fin.natAdd l q.entry)) a)
      (relabelCfg (Fin.natAdd l) none c) := by
  obtain ⟨i, hi, hpi⟩ := hp
  obtain ⟨j, hj, hqj⟩ := hq
  exact ⟨i + j, Nat.add_le_add hi hj, link_trace p q hpi hb hqj⟩

end SubexponentialSAT.ProgramLinking

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

/-- Specification of popping a source onto each of two destinations. -/
def fanoutStacks {S : Type u} [DecidableEq S] (src dst₁ dst₂ : S)
    (stk : Stacks S) : Stacks S :=
  Function.update
    (Function.update (Function.update stk src []) dst₁
      ((stk src).reverse ++ stk dst₁))
    dst₂ ((stk src).reverse ++ stk dst₂)

open BitProgram

theorem readRegs_reset {r : ℕ} (regs : Fin r → Bool) (value present : Fin r)
    (top : Option Bool) :
    readRegs (readRegs regs value present top) value present none =
      readRegs regs value present none := by
  funext j
  by_cases hp : j = present
  · subst j; simp [readRegs]
  · by_cases hv : j = value
    · subst j; simp [readRegs, hp]
    · simp [readRegs, hp, hv]

/-- The exit state of the clear loop; only its read registers are clobbered. -/
def clearResult {r s l : ℕ} (exit : Fin l) (src : Fin s) (value present : Fin r)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) : Cfg r s l :=
  ⟨some exit, readRegs regs value present none, clearStacks src stk⟩

/-- Exact execution of the two-instruction clear loop. Local code equations
allow the routine to be placed inside any finite caller program. -/
theorem clear_trace_aux {r s l : ℕ} (p : Program r s l)
    (src : Fin s) (value present : Fin r) (loop check exit : Fin l)
    (hloop : p.code loop = .pop src value present check)
    (hcheck : p.code check = .branch present loop exit)
    (xs : List Bool) (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (hxs : stk src = xs) :
    Trace p (2 * xs.length + 2) ⟨some loop, regs, stk⟩
      (clearResult exit src value present regs stk) := by
  induction xs generalizing regs stk with
  | nil =>
      refine .cons (b := ⟨some check, readRegs regs value present none,
        clearStacks src stk⟩) ?_ ?_
      · simp [step, hloop, execInstr, hxs, clearStacks]
      · refine .cons (b := clearResult exit src value present regs stk) ?_ (.refl _)
        simp [step, hcheck, execInstr, readRegs_present, clearResult]
  | cons a xs ih =>
      let regs' := readRegs regs value present (some a)
      let stk' := Function.update stk src xs
      have hxs' : stk' src = xs := by simp [stk']
      have ht := ih regs' stk' hxs'
      have ht' : Trace p (2 * xs.length + 2) ⟨some loop, regs', stk'⟩
          (clearResult exit src value present regs stk) := by
        simpa only [clearResult, regs', readRegs_reset, stk', clearStacks,
          Function.update_idem] using ht
      have total : Trace p (2 * xs.length + 2 + 1 + 1) ⟨some loop, regs, stk⟩
          (clearResult exit src value present regs stk) := by
        refine .cons (b := ⟨some check, regs', stk'⟩) ?_ ?_
        · simp [step, hloop, execInstr, hxs, regs', stk']
        · refine .cons (b := ⟨some loop, regs', stk'⟩) ?_ ht'
          simp [step, hcheck, execInstr, regs', readRegs_present]
      simpa only [List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_assoc] using total

theorem clear_trace {r s l : ℕ} (p : Program r s l)
    (src : Fin s) (value present : Fin r) (loop check exit : Fin l)
    (hloop : p.code loop = .pop src value present check)
    (hcheck : p.code check = .branch present loop exit)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) :
    Trace p (2 * (stk src).length + 2) ⟨some loop, regs, stk⟩
      (clearResult exit src value present regs stk) :=
  clear_trace_aux p src value present loop check exit hloop hcheck _ regs stk rfl

theorem transferStacks_cons_step {S : Type u} [DecidableEq S]
    (src dst : S) (stk : Stacks S) (a : Bool) (xs : List Bool)
    (hsd : src ≠ dst) (hxs : stk src = a :: xs) :
    transferStacks src dst
        (Function.update (Function.update stk src xs) dst (a :: stk dst)) =
      transferStacks src dst stk := by
  funext j
  by_cases hd : j = dst
  · subst j
    simp [transferStacks, hsd, hxs, List.reverse_cons, List.append_assoc]
  · by_cases hs : j = src
    · subst j
      simp [transferStacks, hsd ]
    · simp [transferStacks, hs, hd]

def transferResult {r s l : ℕ} (exit : Fin l) (src dst : Fin s)
    (value present : Fin r) (regs : Fin r → Bool) (stk : Stacks (Fin s)) : Cfg r s l :=
  ⟨some exit, readRegs regs value present none, transferStacks src dst stk⟩

/-- A concrete transfer loop, with one pop, one branch, and one push per bit.
The final empty read and branch account for the additional two transitions. -/
theorem transfer_trace_aux {r s l : ℕ} (p : Program r s l)
    (src dst : Fin s) (value present : Fin r) (loop check put exit : Fin l)
    (hsd : src ≠ dst) (hvp : value ≠ present)
    (hloop : p.code loop = .pop src value present check)
    (hcheck : p.code check = .branch present put exit)
    (hput : p.code put = .push dst value loop)
    (xs : List Bool) (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (hxs : stk src = xs) :
    Trace p (3 * xs.length + 2) ⟨some loop, regs, stk⟩
      (transferResult exit src dst value present regs stk) := by
  induction xs generalizing regs stk with
  | nil =>
      have hst : transferStacks src dst stk = Function.update stk src [] := by
        funext j
        by_cases hd : j = dst
        · subst j; simp [transferStacks, hxs, hsd.symm]
        · simp [transferStacks, hd]
      refine .cons (b := ⟨some check, readRegs regs value present none,
        Function.update stk src []⟩) ?_ ?_
      · simp [step, hloop, execInstr, hxs]
      · refine .cons (b := transferResult exit src dst value present regs stk) ?_ (.refl _)
        simp [step, hcheck, execInstr, transferResult, hst, readRegs_present]
  | cons a xs ih =>
      let regs' := readRegs regs value present (some a)
      let stk₁ := Function.update stk src xs
      let stk₂ := Function.update stk₁ dst (a :: stk dst)
      have hxs' : stk₂ src = xs := by simp [stk₂, stk₁, hsd]
      have ht := ih regs' stk₂ hxs'
      have hst : transferStacks src dst stk₂ = transferStacks src dst stk :=
        transferStacks_cons_step src dst stk a xs hsd hxs
      have ht' : Trace p (3 * xs.length + 2) ⟨some loop, regs', stk₂⟩
          (transferResult exit src dst value present regs stk) := by
        simpa only [transferResult, regs', readRegs_reset, hst] using ht
      have total : Trace p (3 * xs.length + 2 + 1 + 1 + 1) ⟨some loop, regs, stk⟩
          (transferResult exit src dst value present regs stk) := by
        refine .cons (b := ⟨some check, regs', stk₁⟩) ?_ ?_
        · simp [step, hloop, execInstr, hxs, regs', stk₁]
        · refine .cons (b := ⟨some put, regs', stk₁⟩) ?_ ?_
          · simp [step, hcheck, execInstr, regs', readRegs_present]
          · refine .cons (b := ⟨some loop, regs', stk₂⟩) ?_ ht'
            simp [step, hput, execInstr, regs', stk₂, stk₁,
              readRegs_value, hvp, hsd.symm]
      simpa only [List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_assoc] using total

theorem transfer_trace {r s l : ℕ} (p : Program r s l)
    (src dst : Fin s) (value present : Fin r) (loop check put exit : Fin l)
    (hsd : src ≠ dst) (hvp : value ≠ present)
    (hloop : p.code loop = .pop src value present check)
    (hcheck : p.code check = .branch present put exit)
    (hput : p.code put = .push dst value loop)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) :
    Trace p (3 * (stk src).length + 2) ⟨some loop, regs, stk⟩
      (transferResult exit src dst value present regs stk) :=
  transfer_trace_aux p src dst value present loop check put exit hsd hvp
    hloop hcheck hput _ regs stk rfl

theorem transferProgram_trace {r s : ℕ} (src dst : Fin s) (value present : Fin r)
    (hsd : src ≠ dst) (hvp : value ≠ present)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) :
    Trace (transferProgram src dst value present) (3 * (stk src).length + 2)
      ⟨some 0, regs, stk⟩ (transferResult 3 src dst value present regs stk) :=
  transfer_trace _ src dst value present 0 1 2 3 hsd hvp rfl rfl rfl regs stk

theorem fanoutStacks_cons_step {S : Type u} [DecidableEq S]
    (src dst₁ dst₂ : S) (stk : Stacks S) (a : Bool) (xs : List Bool)
    (h₁ : src ≠ dst₁) (h₂ : src ≠ dst₂) (h₁₂ : dst₁ ≠ dst₂)
    (hxs : stk src = a :: xs) :
    fanoutStacks src dst₁ dst₂
        (Function.update
          (Function.update (Function.update stk src xs) dst₁ (a :: stk dst₁))
          dst₂ (a :: stk dst₂)) =
      fanoutStacks src dst₁ dst₂ stk := by
  funext j
  by_cases hj₂ : j = dst₂
  · subst j
    simp [fanoutStacks, h₁, h₂, h₁₂,
      hxs, List.reverse_cons, List.append_assoc]
  · by_cases hj₁ : j = dst₁
    · subst j
      simp [fanoutStacks, h₁, h₂, h₁₂,
        hxs, List.reverse_cons, List.append_assoc]
    · by_cases hjs : j = src
      · subst j
        simp [fanoutStacks, h₁, h₂, h₁₂]
      · simp [fanoutStacks, hj₁, hj₂, hjs]

def fanoutResult {r s l : ℕ} (exit : Fin l) (src dst₁ dst₂ : Fin s)
    (value present : Fin r) (regs : Fin r → Bool) (stk : Stacks (Fin s)) : Cfg r s l :=
  ⟨some exit, readRegs regs value present none, fanoutStacks src dst₁ dst₂ stk⟩

/-- Pop one source and push its bits onto two destinations, using four actual
instructions per nonempty iteration. -/
theorem fanout_trace_aux {r s l : ℕ} (p : Program r s l)
    (src dst₁ dst₂ : Fin s) (value present : Fin r)
    (loop check put₁ put₂ exit : Fin l)
    (h₁ : src ≠ dst₁) (h₂ : src ≠ dst₂) (h₁₂ : dst₁ ≠ dst₂) (hvp : value ≠ present)
    (hloop : p.code loop = .pop src value present check)
    (hcheck : p.code check = .branch present put₁ exit)
    (hput₁ : p.code put₁ = .push dst₁ value put₂)
    (hput₂ : p.code put₂ = .push dst₂ value loop)
    (xs : List Bool) (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (hxs : stk src = xs) :
    Trace p (4 * xs.length + 2) ⟨some loop, regs, stk⟩
      (fanoutResult exit src dst₁ dst₂ value present regs stk) := by
  induction xs generalizing regs stk with
  | nil =>
      have hst : fanoutStacks src dst₁ dst₂ stk = Function.update stk src [] := by
        funext j
        by_cases hj₂ : j = dst₂
        · subst j; simp [fanoutStacks, hxs, h₂.symm]
        · by_cases hj₁ : j = dst₁
          · subst j; simp [fanoutStacks, hxs, h₁.symm, h₁₂]
          · simp [fanoutStacks, hj₁, hj₂]
      refine .cons (b := ⟨some check, readRegs regs value present none,
        Function.update stk src []⟩) ?_ ?_
      · simp [step, hloop, execInstr, hxs]
      · refine .cons (b := fanoutResult exit src dst₁ dst₂ value present regs stk)
          ?_ (.refl _)
        simp [step, hcheck, execInstr, fanoutResult, hst, readRegs_present]
  | cons a xs ih =>
      let regs' := readRegs regs value present (some a)
      let stk₁ := Function.update stk src xs
      let stk₂ := Function.update stk₁ dst₁ (a :: stk dst₁)
      let stk₃ := Function.update stk₂ dst₂ (a :: stk dst₂)
      have hxs' : stk₃ src = xs := by simp [stk₃, stk₂, stk₁, h₁, h₂]
      have ht := ih regs' stk₃ hxs'
      have hst : fanoutStacks src dst₁ dst₂ stk₃ = fanoutStacks src dst₁ dst₂ stk :=
        fanoutStacks_cons_step src dst₁ dst₂ stk a xs h₁ h₂ h₁₂ hxs
      have ht' : Trace p (4 * xs.length + 2) ⟨some loop, regs', stk₃⟩
          (fanoutResult exit src dst₁ dst₂ value present regs stk) := by
        simpa only [fanoutResult, regs', readRegs_reset, hst] using ht
      have total : Trace p (4 * xs.length + 2 + 1 + 1 + 1 + 1) ⟨some loop, regs, stk⟩
          (fanoutResult exit src dst₁ dst₂ value present regs stk) := by
        refine .cons (b := ⟨some check, regs', stk₁⟩) ?_ ?_
        · simp [step, hloop, execInstr, hxs, regs', stk₁]
        · refine .cons (b := ⟨some put₁, regs', stk₁⟩) ?_ ?_
          · simp [step, hcheck, execInstr, regs', readRegs_present]
          · refine .cons (b := ⟨some put₂, regs', stk₂⟩) ?_ ?_
            · simp [step, hput₁, execInstr, regs', stk₂, stk₁,
                readRegs_value, hvp, h₁.symm]
            · refine .cons (b := ⟨some loop, regs', stk₃⟩) ?_ ht'
              simp [step, hput₂, execInstr, regs', stk₃, stk₂, stk₁,
                readRegs_value, hvp, h₂.symm, h₁₂.symm]
      simpa only [List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_assoc] using total

theorem fanout_trace {r s l : ℕ} (p : Program r s l)
    (src dst₁ dst₂ : Fin s) (value present : Fin r)
    (loop check put₁ put₂ exit : Fin l)
    (h₁ : src ≠ dst₁) (h₂ : src ≠ dst₂) (h₁₂ : dst₁ ≠ dst₂) (hvp : value ≠ present)
    (hloop : p.code loop = .pop src value present check)
    (hcheck : p.code check = .branch present put₁ exit)
    (hput₁ : p.code put₁ = .push dst₁ value put₂)
    (hput₂ : p.code put₂ = .push dst₂ value loop)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) :
    Trace p (4 * (stk src).length + 2) ⟨some loop, regs, stk⟩
      (fanoutResult exit src dst₁ dst₂ value present regs stk) :=
  fanout_trace_aux p src dst₁ dst₂ value present loop check put₁ put₂ exit
    h₁ h₂ h₁₂ hvp hloop hcheck hput₁ hput₂ _ regs stk rfl

theorem fanout_after_transfer_eq_copy {S : Type u} [DecidableEq S]
    (src dst tmp : S) (stk : Stacks S)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst) (htmp : stk tmp = []) :
    fanoutStacks tmp src dst (transferStacks src tmp stk) = copyStacks src dst stk := by
  funext j
  by_cases hd : j = dst
  · subst j
    simp [fanoutStacks, transferStacks, copyStacks, hst,
      hsd.symm, htd.symm, htmp]
  · by_cases hs : j = src
    · subst j
      simp [fanoutStacks, transferStacks, copyStacks, hsd, hst,
        hsd.symm, htd.symm, htmp]
    · by_cases ht : j = tmp
      · subst j
        simp [fanoutStacks, transferStacks, copyStacks, hst, htd,
          hsd.symm, hst.symm, htd.symm, htmp]
      · simp [fanoutStacks, transferStacks, copyStacks, hd, hs, ht]

/-- Preserving copy through one initially empty temporary stack. The source is
restored; its original word is prefixed in forward order to the destination. -/
theorem copy_trace {r s l : ℕ} (p : Program r s l)
    (src dst tmp : Fin s) (value present : Fin r)
    (moveLoop moveCheck movePut copyLoop copyCheck copyPut₁ copyPut₂ exit : Fin l)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst) (hvp : value ≠ present)
    (hm₀ : p.code moveLoop = .pop src value present moveCheck)
    (hm₁ : p.code moveCheck = .branch present movePut copyLoop)
    (hm₂ : p.code movePut = .push tmp value moveLoop)
    (hc₀ : p.code copyLoop = .pop tmp value present copyCheck)
    (hc₁ : p.code copyCheck = .branch present copyPut₁ exit)
    (hc₂ : p.code copyPut₁ = .push src value copyPut₂)
    (hc₃ : p.code copyPut₂ = .push dst value copyLoop)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) (htmp : stk tmp = []) :
    Trace p (7 * (stk src).length + 4) ⟨some moveLoop, regs, stk⟩
      (copyResult exit src dst value present regs stk) := by
  have move := transfer_trace p src tmp value present moveLoop moveCheck movePut copyLoop
    hst hvp hm₀ hm₁ hm₂ regs stk
  have copy := fanout_trace p tmp src dst value present copyLoop copyCheck copyPut₁ copyPut₂ exit
    hst.symm htd hsd hvp hc₀ hc₁ hc₂ hc₃ (readRegs regs value present none)
    (transferStacks src tmp stk)
  have hlen : (transferStacks src tmp stk tmp).length = (stk src).length := by
    simp [transferStacks, htmp]
  have hfinal := fanout_after_transfer_eq_copy src dst tmp stk hsd hst htd htmp
  have copy' : Trace p (4 * (stk src).length + 2)
      (transferResult copyLoop src tmp value present regs stk)
      (copyResult exit src dst value present regs stk) := by
    simpa only [hlen, transferResult, fanoutResult, copyResult, readRegs_reset, hfinal] using copy
  have total := move.trans copy'
  convert total using 1 ; omega

theorem copyProgram_trace {r s : ℕ} (src dst tmp : Fin s) (value present : Fin r)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst) (hvp : value ≠ present)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) (htmp : stk tmp = []) :
    Trace (copyProgram src dst tmp value present) (7 * (stk src).length + 4)
      ⟨some 0, regs, stk⟩ (copyResult 7 src dst value present regs stk) :=
  copy_trace _ src dst tmp value present 0 1 2 3 4 5 6 7 hsd hst htd hvp
    rfl rfl rfl rfl rfl rfl rfl regs stk htmp

/-- A routine boundary can be turned into a terminating execution by executing
the caller's halt instruction, with exactly one additional transition. -/
theorem halt_after_trace {r s l : ℕ} (p : Program r s l) {n : ℕ}
    {start finish : Cfg r s l} (h : Trace p n start finish) (label : Fin l)
    (hpc : finish.pc = some label) (hcode : p.code label = .halt) :
    Trace p (n + 1) start {finish with pc := none} :=
  h.trans (.cons (step_code p finish label .halt hpc hcode) (.refl _))

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

namespace Add

abbrev Config := SubexponentialSAT.BitProgram.Cfg 8 3 13

def cfg (pc : Option (Fin 13)) (r : Regs) (xs ys out : List Bool) : Config :=
  ⟨pc, r, stackState xs ys out⟩

def readRegisters (r : Regs) (a b : Option Bool) : Regs :=
  SubexponentialSAT.BitProgram.readRegs (SubexponentialSAT.BitProgram.readRegs r 1 3 a) 2 4 b

def roundRegisters (r : Regs) (a b : Option Bool) : Regs :=
  let ra := readRegisters r a b
  let rt := Function.update ra 5 (ra 1 ^^ ra 2)
  let ru := Function.update rt 6 (rt 1 && rt 2)
  let rv := Function.update ru 7 (ru 5 && ru 0)
  let rs := Function.update rv 1 (rv 5 ^^ rv 0)
  Function.update rs 0 (rs 6 ^^ rs 7)

@[simp] theorem roundRegisters_carry (r : Regs) (a b : Option Bool) :
    roundRegisters r a b 0 = fastCarry (a.getD false) (b.getD false) (r 0) := by
  simp [roundRegisters, readRegisters, SubexponentialSAT.BitProgram.readRegs, fastCarry]

@[simp] theorem roundRegisters_sum (r : Regs) (a b : Option Bool) :
    roundRegisters r a b 1 = sumBit (a.getD false) (b.getD false) (r 0) := by
  simp [roundRegisters, readRegisters, SubexponentialSAT.BitProgram.readRegs, sumBit]

theorem round_left (r : Regs) (a : Bool) (xs ys out : List Bool) :
    Trace (SubexponentialSAT.BitProgram.step program) 9
      (cfg (some 0) r (a :: xs) ys out)
      (cfg (some 0) (roundRegisters r (some a) ys.head?)
        xs ys.tail (sumBit a (ys.headD false) (r 0) :: out)) := by
  apply Trace.of_iterate
  cases ys <;>
    simp [Function.iterate_succ_apply, SubexponentialSAT.BitProgram.step, SubexponentialSAT.BitProgram.execInstr,
      program, cfg, roundRegisters, readRegisters, SubexponentialSAT.BitProgram.readRegs, sumBit]

theorem round_right (r : Regs) (b : Bool) (ys out : List Bool) :
    Trace (SubexponentialSAT.BitProgram.step program) 10
      (cfg (some 0) r [] (b :: ys) out)
      (cfg (some 0) (roundRegisters r none (some b))
        [] ys (sumBit false b (r 0) :: out)) := by
  apply Trace.of_iterate
  simp [Function.iterate_succ_apply, SubexponentialSAT.BitProgram.step, SubexponentialSAT.BitProgram.execInstr,
    program, cfg, roundRegisters, readRegisters, SubexponentialSAT.BitProgram.readRegs, sumBit]

theorem finish (r : Regs) (out : List Bool) :
    SubexponentialSAT.BitProgram.RunsIn program 7 (cfg (some 0) r [] [] out)
      (cfg none (readRegisters r none none) [] []
        (if r 0 then true :: out else out)) := by
  cases hc : r 0 with
  | false =>
      refine ⟨6, by decide, ?_⟩
      apply Trace.of_iterate
      simp [Function.iterate_succ_apply, SubexponentialSAT.BitProgram.step, SubexponentialSAT.BitProgram.execInstr,
        program, cfg, readRegisters, SubexponentialSAT.BitProgram.readRegs, hc]
  | true =>
      refine ⟨7, le_rfl, ?_⟩
      apply Trace.of_iterate
      simp [Function.iterate_succ_apply, SubexponentialSAT.BitProgram.step, SubexponentialSAT.BitProgram.execInstr,
        program, cfg, readRegisters, SubexponentialSAT.BitProgram.readRegs, hc]

theorem run_right (r : Regs) (ys out : List Bool) :
    ∃ rf : Regs, SubexponentialSAT.BitProgram.RunsIn program (10 * (ys.length + 1))
      (cfg (some 0) r [] ys out)
      (cfg none rf [] [] ((carryAdd (r 0) ys).reverse ++ out)) := by
  induction ys generalizing r out with
  | nil =>
      refine ⟨readRegisters r none none, ?_⟩
      have h := (finish r out).mono (show 7 ≤ 10 * (([] : List Bool).length + 1) by decide)
      cases hc : r 0 <;> simpa [carryAdd, hc] using h
  | cons b ys ih =>
      obtain ⟨rf, hr⟩ := ih (roundRegisters r none (some b))
        (sumBit false b (r 0) :: out)
      have hs : SubexponentialSAT.BitProgram.RunsIn program 10
          (cfg (some 0) r [] (b :: ys) out)
          (cfg (some 0) (roundRegisters r none (some b))
            [] ys (sumBit false b (r 0) :: out)) :=
        ⟨10, le_rfl, round_right r b ys out⟩
      refine ⟨rf, ?_⟩
      have ht := hs.trans hr
      have hcost : 10 + 10 * (ys.length + 1) =
          10 * ((b :: ys).length + 1) := by simp; omega
      rw [hcost] at ht
      simpa [carryAdd, roundRegisters_carry, fastCarry_eq, List.reverse_cons,
        List.append_assoc] using ht

/-- A complete execution to the halted state, for arbitrary operand lengths. -/
theorem run (r : Regs) (xs ys out : List Bool) :
    ∃ rf : Regs, SubexponentialSAT.BitProgram.RunsIn program (10 * (max xs.length ys.length + 1))
      (cfg (some 0) r xs ys out)
      (cfg none rf [] [] ((addCarry (r 0) xs ys).reverse ++ out)) := by
  induction xs generalizing r ys out with
  | nil => simpa [addCarry] using run_right r ys out
  | cons a xs ih =>
      obtain ⟨rf, hr⟩ := ih (roundRegisters r (some a) ys.head?) ys.tail
        (sumBit a (ys.headD false) (r 0) :: out)
      have hs : SubexponentialSAT.BitProgram.RunsIn program 10
          (cfg (some 0) r (a :: xs) ys out)
          (cfg (some 0) (roundRegisters r (some a) ys.head?)
            xs ys.tail (sumBit a (ys.headD false) (r 0) :: out)) :=
        ⟨9, by decide, round_left r a xs ys out⟩
      refine ⟨rf, ?_⟩
      have ht := hs.trans hr
      have hcost : 10 + 10 * (max xs.length ys.tail.length + 1) =
          10 * (max (a :: xs).length ys.length + 1) := by
        cases ys <;> simp [max_add_add_right] <;> omega
      rw [hcost] at ht
      cases ys <;>
        simpa [addCarry, roundRegisters_carry, fastCarry_eq, List.reverse_cons,
          List.append_assoc, max_add_add_right] using ht

theorem littleEndian_run (r : Regs) (xs ys : List Bool) :
    ∃ rf : Regs, SubexponentialSAT.BitProgram.RunsIn littleEndianProgram
      (16 * (max xs.length ys.length + 1))
      ⟨some 0, r, stackState xs ys []⟩
      ⟨none, rf, stackState (addCarry (r 0) xs ys) [] []⟩ := by
  obtain ⟨rf, hr⟩ := run r xs ys []
  let word := addCarry (r 0) xs ys
  let reverseProgram :=
    SubexponentialSAT.StackRoutines.transferProgram (2 : Fin 3) 0 (1 : Fin 8) 3
  have ht := SubexponentialSAT.StackRoutines.transferProgram_trace (2 : Fin 3) 0 (1 : Fin 8) 3
    (by decide) (by decide) rf (stackState [] [] word.reverse)
  have hh := SubexponentialSAT.StackRoutines.halt_after_trace reverseProgram ht 3 rfl rfl
  have hs : SubexponentialSAT.BitProgram.RunsIn reverseProgram (3 * word.length + 3)
      (SubexponentialSAT.ProgramLinking.enter reverseProgram (cfg none rf [] [] word.reverse))
      ⟨none, SubexponentialSAT.BitProgram.readRegs rf 1 3 none, stackState word [] []⟩ := by
    refine ⟨3 * word.reverse.length + 2 + 1, by simp, ?_⟩
    simpa [SubexponentialSAT.StackRoutines.transferResult, SubexponentialSAT.StackRoutines.transferStacks,
      SubexponentialSAT.ProgramLinking.enter, cfg, reverseProgram,
      SubexponentialSAT.StackRoutines.transferProgram] using hh
  have hr' : SubexponentialSAT.BitProgram.RunsIn program (10 * (max xs.length ys.length + 1))
      (cfg (some 0) r xs ys []) (cfg none rf [] [] word.reverse) := by
    simpa [word] using hr
  have hc := SubexponentialSAT.ProgramLinking.link_runsIn program reverseProgram hr' rfl hs
  have hlen := length_addCarry (r 0) xs ys
  refine ⟨SubexponentialSAT.BitProgram.readRegs rf 1 3 none, ?_⟩
  apply SubexponentialSAT.Computation.RunsIn.mono ?_ (show
      10 * (max xs.length ys.length + 1) + (3 * word.length + 3) ≤
        16 * (max xs.length ys.length + 1) by dsimp [word]; omega)
  simpa [littleEndianProgram, reverseProgram, SubexponentialSAT.ProgramLinking.relabelCfg,
    SubexponentialSAT.ProgramLinking.relocatePc, SubexponentialSAT.StackRoutines.transferProgram, cfg] using hc

end Add

namespace Mul

abbrev Config := SubexponentialSAT.BitProgram.Cfg 8 6 32

/-- The six ports are multiplier, shifted multiplicand, accumulator, copy,
copy scratch, and reversed sum. Every instruction acts on Boolean data only. -/
def program : SubexponentialSAT.BitProgram.Program 8 6 32 where
  inputStack := 0
  outputStack := 2
  entry := 0
  code q := match q.val with
    | 0 => .pop 0 1 3 1
    | 1 => .branch 3 2 29
    | 2 => .branch 1 3 27
    | 3 => .pop 1 1 3 4
    | 4 => .branch 3 5 6
    | 5 => .push 4 1 3
    | 6 => .pop 4 1 3 7
    | 7 => .branch 3 8 10
    | 8 => .push 1 1 9
    | 9 => .push 3 1 6
    | 10 => .set 0 false 11
    | 11 => .pop 2 1 3 12
    | 12 => .pop 3 2 4 13
    | 13 => .branch 3 15 14
    | 14 => .branch 4 15 21
    | 15 => .bxor 5 1 2 16
    | 16 => .band 6 1 2 17
    | 17 => .band 7 5 0 18
    | 18 => .bxor 1 5 0 19
    | 19 => .bxor 0 6 7 20
    | 20 => .push 5 1 11
    | 21 => .branch 0 22 23
    | 22 => .push 5 0 23
    | 23 => .goto 24
    | 24 => .pop 5 1 3 25
    | 25 => .branch 3 26 27
    | 26 => .push 2 1 24
    | 27 => .set 1 false 28
    | 28 => .push 1 1 0
    | 29 => .pop 1 1 3 30
    | 30 => .branch 3 29 31
    | _ => .halt

def cfg (pc : Option (Fin 32)) (r : Regs) (xs ys acc cp tmp rev : List Bool) : Config :=
  ⟨pc, r, stackState xs ys acc cp tmp rev⟩

def loopCfg (r : Regs) (xs ys acc : List Bool) : Config :=
  cfg (some 0) r xs ys acc [] [] []

theorem add_code : SubexponentialSAT.ProgramLinking.CodeEmbedding Add.program program
    id addStack addLabel (some 24) := by
  intro q
  fin_cases q <;> rfl

theorem embed_add (pc : Option (Fin 13)) (r rf : Regs)
    (xs ys acc cp tmp rev : List Bool) :
    SubexponentialSAT.ProgramLinking.embedCfg id addStack addLabel (some 24)
      (cfg (some 0) r xs ys [] [] tmp []) (Add.cfg pc rf acc cp rev) =
      cfg (SubexponentialSAT.ProgramLinking.relocatePc addLabel (some 24) pc)
        rf xs ys acc cp tmp rev := by
  simp [SubexponentialSAT.ProgramLinking.embedCfg, cfg, Add.cfg, extend_addStack]

/-- The adder is installed as literal instructions in this program's table. -/
theorem add_block (r : Regs) (xs ys acc cp tmp rev : List Bool) :
    ∃ rf : Regs, SubexponentialSAT.BitProgram.RunsIn program (10 * (max acc.length cp.length + 1))
      (cfg (some 11) r xs ys acc cp tmp rev)
      (cfg (some 24) rf xs ys [] [] tmp ((addCarry (r 0) acc cp).reverse ++ rev)) := by
  obtain ⟨rf, hr⟩ := Add.run r acc cp rev
  have ht := SubexponentialSAT.ProgramLinking.relocate_runsIn Add.program program
    id addStack addLabel (some 24) (cfg (some 0) r xs ys [] [] tmp [])
    Function.injective_id addStack_injective add_code hr
  refine ⟨rf, ?_⟩
  have hz : addLabel (0 : Fin 13) = (11 : Fin 32) := by
    apply Fin.ext
    simp [addLabel]
  simpa only [embed_add, SubexponentialSAT.ProgramLinking.relocatePc,
    hz] using ht

theorem copy_block (r : Regs) (xs ys acc : List Bool) :
    SubexponentialSAT.BitProgram.Trace program (7 * ys.length + 4)
      (cfg (some 3) r xs ys acc [] [] [])
      (cfg (some 10) (SubexponentialSAT.BitProgram.readRegs r 1 3 none) xs ys acc ys [] []) := by
  have h := SubexponentialSAT.StackRoutines.copy_trace program 1 3 4 1 3 3 4 5 6 7 8 9 10
    (by decide) (by decide) (by decide) (by decide)
    rfl rfl rfl rfl rfl rfl rfl r (stackState xs ys acc [] [] []) rfl
  simpa [SubexponentialSAT.StackRoutines.copyResult, SubexponentialSAT.StackRoutines.copyStacks, cfg] using h

theorem transfer_block (r : Regs) (xs ys word : List Bool) :
    SubexponentialSAT.BitProgram.Trace program (3 * word.length + 2)
      (cfg (some 24) r xs ys [] [] [] word.reverse)
      (cfg (some 27) (SubexponentialSAT.BitProgram.readRegs r 1 3 none) xs ys word [] [] []) := by
  have h := SubexponentialSAT.StackRoutines.transfer_trace program 5 2 1 3 24 25 26 27
    (by decide) (by decide) rfl rfl rfl r (stackState xs ys [] [] [] word.reverse)
  simpa [SubexponentialSAT.StackRoutines.transferResult, SubexponentialSAT.StackRoutines.transferStacks, cfg] using h

theorem enter_round (r : Regs) (b : Bool) (xs ys acc : List Bool) :
    SubexponentialSAT.BitProgram.Trace program 3 (loopCfg r (b :: xs) ys acc)
      (cfg (some (if b then 3 else 27))
        (SubexponentialSAT.BitProgram.readRegs r 1 3 (some b)) xs ys acc [] [] []) := by
  let r' := SubexponentialSAT.BitProgram.readRegs r 1 3 (some b)
  have h₁ : SubexponentialSAT.BitProgram.step program (loopCfg r (b :: xs) ys acc) =
      some (cfg (some 1) r' xs ys acc [] [] []) := by
    have h := SubexponentialSAT.BitProgram.step_code program (loopCfg r (b :: xs) ys acc)
      0 (.pop 0 1 3 1) rfl rfl
    simpa [SubexponentialSAT.BitProgram.execInstr, loopCfg, cfg, r'] using h
  have h₂ : SubexponentialSAT.BitProgram.step program (cfg (some 1) r' xs ys acc [] [] []) =
      some (cfg (some 2) r' xs ys acc [] [] []) := by
    have h := SubexponentialSAT.BitProgram.step_code program (cfg (some 1) r' xs ys acc [] [] [])
      1 (.branch 3 2 29) rfl rfl
    simpa [SubexponentialSAT.BitProgram.execInstr, cfg, r', SubexponentialSAT.BitProgram.readRegs] using h
  have h₃ : SubexponentialSAT.BitProgram.step program (cfg (some 2) r' xs ys acc [] [] []) =
      some (cfg (some (if b then 3 else 27)) r' xs ys acc [] [] []) := by
    have h := SubexponentialSAT.BitProgram.step_code program (cfg (some 2) r' xs ys acc [] [] [])
      2 (.branch 1 3 27) rfl rfl
    cases b <;>
      simpa [SubexponentialSAT.BitProgram.execInstr, cfg, r', SubexponentialSAT.BitProgram.readRegs] using h
  exact .cons h₁ (.cons h₂ (.cons h₃ (.refl _)))

theorem reset_carry (r : Regs) (xs ys acc : List Bool) :
    SubexponentialSAT.BitProgram.Trace program 1 (cfg (some 10) r xs ys acc ys [] [])
      (cfg (some 11) (Function.update r 0 false) xs ys acc ys [] []) := by
  apply Trace.of_iterate
  simp [ SubexponentialSAT.BitProgram.step, SubexponentialSAT.BitProgram.execInstr,
    program, cfg]

theorem shift (r : Regs) (xs ys acc : List Bool) :
    SubexponentialSAT.BitProgram.Trace program 2 (cfg (some 27) r xs ys acc [] [] [])
      (loopCfg (Function.update r 1 false) xs (false :: ys) acc) := by
  apply Trace.of_iterate
  simp [Function.iterate_succ_apply, SubexponentialSAT.BitProgram.step, SubexponentialSAT.BitProgram.execInstr,
    program, cfg, loopCfg]

theorem finish (r : Regs) (ys acc : List Bool) :
    ∃ rf : Regs, SubexponentialSAT.BitProgram.Trace program (2 * ys.length + 5)
      (loopCfg r [] ys acc) (cfg none rf [] [] acc [] [] []) := by
  let r₁ := SubexponentialSAT.BitProgram.readRegs r 1 3 none
  have hp : SubexponentialSAT.BitProgram.Trace program 2 (loopCfg r [] ys acc)
      (cfg (some 29) r₁ [] ys acc [] [] []) := by
    apply Trace.of_iterate
    simp [Function.iterate_succ_apply, SubexponentialSAT.BitProgram.step, SubexponentialSAT.BitProgram.execInstr,
      program, cfg, loopCfg, r₁, SubexponentialSAT.BitProgram.readRegs]
  have hc := SubexponentialSAT.StackRoutines.clear_trace program 1 1 3 29 30 31 rfl rfl
    r₁ (stackState [] ys acc [] [] [])
  have hc' : SubexponentialSAT.BitProgram.Trace program (2 * ys.length + 2)
      (cfg (some 29) r₁ [] ys acc [] [] [])
      (cfg (some 31) (SubexponentialSAT.BitProgram.readRegs r₁ 1 3 none) [] [] acc [] [] []) := by
    simpa [SubexponentialSAT.StackRoutines.clearResult, SubexponentialSAT.StackRoutines.clearStacks, cfg] using hc
  have hh := SubexponentialSAT.StackRoutines.halt_after_trace program (hp.trans hc') 31 rfl rfl
  refine ⟨SubexponentialSAT.BitProgram.readRegs r₁ 1 3 none, ?_⟩
  convert hh using 1 <;> simp [cfg] ; omega

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

/-- Atom evaluation uses the existing instruction evaluator itself. -/
def eval {r s : ℕ} (a : Atom r s) (d : State r s) : State r s :=
  State.ofCfg (execInstr (a.instr (0 : Fin 1)) (d.withPC none))

end Atom

/-- Finite executions count exactly the atom and Boolean-test instructions. -/
inductive Eval {r s : ℕ} : Cmd r s → ℕ → State r s → State r s → Prop
  | skip (d) : Eval .skip 0 d d
  | atom (a) (d) : Eval (.atom a) 1 d (a.eval d)
  | seq {first second n m a b c} : Eval first n a b → Eval second m b c →
      Eval (.seq first second) (n + m) a c
  | ite_true {test yes no n a b} : a.regs test = true → Eval yes n a b →
      Eval (.ite test yes no) (n + 1) a b
  | ite_false {test yes no n a b} : a.regs test = false → Eval no n a b →
      Eval (.ite test yes no) (n + 1) a b
  | while_false {test body a} : a.regs test = false → Eval (.while test body) 1 a a
  | while_true {test body n m a b c} : a.regs test = true → Eval body n a b →
      Eval (.while test body) m b c → Eval (.while test body) (n + m + 1) a c

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

/-- A call's cost is its actual instruction-trace length, including the source
halt which becomes the compiled return jump. -/
inductive Eval {r s : ℕ} : Cmd r s → ℕ → State r s → State r s → Prop
  | base {c n a b} : StructuredProgram.Eval c n a b → Eval (.base c) n a b
  | call {labels} (p : Program r s labels) {n a b} :
      Trace p n (a.withPC (some p.entry)) (b.withPC none) → Eval (.call p) n a b
  | seq {first second n m a b c} : Eval first n a b → Eval second m b c →
      Eval (.seq first second) (n + m) a c
  | ite_true {test yes no n a b} : a.regs test = true → Eval yes n a b →
      Eval (.ite test yes no) (n + 1) a b
  | ite_false {test yes no n a b} : a.regs test = false → Eval no n a b →
      Eval (.ite test yes no) (n + 1) a b
  | while_false {test body a} : a.regs test = false → Eval (.while test body) 1 a a
  | while_true {test body n m a b c} : a.regs test = true → Eval body n a b →
      Eval (.while test body) m b c → Eval (.while test body) (n + m + 1) a c

/-- Mathematical data embedding for a subroutine's assigned ports. The finite
compiled instructions use the port maps directly; they never execute this
Function.extend expression. -/
noncomputable def embedState {r s R S : ℕ}
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (frame : State R S) (d : State r s) : State R S :=
  ⟨Function.extend register d.regs frame.regs, Function.extend stack d.stacks frame.stacks⟩

/-- Invoke an existing smaller program using fixed injective port assignments.
Its exact trace count is retained, and all unassigned caller data is framed. -/
theorem eval_call_lifted {r s l R S : ℕ} (p : Program r s l)
    (register : Fin r → Fin R) (stack : Fin s → Fin S) (frame : State R S)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    {n : ℕ} {a b : State r s}
    (h : Trace p n (a.withPC (some p.entry)) (b.withPC none)) :
    Eval (.call (ProgramLinking.liftProgram p register stack)) n
      (embedState register stack frame a) (embedState register stack frame b) := by
  apply Eval.call
  simpa [ProgramLinking.embedCfg, ProgramLinking.relocatePc, embedState,
    StructuredProgram.State.withPC, ProgramLinking.liftProgram] using
    ProgramLinking.liftProgram_trace p register stack (frame.withPC none) hregister hstack h

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

theorem copy_run {r s : ℕ} (src dst tmp : Fin s) (value present : Fin r)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst) (hvp : value ≠ present)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) (htmp : stk tmp = []) :
    Run (copyProgram src dst tmp value present) (7 * (stk src).length + 5)
      regs stk (readRegs regs value present none) (copyStacks src dst stk) := by
  have h := halt_after_trace _ (copyProgram_trace src dst tmp value present
    hsd hst htd hvp regs stk htmp) 7 rfl rfl
  simpa [Run, copyProgram, copyResult, Nat.add_assoc] using h

end SubexponentialSAT.ListRegisterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ProgramFrames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Extensional frame rules for connecting finite programs on fixed ports. -/

namespace SubexponentialSAT.ProgramLinking

open BitProgram

/-- Identify an embedded configuration by its assigned ports and its frame.
This is a proof rule; the executable table uses the finite port maps directly. -/
theorem embedCfg_eq_of_ports {r s l R S L : ℕ}
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L))
    (frame target : Cfg R S L) (source : Cfg r s l)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    (hpc : relocatePc label returnPc source.pc = target.pc)
    (hreg : ∀ i, target.regs (register i) = source.regs i)
    (hregFrame : ∀ i, (¬ ∃ j, register j = i) → target.regs i = frame.regs i)
    (hstack : ∀ i, target.stacks (stack i) = source.stacks i)
    (hstackFrame : ∀ i, (¬ ∃ j, stack j = i) → target.stacks i = frame.stacks i) :
    embedCfg register stack label returnPc frame source = target := by
  have hregs : (embedCfg register stack label returnPc frame source).regs = target.regs := by
    funext i
    classical
    by_cases hi : ∃ j, register j = i
    · obtain ⟨j, rfl⟩ := hi
      exact (embedCfg_register register stack label returnPc frame source hr j).trans
        (hreg j).symm
    · exact (embedCfg_register_frame register stack label returnPc frame source i hi).trans
        (hregFrame i hi).symm
  have hstacks : (embedCfg register stack label returnPc frame source).stacks = target.stacks := by
    funext i
    classical
    by_cases hi : ∃ j, stack j = i
    · obtain ⟨j, rfl⟩ := hi
      exact (embedCfg_stack register stack label returnPc frame source hs j).trans
        (hstack j).symm
    · exact (embedCfg_stack_frame register stack label returnPc frame source i hi).trans
        (hstackFrame i hi).symm
  cases target
  cases he : embedCfg register stack label returnPc frame source
  simp_all [embedCfg]

end SubexponentialSAT.ProgramLinking

namespace SubexponentialSAT.StructuredCalls

/-- The corresponding data-only frame rule for structured subroutine calls. -/
theorem embedState_eq_of_ports {r s R S : ℕ}
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (frame target : State R S) (source : State r s)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    (hreg : ∀ i, target.regs (register i) = source.regs i)
    (hregFrame : ∀ i, (¬ ∃ j, register j = i) → target.regs i = frame.regs i)
    (hstack : ∀ i, target.stacks (stack i) = source.stacks i)
    (hstackFrame : ∀ i, (¬ ∃ j, stack j = i) → target.stacks i = frame.stacks i) :
    embedState register stack frame source = target := by
  have h := ProgramLinking.embedCfg_eq_of_ports register stack (id : Fin 1 → Fin 1) none
    (frame.withPC none) (target.withPC none) (source.withPC none) hr hs rfl
    hreg hregFrame hstack hstackFrame
  exact congrArg StructuredProgram.State.ofCfg h

end SubexponentialSAT.StructuredCalls

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

theorem copyAt_eval {S : ℕ} (source target scratch : Fin S) (d : Data S)
    (hst : source ≠ target) (hss : source ≠ scratch) (hts : scratch ≠ target)
    (ht : d.stacks target = []) (hs : d.stacks scratch = []) :
    Eval (copyAt source target scratch) (7 * (d.stacks source).length + 5)
      d (afterCopy source target d) := by
  have h := ListRegisterProgram.copy_run source target scratch (0 : Fin 8) 1
    hst hss hts (by decide) d.regs d.stacks hs
  apply Eval.call
  simpa [afterCopy, ListRegisterProgram.Run, StructuredProgram.State.withPC,
    StackRoutines.copyStacks, ht] using h

def mulPorts {S : ℕ} (p : Ports S) : Fin 6 → Fin S :=
  ![p.work 0, p.work 1, p.out, p.work 2, p.work 3, p.work 4]

theorem mulPorts_injective {S : ℕ} (p : Ports S) : Function.Injective (mulPorts p) := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [mulPorts, p.work.injective.eq_iff, p.work_ne_out]

abbrev multiplyRaw {S : ℕ} (p : Ports S) : Cmd 8 S :=
  .call (ProgramLinking.liftProgram BinaryPrograms.Mul.program id (mulPorts p))

abbrev multiplyAt {S : ℕ} (p : Ports S) : Cmd 8 S :=
  .seq (copyAt p.left (p.work 0) (p.work 3))
    (.seq (copyAt p.right (p.work 1) (p.work 3)) (multiplyRaw p))

def mulReady {S : ℕ} (p : Ports S) (d : Data S) : Data S :=
  ⟨readRegs d.regs 0 1 none,
    Function.update (Function.update d.stacks (p.work 0) (d.stacks p.left))
      (p.work 1) (d.stacks p.right)⟩

theorem copy_mul_ready {S : ℕ} (p : Ports S) (d : Data S) :
    afterCopy p.right (p.work 1) (afterCopy p.left (p.work 0) d) = mulReady p d := by
  simp [afterCopy, mulReady, StackRoutines.readRegs_reset]

theorem copy_add_ready {S : ℕ} (p : Ports S) (d : Data S) :
    afterCopy p.right (p.work 1) (afterCopy p.left p.out d) = addReady p d := by
  simp [afterCopy, addReady, StackRoutines.readRegs_reset, p.out_ne_right.symm]

theorem embed_add_start {S : ℕ} (p : Ports S) (d : Data S) (hv : Valid p d) :
    embedState id (addPorts p) d
      ⟨(addReady p d).regs,
        BinaryPrograms.Add.stackState (d.stacks p.left) (d.stacks p.right) []⟩ =
      addReady p d := by
  apply embedState_eq_of_ports id (addPorts p) d _ _ Function.injective_id (addPorts_injective p)
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i
    fin_cases i <;> simp [addReady, addPorts, BinaryPrograms.Add.stackState,
      p.work.injective.eq_iff, p.work_ne_out, hv.2]
  · intro i hi
    have ho : i ≠ p.out := fun h => hi ⟨0, h.symm⟩
    have h1 : i ≠ p.work 1 := fun h => hi ⟨1, h.symm⟩
    simp [addReady, ho, h1]

theorem embed_add_finish {S : ℕ} (p : Ports S) (d : Data S) (hv : Valid p d)
    (rf : Fin 8 → Bool) (word : List Bool) :
    embedState id (addPorts p) d
      ⟨rf, BinaryPrograms.Add.stackState word [] []⟩ =
      (⟨rf, Function.update d.stacks p.out word⟩ : Data S) := by
  apply embedState_eq_of_ports id (addPorts p) d _ _ Function.injective_id (addPorts_injective p)
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i
    fin_cases i <;> simp [addPorts, BinaryPrograms.Add.stackState, p.work_ne_out, hv.2]
  · intro i hi
    have ho : i ≠ p.out := fun h => hi ⟨0, h.symm⟩
    simp [ho]

/-- Source-preserving binary addition, with an explicit carry reset before
the verified little-endian adder. -/
theorem addAt_eval {S : ℕ} (p : Ports S) (d : Data S) (hv : Valid p d) :
    ∃ (t : ℕ) (rf : Fin 8 → Bool) (word : List Bool),
      Eval (addAt p) t d ⟨rf, Function.update d.stacks p.out word⟩ ∧
      BinaryArithmetic.toNat word =
        BinaryArithmetic.toNat (d.stacks p.left) + BinaryArithmetic.toNat (d.stacks p.right) ∧
      word.length ≤ (d.stacks p.left).length + (d.stacks p.right).length + 1 ∧
      t ≤ 100 * ((d.stacks p.left).length + (d.stacks p.right).length + 1) ^ 2 := by
  let first := afterCopy p.left p.out d
  have hleft := copyAt_eval p.left p.out (p.work 3) d
    p.out_ne_left.symm (left_ne_work p 3) (p.work_ne_out 3) hv.1 (hv.2 3)
  have hrightWord : first.stacks p.right = d.stacks p.right := by
    simp [first, afterCopy, p.out_ne_right.symm]
  have hright := copyAt_eval p.right (p.work 1) (p.work 3) first
    (right_ne_work p 1) (right_ne_work p 3)
    (by simp [p.work.injective.eq_iff])
    (by simp [first, afterCopy, p.work_ne_out, hv.2])
    (by simp [first, afterCopy, p.work_ne_out, hv.2])
  rw [hrightWord] at hright
  change Eval _ _ first
    (afterCopy p.right (p.work 1) (afterCopy p.left p.out d)) at hright
  rw [copy_add_ready] at hright
  have hcarry : Eval (.base (.atom (.set 0 false))) 1 (addReady p d) (addReady p d) := by
    have he : (StructuredProgram.Atom.set 0 false).eval (addReady p d) = addReady p d := by
      simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr,
        addReady, readRegs ]
    simpa only [he] using Eval.base
      (StructuredProgram.Eval.atom (StructuredProgram.Atom.set 0 false) (addReady p d))
  let word := BinaryArithmetic.add (d.stacks p.left) (d.stacks p.right)
  obtain ⟨rf, t, htime, htrace⟩ := BinaryPrograms.Add.littleEndian_run (addReady p d).regs
    (d.stacks p.left) (d.stacks p.right)
  have hw : BinaryArithmetic.addCarry ((addReady p d).regs 0)
      (d.stacks p.left) (d.stacks p.right) = word := by
    simp [addReady, readRegs, word, BinaryArithmetic.add]
  rw [hw] at htrace
  have hcall := eval_call_lifted BinaryPrograms.Add.littleEndianProgram id (addPorts p) d
    Function.injective_id (addPorts_injective p)
    (a := ⟨(addReady p d).regs,
      BinaryPrograms.Add.stackState (d.stacks p.left) (d.stacks p.right) []⟩)
    (b := ⟨rf, BinaryPrograms.Add.stackState word [] []⟩) htrace
  rw [embed_add_start p d hv, embed_add_finish p d hv] at hcall
  refine ⟨(7 * (d.stacks p.left).length + 5) +
      ((7 * (d.stacks p.right).length + 5) + (1 + t)), rf, word,
    hleft.seq (hright.seq (hcarry.seq hcall)), BinaryArithmetic.toNat_add _ _, ?_, ?_⟩
  · have hlen := BinaryArithmetic.length_add (d.stacks p.left) (d.stacks p.right)
    dsimp [word]
    have hm : max (d.stacks p.left).length (d.stacks p.right).length ≤
        (d.stacks p.left).length + (d.stacks p.right).length := by omega
    omega
  · have hm : max (d.stacks p.left).length (d.stacks p.right).length ≤
        (d.stacks p.left).length + (d.stacks p.right).length := by omega
    nlinarith

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

abbrev Data (S : ℕ) := State 8 S

abbrev atom {S : ℕ} (a : StructuredProgram.Atom 8 S) : Cmd 8 S := .base (.atom a)

end SubexponentialSAT.ArithmeticExpressionSupport

end OAI.Algorithms
end


