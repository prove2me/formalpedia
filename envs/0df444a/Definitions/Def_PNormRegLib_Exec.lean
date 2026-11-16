-- Prove2me | Definitions.Def_PNormRegLib_Exec
-- name    : PNormRegLib_Exec
-- status  : Definition
-- author  : @milia
-- created : 2026-11-15T08:10:13.463451+00:00
-- url     : https://prove2.me/theorems/35c6d67a-3210-4a09-acb8-16ab7868b939
-- title:
--   Single-instruction semantics of the real RAM
-- statement:
--   Consider the real RAM of the definition `PNormReg_Machine`. For an instruction $\iota$, a coin tape $\omega:\mathbb N\to\{0,1\}$ and a machine state $s$, let $\mathrm{exec}_\omega(\iota,s)$ be the state obtained by executing $\iota$ once in $s$, regardless of which instruction the program counter of $s$ points to:
--
--   1. the core arithmetic, memory, pointer and jump instructions act as in `SmaleNinth.RAMStep`;
--   2. pointer addition and subtraction, integer load and store, the pointer-to-real cast, $\sqrt{\cdot}$, the real power and the coin act as in `PNormReg.step`;
--   3. the work counter grows by $1$; `halt` sets the halted flag; `coin` writes bit number $\mathrm{cursor}$ of $\omega$ and advances the cursor.
--
--   The map $\mathrm{coreExec}(\iota,c)$ is the same operation for a core instruction $\iota$ acting on a core configuration $c$.
--
--   These maps separate *what an instruction does* from *which instruction is fetched*. Statements about single instructions, step lemmas for concrete programs, and simulations between programs can then be proved without unfolding the program lookup.
--
--   **Formalization Note.** `exec` does not consult the halted flag. It is meant for running states, where it agrees with one machine step; see `PNormRegLib.step_eq_exec`.
-- source:
--   Restatement of PNormReg.step (definition PNormReg_Machine) and SmaleNinth.RAMStep (definition SmaleNinth_RealRAM), split by instruction; original library definition, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions'.

import Mathlib
import Definitions.Def_PNormReg_Machine

namespace PNormRegLib

open PNormReg SmaleNinth

/-- The effect of one core instruction `i` on a configuration: the body of `SmaleNinth.RAMStep` for
that instruction, without the program lookup. -/
noncomputable def coreExec (i : RAMInstr) (s : RAMConfig) : RAMConfig :=
  match i with
  | .const dst c => ⟨s.pc + 1, Function.update s.regs dst c, s.ptrs, s.mem⟩
  | .add dst i j => ⟨s.pc + 1, Function.update s.regs dst (s.regs i + s.regs j), s.ptrs, s.mem⟩
  | .sub dst i j => ⟨s.pc + 1, Function.update s.regs dst (s.regs i - s.regs j), s.ptrs, s.mem⟩
  | .mul dst i j => ⟨s.pc + 1, Function.update s.regs dst (s.regs i * s.regs j), s.ptrs, s.mem⟩
  | .div dst i j => ⟨s.pc + 1, Function.update s.regs dst (s.regs i / s.regs j), s.ptrs, s.mem⟩
  | .load dst q => ⟨s.pc + 1, Function.update s.regs dst (s.mem (s.ptrs q)), s.ptrs, s.mem⟩
  | .store q i => ⟨s.pc + 1, s.regs, s.ptrs, Function.update s.mem (s.ptrs q) (s.regs i)⟩
  | .pset q c => ⟨s.pc + 1, s.regs, Function.update s.ptrs q c, s.mem⟩
  | .pcopy q q' => ⟨s.pc + 1, s.regs, Function.update s.ptrs q (s.ptrs q'), s.mem⟩
  | .pinc q => ⟨s.pc + 1, s.regs, Function.update s.ptrs q (s.ptrs q + 1), s.mem⟩
  | .pdec q => ⟨s.pc + 1, s.regs, Function.update s.ptrs q (s.ptrs q - 1), s.mem⟩
  | .jle i target => if s.regs i ≤ 0 then ⟨target, s.regs, s.ptrs, s.mem⟩ else
      ⟨s.pc + 1, s.regs, s.ptrs, s.mem⟩
  | .pjle q q' target => if s.ptrs q ≤ s.ptrs q' then ⟨target, s.regs, s.ptrs, s.mem⟩ else
      ⟨s.pc + 1, s.regs, s.ptrs, s.mem⟩
  | .accept => s
  | .reject => s

/-- The effect of executing the instruction `ins` in a running (not halted) state: the branch of
`PNormReg.step` for that instruction, without the program lookup. Work grows by one, `halt` sets the
halted flag, and `coin` reads bit `cursor` of the tape `ω`. -/
noncomputable def exec (ω : ℕ → Bool) (ins : Instr) (s : State) : State :=
  match ins with
  | .core i => ⟨coreExec i s.core, s.integerMemory, s.cursor, s.halted, s.work + 1⟩
  | .pointerAdd d a b => ⟨⟨s.core.pc + 1, s.core.regs,
      Function.update s.core.ptrs d (s.core.ptrs a + s.core.ptrs b), s.core.mem⟩,
      s.integerMemory, s.cursor, s.halted, s.work + 1⟩
  | .pointerSub d a b => ⟨⟨s.core.pc + 1, s.core.regs,
      Function.update s.core.ptrs d (s.core.ptrs a - s.core.ptrs b), s.core.mem⟩,
      s.integerMemory, s.cursor, s.halted, s.work + 1⟩
  | .integerLoad d a => ⟨⟨s.core.pc + 1, s.core.regs,
      Function.update s.core.ptrs d (s.integerMemory (s.core.ptrs a)), s.core.mem⟩,
      s.integerMemory, s.cursor, s.halted, s.work + 1⟩
  | .integerStore a b => ⟨⟨s.core.pc + 1, s.core.regs, s.core.ptrs, s.core.mem⟩,
      Function.update s.integerMemory (s.core.ptrs a) (s.core.ptrs b), s.cursor, s.halted,
      s.work + 1⟩
  | .pointerReal d a => ⟨⟨s.core.pc + 1, Function.update s.core.regs d (s.core.ptrs a : ℝ),
      s.core.ptrs, s.core.mem⟩, s.integerMemory, s.cursor, s.halted, s.work + 1⟩
  | .sqrt d a => ⟨⟨s.core.pc + 1, Function.update s.core.regs d (Real.sqrt (s.core.regs a)),
      s.core.ptrs, s.core.mem⟩, s.integerMemory, s.cursor, s.halted, s.work + 1⟩
  | .rpow d a b => ⟨⟨s.core.pc + 1,
      Function.update s.core.regs d (|s.core.regs a| ^ s.core.regs b),
      s.core.ptrs, s.core.mem⟩, s.integerMemory, s.cursor, s.halted, s.work + 1⟩
  | .coin d => ⟨⟨s.core.pc + 1, Function.update s.core.regs d (if ω s.cursor then 1 else 0),
      s.core.ptrs, s.core.mem⟩, s.integerMemory, s.cursor + 1, s.halted, s.work + 1⟩
  | .halt => ⟨⟨s.core.pc + 1, s.core.regs, s.core.ptrs, s.core.mem⟩, s.integerMemory, s.cursor,
      true, s.work + 1⟩

end PNormRegLib


