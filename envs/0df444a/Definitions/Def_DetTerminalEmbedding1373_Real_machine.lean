-- Prove2me | Definitions.Def_DetTerminalEmbedding1373_Real_machine
-- name    : DetTerminalEmbedding1373_Real_machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:23:29.876196+00:00
-- url     : https://prove2.me/theorems/df9eebe1-9831-44c1-a6bc-1181cd7aea67
-- title:
--   Deterministic real arithmetic programs and charged execution
-- statement:
--   A finite program operates on real registers, integer address registers and random-access real and integer memory. It reuses the published scalar real-RAM instructions and adds square root, exponential, integer address arithmetic and integer-to-real conversion. There is no sampling, real-to-integer conversion, logarithm, Gaussian integration, or optimization oracle. Real literals in admissible programs are rational. Each executed instruction, including address arithmetic, memory access, comparison, jump and halt, costs one unit:
--
--   $$W_{t+1}=W_t+1$$
--
--   until explicit halt. Invalid program counters are stuck and charged. The denotation uses the least halting time, with a zero-time default only for nonhalting executions; the algorithmic theorem targets prove halting. This separates the allowed computation from its correctness and resource guarantees.
-- source:
--   Vladimir Braverman, Kuan Cheng, Jiaqing Zhu, STOC 2027 submission #1373 (October 2026), pp. 3, 15–22, §1.1 arithmetic model; §4 and §6 operational encoding; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1373.pdf

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM

set_option autoImplicit false

namespace DetTerminalEmbedding1373.Real

/-- The published scalar real RAM, extended by deterministic indexed memory,
integer address arithmetic, integer-to-real conversion, sqrt and exp. No real-to-integer
conversion, randomness, logarithm, minimization or function-valued instruction. -/
inductive Instr where
  | core (i : SmaleNinth.RAMInstr)
  | padd (dst a b : ℕ)
  | psub (dst a b : ℕ)
  | pmul (dst a b : ℕ)
  | rload (dst bank address : ℕ)
  | rstore (bank address src : ℕ)
  | iload (dst bank address : ℕ)
  | istore (bank address src : ℕ)
  | cast (dst src : ℕ)
  | sqrt (dst src : ℕ)
  | exp (dst src : ℕ)
  | jump (target : ℕ)
  | halt

abbrev Program := List Instr

/-- Only rational real literals and explicit halt are allowed. This restricts code,
never the real input. Integer multiplication is used solely for memory addresses. -/
def Admissible (P : Program) : Prop :=
  ∀ i ∈ P, match i with
    | .core (.const _ x) => ∃ q : ℚ, x = (q : ℝ)
    | .core .accept | .core .reject => False
    | _ => True

structure MachineState where
  core : SmaleNinth.RAMConfig
  reals : ℕ → ℤ → ℝ
  ints : ℕ → ℤ → ℤ
  halted : Bool
  work : ℕ

def coreCode (P : Program) : SmaleNinth.RAMProgram :=
  P.map fun i => match i with | .core j => j | _ => .const 0 0

/-- Every instruction, address calculation, load, store, branch and halt costs one.
Invalid program counters are stuck and charged. Halted states stutter for free. -/
noncomputable def machineStep (P : Program) (s : MachineState) : MachineState :=
  if s.halted then s else
    let t : MachineState := { s with
      core := {s.core with pc := s.core.pc + 1}
      work := s.work + 1 }
    match P[s.core.pc]? with
    | none => {s with work := s.work + 1}
    | some (.core _) => {t with core := SmaleNinth.RAMStep (coreCode P) s.core}
    | some (.padd d a b) => {t with core := {t.core with
        ptrs := Function.update s.core.ptrs d (s.core.ptrs a + s.core.ptrs b)}}
    | some (.psub d a b) => {t with core := {t.core with
        ptrs := Function.update s.core.ptrs d (s.core.ptrs a - s.core.ptrs b)}}
    | some (.pmul d a b) => {t with core := {t.core with
        ptrs := Function.update s.core.ptrs d (s.core.ptrs a * s.core.ptrs b)}}
    | some (.rload d b a) => {t with core := {t.core with
        regs := Function.update s.core.regs d (s.reals b (s.core.ptrs a))}}
    | some (.rstore b a v) => {t with reals := (Function.update s.reals b
        (Function.update (s.reals b) (s.core.ptrs a) (s.core.regs v)))}
    | some (.iload d b a) => {t with core := {t.core with
        ptrs := Function.update s.core.ptrs d (s.ints b (s.core.ptrs a))}}
    | some (.istore b a v) => {t with ints := (Function.update s.ints b
        (Function.update (s.ints b) (s.core.ptrs a) (s.core.ptrs v)))}
    | some (.cast d a) => {t with core := {t.core with
        regs := Function.update s.core.regs d (s.core.ptrs a : ℝ)}}
    | some (.sqrt d a) => {t with core := {t.core with
        regs := Function.update s.core.regs d (Real.sqrt (s.core.regs a))}}
    | some (.exp d a) => {t with core := {t.core with
        regs := Function.update s.core.regs d (Real.exp (s.core.regs a))}}
    | some (.jump a) => {t with core := {t.core with pc := a}}
    | some .halt => {t with halted := true}

noncomputable def machineRun (P : Program) (s : MachineState) (t : ℕ) : MachineState :=
  (machineStep P)^[t] s

/-- A terminating run, with its actual instruction count. No cost certificate is an input. -/
def Halts (P : Program) (s : MachineState) (t : ℕ) : Prop :=
  (machineRun P s t).halted = true ∧ (machineRun P s t).work = t

open Classical in
/-- Least halting time, if there is one; zero otherwise. This denotes the operational
program and is never an instruction available to it. All resource targets prove halting. -/
noncomputable def haltTime (P : Program) (s : MachineState) : ℕ :=
  if h : ∃ t, (machineRun P s t).halted = true then Nat.find h else 0

noncomputable def finalState (P : Program) (s : MachineState) : MachineState :=
  machineRun P s (haltTime P s)

end DetTerminalEmbedding1373.Real


