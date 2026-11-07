-- Prove2me | Definitions.Def_PopRAM_WordRAM
-- name    : PopRAM_WordRAM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:22:12.525207+00:00
-- url     : https://prove2.me/theorems/0b934887-b2ef-4555-a6e3-6d92e57e98e9
-- title:
--   The $w$-RAM: Cook–Reckhow instructions on two's-complement $w$-bit words (Table 1)
-- statement:
--   The **$w$-RAM** has registers indexed by natural numbers, each holding a signed $w$-bit word in two's-complement (U2) encoding; all registers start at $0$. A program is a finite list of instructions (Table 1):
--
--   1. $\mathrm{LOAD}(C, r_d)$: $C\to r_d$, for an integer constant $C$ of the program;
--   2. $\mathrm{ADD}(r_{s1},r_{s2},r_d)$ and $\mathrm{SUB}(r_{s1},r_{s2},r_d)$: $[r_{s1}]\pm[r_{s2}]\to r_d$, modulo $2^w$;
--   3. $\mathrm{COPY}(i,r_p,d,r_d)$: $[[r_p]]\to r_d$, and $\mathrm{COPY}(d,r_s,i,r_p)$: $[r_s]\to[[r_p]]$ (indirect addressing);
--   4. $\mathrm{JGE}(r,I_z)$: jump to instruction $z$ if $[r]\ge 0$, otherwise continue;
--   5. $\mathrm{READ}(r_d)$: read the next input value into $r_d$; $\mathrm{PRINT}(r_s)$: output the value of $r_s$.
--
--   The first six are the **RAM instructions**. Execution starts at instruction $0$ and stops when the instruction pointer reaches the end of the program. With $\rho$ registers, an execution step **faults** if it uses a direct register index $\ge\rho$, an indirect address whose signed value is outside $\{0,\dots,\rho-1\}$, a register that has not been written before (including a pointer used for indirect addressing), or a READ when no input is left. The machine counts the executed READ, PRINT and RAM instructions.
--
--   `Behaves` expresses items 1, 3 and 4 of Definition 1 for one input tuple $k=(k_1,\dots,k_{T_R})$: the program runs without fault until it halts, having executed exactly $T_R$ READs, at most $T_{RAM}$ RAM instructions and exactly $T_P$ PRINTs, and every printed value lies in $[0,2^{w-1})$. `progOut` is the list of printed values.
--
--   **Formalization Note** Words are `BitVec w`; LOAD writes the $w$-bit two's-complement word of $C$ (constants "are extended by copies of the sign bit", p.16), READ writes the $w$-bit word of the input value, JGE tests the signed value, PRINT records the signed value. A jump past the end of the program halts it.
-- source:
--   Gąsieniec, Grodzicki, Stachowiak, Efficient Stable Word-RAM Simulation by Population Protocols, arXiv:2611.06178 (preprint, held version, sha256 f13223b33593e77d2342fbfab2d49c58efd6035c06f316456f76030e0dca9acd), §2, p.5 (PDF p.6), Table 1; Definition 1, items 3–4, p.6 (PDF p.7)

import Mathlib

set_option autoImplicit false

namespace PopRAM

/-! # The w-RAM (Cook–Reckhow instruction set, Table 1)

Gąsieniec, Grodzicki, Stachowiak, *Efficient Stable Word-RAM Simulation by Population Protocols*,
arXiv:2611.06178 (held version, sha256 f13223b3…), §2, p.5 (PDF p.6), Table 1, and Definition 1,
pp.5–6 (PDF pp.6–7). Registers "store signed w-bit words in two's-complement (U2) encoding.
Arithmetic is performed modulo 2^w." "The execution terminates when ip reaches the end of the
program."

**Formalization Note**
- Words are `BitVec w`; registers are `ℕ → BitVec w`, all `0` at the start. `LOAD(C, rd)` writes
  `BitVec.ofInt w C` (the constant `C` is part of the fixed code and is "extended by copies of the
  sign bit", p.16). `ADD`/`SUB` are `BitVec` addition/subtraction (mod `2^w`). `JGE(r, z)` jumps to
  `z` iff `[r].toInt ≥ 0`. `READ(rd)` writes `BitVec.ofNat w k` for the next input value `k`.
  `PRINT(rs)` appends `[rs].toInt` to the output list.
- `copyInd rp rd` is `COPY(i, rp, d, rd)` (`[[rp]] → rd`); `storeInd rs rp` is `COPY(d, rs, i, rp)`
  (`[rs] → [[rp]]`).
- The machine also records which registers have been written, and counts executed READ, PRINT and
  RAM instructions (LOAD, ADD, SUB, both COPYs, JGE are the RAM instructions, p.5).
- A step **faults** (`ramStep` returns `none`) on: a direct register index `≥ ρ`; an indirect address
  whose signed value is outside `[0, ρ)`; reading a register never written (operands of ADD/SUB,
  the pointer and the source of either COPY, the registers read by JGE and PRINT); a READ with no
  input left. These are the violations of items 3–4 of Definition 1.
- A state with `ip ≥ code.length` is halted, and `ramStep` leaves it unchanged; a jump target past the
  end therefore halts the program. -/

/-- The instructions of Table 1. -/
inductive Instr where
  /-- `LOAD(C, rd)`: `C → rd` -/
  | load (c : ℤ) (rd : ℕ)
  /-- `ADD(rs1, rs2, rd)`: `[rs1] + [rs2] → rd` -/
  | add (rs1 rs2 rd : ℕ)
  /-- `SUB(rs1, rs2, rd)`: `[rs1] − [rs2] → rd` -/
  | sub (rs1 rs2 rd : ℕ)
  /-- `COPY(i, rp, d, rd)`: `[[rp]] → rd` -/
  | copyInd (rp rd : ℕ)
  /-- `COPY(d, rs, i, rp)`: `[rs] → [[rp]]` -/
  | storeInd (rs rp : ℕ)
  /-- `JGE(r, I_z)`: if `[r] ≥ 0` jump to instruction `z` -/
  | jge (r z : ℕ)
  /-- `READ(rd)`: read the next input value into `rd` -/
  | read (rd : ℕ)
  /-- `PRINT(rs)`: output the value of `rs` -/
  | print (rs : ℕ)
  deriving DecidableEq

/-- A machine state of the w-RAM. -/
structure MState (w : ℕ) where
  /-- instruction pointer -/
  ip : ℕ
  /-- register contents -/
  reg : ℕ → BitVec w
  /-- registers written so far -/
  written : Finset ℕ
  /-- input values not yet read -/
  input : List ℕ
  /-- printed values, in order -/
  output : List ℤ
  /-- executed READ instructions -/
  nRead : ℕ
  /-- executed PRINT instructions -/
  nPrint : ℕ
  /-- executed RAM instructions -/
  nRAM : ℕ

namespace MState

variable {w : ℕ}

/-- The initial state on input list `k`: `ip = 0`, all registers `0` and unwritten. -/
def init (k : List ℕ) : MState w :=
  ⟨0, fun _ => 0, ∅, k, [], 0, 0, 0⟩

/-- Write `v` into register `r`. -/
def set (s : MState w) (r : ℕ) (v : BitVec w) : MState w :=
  { s with reg := Function.update s.reg r v, written := insert r s.written }

/-- Advance `ip` by one and count one RAM instruction. -/
def nextRAM (s : MState w) : MState w :=
  { s with ip := s.ip + 1, nRAM := s.nRAM + 1 }

end MState

/-- The register index denoted by the word `x`, if its signed value lies in `[0, ρ)`. -/
def addr {w : ℕ} (ρ : ℕ) (x : BitVec w) : Option ℕ :=
  if 0 ≤ x.toInt ∧ x.toInt < ρ then some x.toInt.toNat else none

/-- Register `r` may be read: it is an index below `ρ` and has been written. -/
def readable {w : ℕ} (ρ : ℕ) (s : MState w) (r : ℕ) : Prop := r < ρ ∧ r ∈ s.written

instance {w : ℕ} (ρ : ℕ) (s : MState w) (r : ℕ) : Decidable (readable ρ s r) := by
  unfold readable; infer_instance

/-- One step of program `code` with `ρ` registers; `none` is a fault. -/
def ramStep {w : ℕ} (code : List Instr) (ρ : ℕ) (s : MState w) : Option (MState w) :=
  match code[s.ip]? with
  | none => some s
  | some (Instr.load c rd) =>
      if rd < ρ then some (s.set rd (BitVec.ofInt w c)).nextRAM else none
  | some (Instr.add rs1 rs2 rd) =>
      if readable ρ s rs1 ∧ readable ρ s rs2 ∧ rd < ρ then
        some (s.set rd (s.reg rs1 + s.reg rs2)).nextRAM else none
  | some (Instr.sub rs1 rs2 rd) =>
      if readable ρ s rs1 ∧ readable ρ s rs2 ∧ rd < ρ then
        some (s.set rd (s.reg rs1 - s.reg rs2)).nextRAM else none
  | some (Instr.copyInd rp rd) =>
      if readable ρ s rp ∧ rd < ρ then
        match addr ρ (s.reg rp) with
        | some a => if a ∈ s.written then some (s.set rd (s.reg a)).nextRAM else none
        | none => none
      else none
  | some (Instr.storeInd rs rp) =>
      if readable ρ s rs ∧ readable ρ s rp then
        match addr ρ (s.reg rp) with
        | some a => some (s.set a (s.reg rs)).nextRAM
        | none => none
      else none
  | some (Instr.jge r z) =>
      if readable ρ s r then
        some { s with
          ip := if 0 ≤ (s.reg r).toInt then z else s.ip + 1
          nRAM := s.nRAM + 1 }
      else none
  | some (Instr.read rd) =>
      if rd < ρ then
        match s.input with
        | x :: rest =>
            some { (s.set rd (BitVec.ofNat w x)) with
              ip := s.ip + 1
              input := rest
              nRead := s.nRead + 1 }
        | [] => none
      else none
  | some (Instr.print rs) =>
      if readable ρ s rs then
        some { s with
          ip := s.ip + 1
          output := s.output ++ [(s.reg rs).toInt]
          nPrint := s.nPrint + 1 }
      else none

/-- The state after `t` steps on input list `k`, or `none` if a fault occurred. -/
def runSteps (w : ℕ) (code : List Instr) (ρ : ℕ) (k : List ℕ) : ℕ → Option (MState w)
  | 0 => some (MState.init k)
  | t + 1 => (runSteps w code ρ k t).bind (ramStep code ρ)

/-- Items 1, 3 and 4 of Definition 1 for one input tuple `k`: the program runs without fault until
it halts, having executed exactly `TR` READs, at most `TRAM` RAM instructions and exactly `TP`
PRINTs, every printed value lying in `[0, 2^(w-1))`. (With `TR` input values, `nRead = TR` means
every value has been read.) -/
def Behaves (code : List Instr) (w TR TRAM TP ρ : ℕ) (k : Fin TR → ℕ) : Prop :=
  ∃ t : ℕ, ∃ s : MState w, runSteps w code ρ (List.ofFn k) t = some s ∧
    code.length ≤ s.ip ∧ s.nRead = TR ∧ s.nRAM ≤ TRAM ∧ s.nPrint = TP ∧
    ∀ v ∈ s.output, 0 ≤ v ∧ v < 2 ^ (w - 1)

/-- The `j`-th printed value after `T` steps (as a natural number), `0` if there is none. When
`Behaves` holds and `T ≥ TR + TRAM + TP`, the machine has halted by step `T` and this is the
program's `j`-th output. -/
def progOut (code : List Instr) (w ρ : ℕ) (k : List ℕ) (T j : ℕ) : ℕ :=
  match runSteps w code ρ k T with
  | some s => (s.output.getD j 0).toNat
  | none => 0

end PopRAM


