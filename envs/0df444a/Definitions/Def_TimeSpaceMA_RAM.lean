-- Prove2me | Definitions.Def_TimeSpaceMA_RAM
-- name    : TimeSpaceMA_RAM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:56:10.514915+00:00
-- url     : https://prove2.me/theorems/35addda2-e578-4337-9330-aa7b2df5e828
-- title:
--   Log-cost RAM: programs, steps, costs
-- statement:
--   A **program** is a finite list of instructions over a memory of natural numbers: `const d c` ($M[d] := c$), `add d a b`, `monus d a b` ($M[d] := M[a] \pm M[b]$, truncated at $0$), `load d a` ($M[d] := M[M[a]]$), `store a b` ($M[M[a]] := M[b]$), `jle a b target`, `coin d` (reads the next bit of a coin tape into $M[d]$), and `halt`.
--
--   Each executed instruction adds to the accumulated cost `work` the amount $1$ plus the bit lengths of every address used and every value read or written. An invalid program counter is stuck and never halts. A program *runs to* a state if an iterate of the step reaches that state with the halted flag set. Initial memory contents are not charged; a cell is paid for when it is read.
--
--   The paper speaks of Arthur's and Merlin's running time without a machine. Log cost is what gives message length and time their meaning: no cell can hold a message for free, and no program is a function of the input in disguise. The model is polylogarithmically equivalent to a word RAM with $\Theta(\log T)$-bit words, which the $t^\varepsilon$ factors absorb.
-- source:
--   Williams, Xi, Short Non-Interactive Proofs for Time-Space Computations, STOC 2027 submission (manuscript sha256 184c2f95…), §3.7, pp.19–22 ("running time"; no machine is named)

import Mathlib

namespace TimeSpaceMA

/-- An instruction of the log-cost RAM. No constructor carries a function: a program is a finite
syntactic object. Cells hold natural numbers; `load` and `store` are indirect. -/
inductive Instr
  | const (d c : ℕ)
  | add (d a b : ℕ)
  | monus (d a b : ℕ)
  | load (d a : ℕ)
  | store (a b : ℕ)
  | jle (a b target : ℕ)
  | coin (d : ℕ)
  | halt

/-- A program of the log-cost RAM (Williams, Xi, STOC 2027 submission, manuscript sha256 184c2f95…:
the page gives Arthur's and Merlin's "running time" without a machine).

**Formalization Note** Each executed instruction costs 1 plus the bit lengths (`Nat.size`) of every
address used and every value read or written, so a cell cannot carry a message for free. There is no
multiplication: it is programmable at polylogarithmic overhead, which the `t^ε` factors absorb. The
model is polylog-equivalent to a word RAM with `Θ(log T)`-bit words; `paper.md`, decision 3. -/
abbrev Program := List Instr

/-- Machine state: program counter, memory, coin-tape cursor, halted flag, accumulated cost. -/
structure State where
  pc : ℕ
  mem : ℕ → ℕ
  cursor : ℕ
  halted : Bool
  work : ℕ

/-- The start state on a given memory. -/
def State.init (mem : ℕ → ℕ) : State := ⟨0, mem, 0, false, 0⟩

/-- One step with coin tape `τ`. A halted state stays; an invalid program counter is stuck and never
halts. -/
def Program.step (p : Program) (τ : ℕ → Bool) (st : State) : State :=
  if st.halted then st
  else
    match p[st.pc]? with
    | none => st
    | some (.const d c) =>
        { st with
          pc := st.pc + 1
          mem := Function.update st.mem d c
          work := st.work + 1 + d.size + c.size }
    | some (.add d a b) =>
        let u := st.mem a
        let v := st.mem b
        { st with
          pc := st.pc + 1
          mem := Function.update st.mem d (u + v)
          work := st.work + 1 + d.size + a.size + b.size + u.size + v.size + (u + v).size }
    | some (.monus d a b) =>
        let u := st.mem a
        let v := st.mem b
        { st with
          pc := st.pc + 1
          mem := Function.update st.mem d (u - v)
          work := st.work + 1 + d.size + a.size + b.size + u.size + v.size + (u - v).size }
    | some (.load d a) =>
        let u := st.mem a
        let v := st.mem u
        { st with
          pc := st.pc + 1
          mem := Function.update st.mem d v
          work := st.work + 1 + d.size + a.size + u.size + v.size }
    | some (.store a b) =>
        let u := st.mem a
        let v := st.mem b
        { st with
          pc := st.pc + 1
          mem := Function.update st.mem u v
          work := st.work + 1 + a.size + b.size + u.size + v.size }
    | some (.jle a b target) =>
        let u := st.mem a
        let v := st.mem b
        { st with
          pc := if u ≤ v then target else st.pc + 1
          work := st.work + 1 + a.size + b.size + u.size + v.size + target.size }
    | some (.coin d) =>
        let v := (τ st.cursor).toNat
        { st with
          pc := st.pc + 1
          mem := Function.update st.mem d v
          cursor := st.cursor + 1
          work := st.work + 1 + d.size + v.size }
    | some .halt =>
        { st with
          halted := true
          work := st.work + 1 }

/-- From memory `mem` with tape `τ`, the program halts in state `st`. A halted state is a fixed point
of the step, so `st` is unique. -/
def Program.RunsTo (p : Program) (τ : ℕ → Bool) (mem : ℕ → ℕ) (st : State) : Prop :=
  ∃ T : ℕ, (p.step τ)^[T] (State.init mem) = st ∧ st.halted = true

/-- The program has no `coin` instruction. -/
def Program.CoinFree (p : Program) : Prop :=
  ∀ d, Instr.coin d ∉ p

/-- The all-`false` tape, used to run coin-free programs. -/
def zeroTape : ℕ → Bool := fun _ => false

/-- The memory holding the list `l` from cell `0` on, zero elsewhere. Loading is free; a cell is paid
for when it is read. -/
def memOf (l : List ℕ) : ℕ → ℕ := fun i => l.getD i 0

end TimeSpaceMA


