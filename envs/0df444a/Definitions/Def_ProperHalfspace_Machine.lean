-- Prove2me | Definitions.Def_ProperHalfspace_Machine
-- name    : ProperHalfspace_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:01:47.49765+00:00
-- url     : https://prove2.me/theorems/7f1e8170-cd76-425a-b668-96ed114dc437
-- title:
--   The membership-query real RAM with fair coins
-- statement:
--   The page says that all running-time bounds "count arithmetic operations in the real-RAM model" and names no instruction set. This definition fixes one: a unit-cost machine with finitely many instructions, real registers, integer pointers, a real and an integer memory, exact $+,-,\times,\div$ (with $x/0=0$), rational literals, comparisons and jumps, pointer addition and subtraction, the pointer-to-real cast, fair coins, a membership query and a halt instruction.
--
--   A query reads a point $x\in\{\pm1\}^n$ from $n$ memory cells by their signs and writes $f(x)$ to a register. It counts as one query and costs $n$ units of work. Every other executed instruction costs one unit. The oracle $f$ enters the semantics only there. A program is a finite list of instructions, no instruction carries a function, and every real literal is rational.
--
--   The machine has no square root, floor, real-to-integer cast, exponential, logarithm, eigensolver, uniform real draw or pointer multiplication, so a program can obtain nothing for free. A theorem of the form "there is a program" is stronger for each instruction left out.
--
--   The module also fixes the input and output layouts of Theorem 1, Proposition 10 and Proposition 16, and the probability of an event of the coin tape, as a count over the $2^B$ tapes of length $B$.
--
--   **Formalization Note** The real-RAM core is the published `SmaleNinth.RAMInstr`. An invalid program counter is stuck and charged, so only `halt` halts, and a halted machine stutters at no cost. A coin costs one unit of work, so a run within $B$ units reads at most $B$ coins.
-- source:
--   De, Mossel, Nadimpalli, Neeman, Efficient Proper Agnostic Learning of Halfspaces, arXiv:2611.02344 (Nov. 1, 2026), Theorem 1 and the sentence after it, p.2

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_ProperHalfspace_Cube

namespace ProperHalfspace

/-!
# The membership-query real RAM with fair coins

De, Mossel, Nadimpalli, Neeman, arXiv:2611.02344 (Nov. 1, 2026), Theorem 1, p.2: "All running-time bounds in this paper count
arithmetic operations in the real-RAM model".

**Formalization Note.** The page names no instruction set. This module fixes the strong reading: a unit-cost real RAM, the
published `SmaleNinth.RAMInstr` core (exact `+ − × ÷` with `x/0 = 0`, indirect memory, pointers, jumps), with
* integer pointer `+` and `−` and an integer memory;
* the pointer-to-real cast, one way only: there is no floor and no real-to-integer cast;
* fair coins as the only randomness;
* the membership query `query`, the only instruction that reads `f`;
* `halt`.
There is no square root, exponential, logarithm, eigensolver, uniform real draw or pointer multiplication. `Admissible`
restricts the program's real literals to rationals and excludes the core's `accept`/`reject`. Every instruction left out
makes the theorems about this machine stronger.

Costs: `query` adds one to `queries` and `n` to `work`, since it reads `n` cells. Every other executed instruction adds one
to `work`, including jumps, coins and `halt`. An invalid program counter is stuck and charged, so only `halt` halts. A
halted machine stutters at no cost.

Randomness: a coin costs one unit of work, so a run within `B` units of work reads at most `B` coins. `tapeProb B` is the
count over the tapes `Fin B → Bool`, whose later positions read `false`.
-/

/-- One instruction: a core real-RAM instruction or one of the additions of this module. -/
inductive Instr : Type
  /-- A core instruction of `SmaleNinth.RAMInstr`. -/
  | core (i : SmaleNinth.RAMInstr)
  /-- `p[d] := p[a] + p[b]`. -/
  | pointerAdd (d a b : ℕ)
  /-- `p[d] := p[a] − p[b]`. -/
  | pointerSub (d a b : ℕ)
  /-- `p[d] := I[p[a]]`, integer memory. -/
  | integerLoad (d a : ℕ)
  /-- `I[p[a]] := p[b]`, integer memory. -/
  | integerStore (a b : ℕ)
  /-- `r[d] := (p[a] : ℝ)`. -/
  | pointerReal (d a : ℕ)
  /-- `r[d] := 1` or `0`, from the next tape bit. -/
  | coin (d : ℕ)
  /-- `r[d] := f(x)`, where `xᵢ = 1` if `M[p[q] + i] ≥ 0` and `xᵢ = −1` otherwise, for `i < n`. -/
  | query (d q : ℕ)
  /-- Stop. -/
  | halt

/-- A program: a finite list of instructions, executed from position `0`. -/
abbrev Program := List Instr

/-- Real literals are rational, and the core `accept`/`reject` do not occur. No instruction carries a function. -/
def Admissible (P : Program) : Prop :=
  ∀ i ∈ P, (∀ d c, i = .core (.const d c) → ∃ q : ℚ, c = (q : ℝ)) ∧
    i ≠ .core .accept ∧ i ≠ .core .reject

/-- The program uses neither coins nor queries. -/
def NoOracle (P : Program) : Prop :=
  ∀ i ∈ P, (∀ d, i ≠ .coin d) ∧ ∀ d q, i ≠ .query d q

/-- The core instruction at a program position; the additions of this module are not core instructions, and `step` never
calls `RAMStep` on them. -/
def Instr.coreOf : Instr → SmaleNinth.RAMInstr
  | .core i => i
  | _ => .accept

/-- A configuration of the machine. -/
structure State where
  /-- The core configuration: program counter, real registers, pointers, real memory. -/
  cfg : SmaleNinth.RAMConfig
  /-- The integer memory. -/
  imem : ℤ → ℤ
  /-- The number of coins read. -/
  coins : ℕ
  /-- The number of membership queries. -/
  queries : ℕ
  /-- The units of work. -/
  work : ℕ
  /-- Whether `halt` has been executed. -/
  halted : Bool

/-- The cube point read by `query` from the `n` memory cells starting at `base`. -/
noncomputable def queryPoint (n : ℕ) (mem : ℤ → ℝ) (base : ℤ) : Cube n :=
  fun i => if 0 ≤ mem (base + (i : ℕ)) then 1 else -1

/-- Advance by one instruction, at one unit of work, with new registers and pointers. -/
def State.next (s : State) (regs : ℕ → ℝ) (ptrs : ℕ → ℤ) : State :=
  { s with cfg := ⟨s.cfg.pc + 1, regs, ptrs, s.cfg.mem⟩, work := s.work + 1 }

/-- One step. A halted state stutters at no cost. An invalid program counter is stuck and charged. The oracle `f` occurs only
in the `query` branch. -/
noncomputable def step (P : Program) {n : ℕ} (f : Cube n → ℝ) (tape : ℕ → Bool) (s : State) : State :=
  if s.halted then s else
    let r := s.cfg.regs
    let p := s.cfg.ptrs
    match P[s.cfg.pc]? with
    | none => { s with work := s.work + 1 }
    | some (.core _) =>
        { s with cfg := SmaleNinth.RAMStep (P.map Instr.coreOf) s.cfg, work := s.work + 1 }
    | some (.pointerAdd d a b) => s.next r (Function.update p d (p a + p b))
    | some (.pointerSub d a b) => s.next r (Function.update p d (p a - p b))
    | some (.integerLoad d a) => s.next r (Function.update p d (s.imem (p a)))
    | some (.integerStore a b) => { s.next r p with imem := Function.update s.imem (p a) (p b) }
    | some (.pointerReal d a) => s.next (Function.update r d (p a : ℝ)) p
    | some (.coin d) =>
        { s.next (Function.update r d (if tape s.coins then 1 else 0)) p with coins := s.coins + 1 }
    | some (.query d q) =>
        { s with
          cfg := ⟨s.cfg.pc + 1, Function.update r d (f (queryPoint n s.cfg.mem (p q))), p, s.cfg.mem⟩
          queries := s.queries + 1
          work := s.work + n }
    | some .halt => { s with halted := true, work := s.work + 1 }

/-- The state after `t` steps from `s₀`. -/
noncomputable def run (P : Program) {n : ℕ} (f : Cube n → ℝ) (tape : ℕ → Bool) (s₀ : State) (t : ℕ) : State :=
  (step P f tape)^[t] s₀

/-- The start state with the given pointers and real memory; registers, integer memory and counters are `0`. -/
def initState (ptrs : ℕ → ℤ) (mem : ℤ → ℝ) : State where
  cfg := ⟨0, fun _ => 0, ptrs, mem⟩
  imem := fun _ => 0
  coins := 0
  queries := 0
  work := 0
  halted := false

/-- The layout of Theorem 1's input: pointer `0` holds `n`; `M[0] = ε`; everything else is `0`. -/
noncomputable def goalInit (n : ℕ) (ε : ℝ) : State :=
  initState (Function.update (fun _ => 0) 0 (n : ℤ)) (Function.update (fun _ => 0) 0 ε)

/-- The layout of Proposition 16's input: pointer `0` holds `n`; `M[0..3] = ρ, β, κ, δ`; everything else is `0`. -/
noncomputable def estimatorInit (n : ℕ) (ρ β κ δ : ℝ) : State :=
  initState (Function.update (fun _ => 0) 0 (n : ℤ)) fun a =>
    if a = 0 then ρ else if a = 1 then β else if a = 2 then κ else if a = 3 then δ else 0

/-- The real memory of Proposition 10's input: row `j < m` occupies the `D + 1` cells from `j (D + 1)`, holding `φ_j` and then
`y_j`; everything else is `0`. -/
noncomputable def sampleMem {m D : ℕ} (φ : Fin m → Fin D → ℝ) (y : Fin m → ℝ) (a : ℤ) : ℝ :=
  if 0 ≤ a then
    if hj : a.toNat / (D + 1) < m then
      if hr : a.toNat % (D + 1) < D then φ ⟨a.toNat / (D + 1), hj⟩ ⟨a.toNat % (D + 1), hr⟩
      else y ⟨a.toNat / (D + 1), hj⟩
    else 0
  else 0

/-- The layout of Proposition 10's input: pointer `0` holds `m`, pointer `1` holds `D`, memory `sampleMem`. -/
noncomputable def ermInit {m D : ℕ} (φ : Fin m → Fin D → ℝ) (y : Fin m → ℝ) : State :=
  initState (Function.update (Function.update (fun _ => 0) 0 (m : ℤ)) 1 (D : ℤ)) (sampleMem φ y)

/-- The output normal: at `halt`, `M[i] = wᵢ` for `i < d`. -/
def decodeNormal (d : ℕ) (s : State) : Fin d → ℝ := fun i => s.cfg.mem ((i : ℕ) : ℤ)

/-- The output threshold: at `halt`, `M[d] = θ`. -/
def decodeThreshold (d : ℕ) (s : State) : ℝ := s.cfg.mem (d : ℤ)

/-- The output matrix of Proposition 16: at `halt`, `M[i n + j] = M̂ᵢⱼ`. -/
def decodeMatrix (n : ℕ) (s : State) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => s.cfg.mem (((i : ℕ) * n + (j : ℕ) : ℕ) : ℤ)

/-- A `B`-bit tape extended by `false`. -/
def extendTape {B : ℕ} (tape : Fin B → Bool) (i : ℕ) : Bool :=
  if h : i < B then tape ⟨i, h⟩ else false

open Classical in
/-- The probability of an event of the tape, as a count over the `2^B` tapes of length `B`. -/
noncomputable def tapeProb (B : ℕ) (A : (ℕ → Bool) → Prop) : ℝ :=
  ((Finset.univ.filter fun τ : Fin B → Bool => A (extendTape τ)).card : ℝ) / (2 : ℝ) ^ B

end ProperHalfspace


