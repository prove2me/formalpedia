-- Prove2me | Definitions.Def_FasterWCTFPTAS_Main_Machine
-- name    : FasterWCTFPTAS_Main_Machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:05:57.307487+00:00
-- url     : https://prove2.me/theorems/9f84d31c-1df6-458a-bf2d-9da4472e25a3
-- title:
--   Deterministic unit-cost real RAM with rational literals and a work-bounded floor
-- statement:
--   The paper states its running times in $O(\cdot)$ without naming a machine model; they are the time bounds of the cited $\varepsilon$-kernel constructions of computational geometry together with elementary dynamic-programming bookkeeping. This definition fixes a **deterministic unit-cost real RAM**.
--
--   The machine extends the published real-RAM core `SmaleNinth.RAMInstr`: exact $+,-,\times,\div$ on real registers, real literals, indirect real memory $M[p_q]$ through integer pointer registers, pointer set/copy/increment/decrement, and comparison jumps on reals and on pointers. It adds
--
--   1. pointer addition and subtraction $p_d := p_a \pm p_b$;
--   2. the cast $r_d := p_q$ from a pointer to a real register;
--   3. a **bounded floor** $p_d := \lfloor r_s\rfloor$, executed only when $|\lfloor r_s\rfloor| \le K\,(w+L+1)$, where $w$ is the number of instructions executed so far, $L$ is the input length and the constant $K$ is written in the instruction (so it is fixed together with the program); otherwise the machine is stuck forever;
--   4. `halt`.
--
--   A program is **admissible** when every real literal is rational and the core's `accept`/`reject` instructions do not occur. There is no square root, exponential, logarithm or random draw. Every executed instruction costs one unit, and only `halt` halts.
--
--   A run on an input list $x_1,\dots,x_L$ of reals starts with all registers and pointers equal to $0$, memory cell $0$ holding $L$ and cells $1,\dots,L$ holding the input. The **output** is read at the first halted state: it is the list of memory cells $-1,-2,\dots,-\ell$, where $\ell$ is the value of pointer register $0$. "The program halts within $B$ steps" means that the halted state is reached after at most $B$ executed instructions.
--
--   This is the machine on which the running-time clauses of Lemmas 3.4–3.6, Corollary 4.7 and Theorem 1.1 are stated.
--
--   **Formalization Note** The floor is needed for the linear-time bucketing in Chan's planar construction (Lemma 3.5), on which the $m=2$ clause of Theorem 1.1 rests. Its result is bounded by the work done, so a floor returns only an integer the program could have reached by counting; a floor without this bound, combined with unit-cost multiplication, would allow bit extraction from exponentially long numbers and could trivialize running-time statements about NP-hard problems. Division by zero gives $0$ (Lean's convention).
-- source:
--   Karl Bringmann, Anita Dürr, Karol Węgrzycki, STOC 2027 submission #1072 (October 2026), p. 1 (PDF p. 2), Theorem 1.1; p. 11 (PDF p. 12), Lemmas 3.4–3.6 (machine model not named in the source; reading R1 of the mission plan)

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM

set_option autoImplicit false

namespace FasterWCTFPTAS.Main

/-!
# The machine model (reading R1)

The paper (Bringmann–Dürr–Węgrzycki, STOC 2027 submission #1072) states its running times in
O(·) without naming a machine; its time bounds are those of the cited ε-kernel constructions
[AdFM17, Cha06] from computational geometry plus elementary dynamic-programming bookkeeping.
We fix a **deterministic unit-cost real RAM**.

The machine extends the published real-RAM core `SmaleNinth.RAMInstr` (exact `+ − × ÷` on real
registers, real literals, indirect real memory `M[p[q]]` through integer pointer registers,
pointer set/copy/increment/decrement, comparison jumps on reals and on pointers) with:
* `padd`, `psub`: pointer arithmetic `p[d] := p[a] ± p[b]`;
* `ofPtr d q`: `r[d] := p[q]` (pointer to real);
* `floorPtr d r K`: `p[d] := ⌊r[r]⌋`, executed only when `|⌊r[r]⌋| ≤ K · (w + L + 1)`, where `w` is
  the number of instructions executed so far and `L` the input length; otherwise the machine is
  **stuck** (it repeats the instruction forever and never halts). The constant `K` is part of the
  instruction, hence fixed together with the program. A bounded floor returns only an integer
  the program could already have reached by counting, so it yields no bit extraction from huge
  reals;
* `halt`.

`Admissible` requires every real literal to be **rational** and forbids the core's
`accept`/`reject`. There is no square root, exponential, logarithm or randomness. Division by
zero gives `0` (Lean's convention). Every executed instruction costs one unit; a program counter
outside the program is stuck. Only `halt` halts.

**Input and output layout.** A run on the input list `xs` starts with all registers and pointers
`0`, memory cell `0` holding the length of `xs` and cells `1, …, |xs|` holding `xs`; every other
cell is `0`. At the first halted state the output is the list of the real memory cells
`-1, -2, …, -ℓ`, where `ℓ` is the value of pointer register `0` (`ℓ ≤ 0` gives the empty list).
-/

namespace Machine

/-- An instruction of the real RAM. -/
inductive Instr where
  /-- A `SmaleNinth` core instruction. -/
  | core (instruction : SmaleNinth.RAMInstr)
  /-- `p[dst] := p[a] + p[b]`. -/
  | padd (dst a b : ℕ)
  /-- `p[dst] := p[a] - p[b]`. -/
  | psub (dst a b : ℕ)
  /-- `r[dst] := p[src]`. -/
  | ofPtr (dst src : ℕ)
  /-- `p[dst] := ⌊r[src]⌋` if `|⌊r[src]⌋| ≤ K · (work + inputLength + 1)`; stuck otherwise. -/
  | floorPtr (dst src K : ℕ)
  /-- Halt. -/
  | halt

/-- A program: a finite list of instructions, executed from position `0`. -/
abbrev Program := List Instr

/-- Every real literal is rational, and the core's `accept`/`reject` do not occur. -/
def Admissible (P : Program) : Prop :=
  ∀ op ∈ P, match op with
    | .core (.const _ value) => ∃ q : ℚ, value = (q : ℝ)
    | .core .accept | .core .reject => False
    | _ => True

/-- The core table of `P` (extension instructions become placeholders that the core never
executes, since the step function dispatches them itself). -/
def coreProgram (P : Program) : SmaleNinth.RAMProgram :=
  P.map fun op => match op with
    | .core i => i
    | _ => .const 0 0

/-- A machine state. -/
structure State where
  /-- Program counter, real registers, pointer registers, real memory. -/
  core : SmaleNinth.RAMConfig
  /-- Halted flag. -/
  halted : Bool
  /-- Number of executed instructions. -/
  work : ℕ
  /-- Length of the input list (fixed during the run). -/
  inputLength : ℕ

/-- One step of `P`. A halted state does not change. -/
noncomputable def step (P : Program) (s : State) : State :=
  if s.halted then s else
    let t : State := { s with
      work := s.work + 1
      core := { s.core with pc := s.core.pc + 1 } }
    match P[s.core.pc]? with
    | none => { s with work := s.work + 1 }
    | some (.core _) => { t with core := SmaleNinth.RAMStep (coreProgram P) s.core }
    | some (.padd d a b) =>
        { t with core := { t.core with
            ptrs := Function.update s.core.ptrs d (s.core.ptrs a + s.core.ptrs b) } }
    | some (.psub d a b) =>
        { t with core := { t.core with
            ptrs := Function.update s.core.ptrs d (s.core.ptrs a - s.core.ptrs b) } }
    | some (.ofPtr d a) =>
        { t with core := { t.core with
            regs := Function.update s.core.regs d (s.core.ptrs a : ℝ) } }
    | some (.floorPtr d a K) =>
        if |⌊s.core.regs a⌋| ≤ (K : ℤ) * ((s.work : ℤ) + (s.inputLength : ℤ) + 1) then
          { t with core := { t.core with
              ptrs := Function.update s.core.ptrs d ⌊s.core.regs a⌋ } }
        else { s with work := s.work + 1 }
    | some .halt => { t with halted := true }

/-- The initial state on input `xs`: memory cell `0` holds `|xs|`, cells `1, …, |xs|` hold `xs`. -/
noncomputable def initState (xs : List ℝ) : State :=
  ⟨⟨0, fun _ => 0, fun _ => 0,
    fun z => if z = 0 then (xs.length : ℝ) else if 0 < z then xs.getD (z.toNat - 1) 0 else 0⟩,
    false, 0, xs.length⟩

/-- The state after `k` steps on input `xs`. -/
noncomputable def run (P : Program) (xs : List ℝ) (k : ℕ) : State :=
  (step P)^[k] (initState xs)

/-- The run halts within `B` executed instructions. -/
def HaltsWithin (P : Program) (xs : List ℝ) (B : ℝ) : Prop :=
  ∃ k : ℕ, (k : ℝ) ≤ B ∧ (run P xs k).halted = true

/-- The output list of a state: memory cells `-1, …, -ℓ`, `ℓ = p[0]`. -/
noncomputable def outputOf (s : State) : List ℝ :=
  List.ofFn fun i : Fin (s.core.ptrs 0).toNat => s.core.mem (-((i : ℤ) + 1))

open Classical in
/-- The output of the run (at its first halted state), `none` if it never halts. -/
noncomputable def output (P : Program) (xs : List ℝ) : Option (List ℝ) :=
  if h : ∃ k, (run P xs k).halted = true then some (outputOf (run P xs (Nat.find h)))
  else none

end Machine

end FasterWCTFPTAS.Main


