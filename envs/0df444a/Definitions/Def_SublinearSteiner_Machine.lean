-- Prove2me | Definitions.Def_SublinearSteiner_Machine
-- name    : SublinearSteiner_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:39:31.448628+00:00
-- url     : https://prove2.me/theorems/7e472914-336a-49cd-99a1-aa583d7db6cb
-- title:
--   The distance-oracle real RAM with fair coins
-- statement:
--   The cost model of the mission's goal. The paper says "time" and names no machine; this is the strong reading.
--
--   A program is a finite list of instructions of a unit-cost real RAM: the published core `SmaleNinth.RAMInstr` (real arithmetic, pointer manipulation, indirect memory, conditional jumps), together with
--   1. pointer addition and subtraction, and an integer memory, which holds the input;
--   2. a cast from pointers to reals, one way only;
--   3. `coin`, a fair coin from a tape of random bits;
--   4. `query`, the distance oracle, the only instruction that reads the metric;
--   5. `halt`, which outputs a real number.
--
--   There is no floor, no real-to-integer cast, no pointer multiplication, no exp, log or square root, and no uniform real sample. `Admissible` requires the program's real literals to be rational and excludes the core's `accept` and `reject`.
--
--   Every executed instruction costs one unit of work, and each `query` is one query. The input is $n$ and the membership bits of $T$; the distance oracle is the only access to $w$.
--
--   **Formalization Note.** `budget C K n` is $\lceil Cn^{3/2}\log(n+2)^K\rceil$. A machine stuck at an invalid program counter is charged and never outputs. Sanity lemmas check that `Admissible` excludes an irrational literal, that work is at most the number of steps, and that the metric is read only in the `query` branch.
-- source:
--   Mahabadi, Roghani, Tarnawski, Vakilian, Tight Bounds for Sublinear Metric Steiner Tree, STOC 2027 submission (manuscript sha256 ae133037…), Theorem 1.1, p.1, with the distance-oracle model of p.1

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM

open scoped Classical

namespace SublinearSteiner

/-!
# The distance-oracle real RAM with fair coins

Mahabadi, Roghani, Tarnawski, Vakilian, *Tight Bounds for Sublinear Metric Steiner Tree*, STOC 2027
submission (manuscript sha256 ae133037…), Theorem 1.1, p.1, with the distance-oracle model of p.1: "an algorithm knows
`V` and `T` and may query any pair `{u, v}` to learn `w(u, v)`; its cost is the number of queries".

**Formalization Note.** The page says "time" and names no machine. This module fixes the strong reading: a unit-cost
real RAM, the published `SmaleNinth.RAMInstr` core, with
* integer pointer `+` and `−` and an integer memory, which holds the input;
* the pointer-to-real cast, one way only: there is no floor and no real-to-integer cast;
* fair coins as the only randomness (no uniform real sample);
* the distance oracle `query`, the only instruction that reads `w`, charged one query always;
* `halt`, which outputs a real and stops.
There is no pointer multiplication, exp, log or square root. `Admissible` restricts the program's real literals to
rationals and excludes the core's `accept`/`reject`. Each omitted instruction would give a stronger machine and hence a
weaker theorem.

Every executed instruction costs one unit of `work`, including jumps, coins, queries and `halt`. An invalid program
counter is stuck and charged; a machine that has halted stutters at no cost.

Input: `I 0 = n`; `I (1 + v) = 1` if `v ∈ T`, else `0`; everything else `0`. The real memory starts at `0`.

Randomness: a run of `B` steps reads at most `B` coins. The probability over a run is the count over the tapes
`Fin B → Bool`, later positions read `false`.
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
  /-- `r[d] := w(p[a], p[b])` if both pointers are in `Fin n`, else `0`; one query in every case. -/
  | query (d a b : ℕ)
  /-- Output `r[src]` and stop. -/
  | halt (src : ℕ)

/-- A program: a finite list of instructions, executed from position `0`. -/
abbrev Program := List Instr

/-- Real literals are rational, and the core `accept`/`reject` do not occur. -/
def Admissible (P : Program) : Prop :=
  ∀ i ∈ P, (∀ d c, i = .core (.const d c) → ∃ q : ℚ, c = (q : ℝ)) ∧
    i ≠ .core .accept ∧ i ≠ .core .reject

/-- The core instruction at a program position; the additions of this module are not core instructions, and `step`
never calls `RAMStep` on them. -/
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
  /-- The number of instructions executed. -/
  work : ℕ
  /-- The number of distance queries. -/
  queries : ℕ
  /-- The output, once halted. -/
  output : Option ℝ

/-- A pointer value as a point of `Fin n`. -/
def toPoint (n : ℕ) (x : ℤ) : Option (Fin n) :=
  if h : 0 ≤ x ∧ x.toNat < n then some ⟨x.toNat, h.2⟩ else none

/-- The distance oracle's answer on two pointer values. -/
noncomputable def oracleAnswer {n : ℕ} (w : Fin n → Fin n → ℝ) (x y : ℤ) : ℝ :=
  match toPoint n x, toPoint n y with
  | some u, some v => w u v
  | _, _ => 0

/-- Advance by one instruction with new registers and pointers. -/
def State.next (s : State) (regs : ℕ → ℝ) (ptrs : ℕ → ℤ) : State :=
  { s with cfg := ⟨s.cfg.pc + 1, regs, ptrs, s.cfg.mem⟩, work := s.work + 1 }

/-- One step. A halted state stutters at no cost. An invalid program counter is stuck and charged. -/
noncomputable def step (P : Program) {n : ℕ} (w : Fin n → Fin n → ℝ) (tape : ℕ → Bool) (s : State) : State :=
  match s.output with
  | some _ => s
  | none =>
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
    | some (.query d a b) =>
        { s.next (Function.update r d (oracleAnswer w (p a) (p b))) p with queries := s.queries + 1 }
    | some (.halt src) => { s with output := some (r src), work := s.work + 1 }

/-- The start state on the terminal set `T`. -/
noncomputable def initState {n : ℕ} (T : Finset (Fin n)) : State where
  cfg := ⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩
  imem := fun i =>
    if i = 0 then (n : ℤ)
    else if ∃ v : Fin n, i = 1 + (v : ℕ) ∧ v ∈ T then 1 else 0
  coins := 0
  work := 0
  queries := 0
  output := none

/-- A `B`-bit tape extended by `false`. -/
def extendTape {B : ℕ} (tape : Fin B → Bool) (i : ℕ) : Bool :=
  if h : i < B then tape ⟨i, h⟩ else false

/-- The state after `t` steps on the instance `(T, w)` and the tape. -/
noncomputable def run (P : Program) {n : ℕ} (T : Finset (Fin n)) (w : Fin n → Fin n → ℝ) {B : ℕ}
    (tape : Fin B → Bool) (t : ℕ) : State :=
  (step P w (extendTape tape))^[t] (initState T)

/-- `⌈C · n^{3/2} · log(n + 2)^K⌉`, the page's `Õ(n^{3/2})` with constants `C` and `K`. -/
noncomputable def budget (C K n : ℕ) : ℕ :=
  ⌈(C : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) * Real.log ((n : ℝ) + 2) ^ K⌉₊

end SublinearSteiner


