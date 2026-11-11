-- Prove2me | Definitions.Def_WeakStrongMSR_Machine
-- name    : WeakStrongMSR_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T08:26:53.712599+00:00
-- url     : https://prove2.me/theorems/1aa3bd8a-3991-4f9f-9fe8-ecd4b8c5d9c2
-- title:
--   The weak–strong randomized real RAM: free weak reads, counted strong queries
-- statement:
--   The machine for "polynomial time" is a unit-cost randomized real RAM: the real pointer machine `SmaleNinth.RAMInstr` together with integer pointer arithmetic, an integer memory, a one-way pointer-to-real cast, and the random-tape instructions of the published `MinSumFPT.Machine` (the tape is a sequence of independent uniform $[0,1]$ reals with law `MinSumFPT.tapeLaw`). It accesses the instance only through three oracle instructions.
--
--   1. `weak t a b` writes $\tilde d(p_a,p_b)$ into a real register. It costs one step and no strong query, since weak answers are free.
--   2. `strong a` strongly queries the point $p_a$: the point enters the strong set, and **every execution** counts one strong query.
--   3. `sdist t a b` writes $d(p_a,p_b)$ if both points are in the strong set and $0$ otherwise. Given $SO(x)$ and $SO(y)$ the algorithm can compute $d(x,y)$. This is the only instruction that reads $d$.
--
--   The input is $n,k$ in integer memory and $\delta,\Delta$ in real memory. The metric is never part of the input. The output is written at fixed addresses: the slot label of point $v$, the centre of slot $j$ and the radius of slot $j$. Every instruction costs one step.
--
--   **Formalization Note** The machine has no floor, logarithm, exponential or square root, and its real literals are rational (`Admissible`). Each missing primitive makes the existence claim of Theorem 1.2 stronger.
-- source:
--   Friggstad–Jamshidian–Vakilian, Minimum Sum-of-Radii Clustering with Strong and Weak Oracles (manuscript, STOC 2027 submission, sha256 5f8fbaf3…67e8f92a0), Definition 1.1, p.1 (PDF 2); abstract (PDF 1); Theorem 1.2, p.2 (PDF 3); §2.3, p.5 (PDF 6)

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_MinSumFPT_Machine
import Definitions.Def_WeakStrongMSR_Model

open scoped Classical

set_option autoImplicit false

namespace WeakStrongMSR

/-!
# The weak–strong randomized real RAM

Friggstad–Jamshidian–Vakilian, *Minimum Sum-of-Radii Clustering with Strong and Weak Oracles*
(manuscript, sha256 5f8fbaf3…67e8f92a0), Definition 1.1, p.1 (the two oracles; "The cost of an
algorithm is the number of strong queries"); abstract ("the answers of the weak oracle are given to
us for free"); Theorem 1.2, p.2 ("polynomial-time algorithm"); §2.3, p.5 (the known bound `Δ` on
the aspect ratio).

This module bundles the instruction set, configurations, step function, input layout and output
layout of one machine model (a family of tightly coupled definitions, kept in one module).

**Formalization Note.** The page names no machine for "polynomial time". The model is the unit-cost
randomized real RAM of the published `MinSumFPT.Machine` (the core `SmaleNinth.RAMInstr`, integer
pointer `+`/`−`, an integer memory, the one-way pointer-to-real cast, `unif` and `uniformIndex` on a
tape of independent uniform `[0, 1]` reals, whose law is the published `MinSumFPT.tapeLaw`), with
its distance oracle replaced by the two oracles of Definition 1.1:
* `weak t a b` reads the weak distance `d̃(p[a], p[b])`: one step and **no** strong query (weak
  answers are free);
* `strong a` strongly queries the point `p[a]`: it enters the strong set, and **every execution**
  counts one strong query (so a bound on executions bounds the number of queried points);
* `sdist t a b` returns the exact distance `d(p[a], p[b])` when both points have been strongly
  queried, and `0` otherwise ("Given SO(x) and SO(y), the algorithm can compute d(x, y)"). This is
  the only instruction that reads `d`.
The program never receives `d` as input. There is no floor, log, exp or square root, and real
literals are rational (`Admissible`); every omitted primitive makes the machine weaker and the goal
stronger. Every executed instruction costs one step; a halted state stutters at no cost; an invalid
program counter is stuck and charged.

**Input**: `imem 0 = n`, `imem 1 = k`, real memory `mem 0 = δ`, `mem 1 = Δ`; everything else `0`;
the strong set is empty. Points are the pointer values `0, …, n − 1`.

**Output** (R6): the slot label of point `v` at `imem (−1 − v)`, the centre of slot `j` at
`imem (−1 − n − j)`, the radius of slot `j` at the real memory cell `mem (−1 − j)`. -/

/-- One instruction: a core real-RAM instruction or one of the additions of this module. -/
inductive Instr : Type
  /-- A core instruction of `SmaleNinth.RAMInstr`. -/
  | core (i : SmaleNinth.RAMInstr)
  /-- `p[t] := p[a] + p[b]`. -/
  | pointerAdd (t a b : ℕ)
  /-- `p[t] := p[a] − p[b]`. -/
  | pointerSub (t a b : ℕ)
  /-- `p[t] := imem[p[a]]`. -/
  | integerLoad (t a : ℕ)
  /-- `imem[p[a]] := p[b]`. -/
  | integerStore (a b : ℕ)
  /-- `r[t] := (p[a] : ℝ)`. -/
  | pointerReal (t a : ℕ)
  /-- `r[t] := ω j`, the next real of the tape. -/
  | unif (t : ℕ)
  /-- `p[t] := MinSumFPT.drawIndex p[a] (ω j)`, a uniform index in `{1, …, p[a]}`; reads one tape
  real. -/
  | uniformIndex (t a : ℕ)
  /-- `r[t] := d̃(p[a], p[b])` if both pointers are points, else `0`; free (no strong query). -/
  | weak (t a b : ℕ)
  /-- Strongly query the point `p[a]` (if it is a point); one strong query in every case. -/
  | strong (a : ℕ)
  /-- `r[t] := d(p[a], p[b])` if both pointers are strongly queried points, else `0`. -/
  | sdist (t a b : ℕ)
  /-- Stop. -/
  | halt

/-- A program: a finite list of instructions, executed from position `0`. -/
abbrev Program := List Instr

/-- Real literals are rational, and the core `accept`/`reject` do not occur. -/
def Admissible (P : Program) : Prop :=
  ∀ i ∈ P, (∀ t c, i = .core (.const t c) → ∃ q : ℚ, c = (q : ℝ)) ∧
    i ≠ .core .accept ∧ i ≠ .core .reject

/-- The core instruction at a program position (the additions are never passed to `RAMStep`). -/
def Instr.coreOf : Instr → SmaleNinth.RAMInstr
  | .core i => i
  | _ => .accept

/-- A configuration of the machine. -/
structure State (n : ℕ) where
  /-- Program counter, real registers, pointers, real memory. -/
  cfg : SmaleNinth.RAMConfig
  /-- The integer memory. -/
  imem : ℤ → ℤ
  /-- The number of tape reals read. -/
  tapePos : ℕ
  /-- The number of instructions executed. -/
  work : ℕ
  /-- The number of executed `strong` instructions (strong queries). -/
  queries : ℕ
  /-- The strongly queried points. -/
  strongSet : Finset (Fin n)
  /-- Whether `halt` has been executed. -/
  halted : Bool

/-- Advance by one instruction with new registers and pointers. -/
def State.next {n : ℕ} (s : State n) (regs : ℕ → ℝ) (ptrs : ℕ → ℤ) : State n :=
  { s with cfg := ⟨s.cfg.pc + 1, regs, ptrs, s.cfg.mem⟩, work := s.work + 1 }

/-- The weak oracle's answer on two pointer values (`0` unless both are points). -/
noncomputable def weakAnswer {n : ℕ} (w : Fin n → Fin n → ℝ) (x y : ℤ) : ℝ :=
  match MinSumFPT.toPoint n x, MinSumFPT.toPoint n y with
  | some u, some v => w u v
  | _, _ => 0

/-- The exact distance of two pointer values, available only when both are strongly queried
points (`0` otherwise). -/
noncomputable def strongAnswer {n : ℕ} (d : Fin n → Fin n → ℝ) (Q : Finset (Fin n)) (x y : ℤ) :
    ℝ :=
  match MinSumFPT.toPoint n x, MinSumFPT.toPoint n y with
  | some u, some v => if u ∈ Q ∧ v ∈ Q then d u v else 0
  | _, _ => 0

/-- One step with the weak table `w`, the metric `d` (read only by `sdist`, on strongly queried
points) and the tape `ω`. -/
noncomputable def step (P : Program) {n : ℕ} (w d : Fin n → Fin n → ℝ) (ω : ℕ → ℝ)
    (s : State n) : State n :=
  if s.halted then s else
    let r := s.cfg.regs
    let p := s.cfg.ptrs
    match P[s.cfg.pc]? with
    | none => { s with work := s.work + 1 }
    | some (.core _) =>
        { s with cfg := SmaleNinth.RAMStep (P.map Instr.coreOf) s.cfg, work := s.work + 1 }
    | some (.pointerAdd t a b) => s.next r (Function.update p t (p a + p b))
    | some (.pointerSub t a b) => s.next r (Function.update p t (p a - p b))
    | some (.integerLoad t a) => s.next r (Function.update p t (s.imem (p a)))
    | some (.integerStore a b) => { s.next r p with imem := Function.update s.imem (p a) (p b) }
    | some (.pointerReal t a) => s.next (Function.update r t (p a : ℝ)) p
    | some (.unif t) =>
        { s.next (Function.update r t (ω s.tapePos)) p with tapePos := s.tapePos + 1 }
    | some (.uniformIndex t a) =>
        { s.next r (Function.update p t (MinSumFPT.drawIndex (p a) (ω s.tapePos))) with
            tapePos := s.tapePos + 1 }
    | some (.weak t a b) => s.next (Function.update r t (weakAnswer w (p a) (p b))) p
    | some (.strong a) =>
        { s.next r p with
            queries := s.queries + 1
            strongSet :=
              match MinSumFPT.toPoint n (p a) with
              | some u => insert u s.strongSet
              | none => s.strongSet }
    | some (.sdist t a b) =>
        s.next (Function.update r t (strongAnswer d s.strongSet (p a) (p b))) p
    | some .halt => { s with halted := true, work := s.work + 1 }

/-- The start state on the inputs `n, k, δ, Δ`. -/
noncomputable def initState (n k : ℕ) (δ Δ : ℝ) : State n where
  cfg := ⟨0, fun _ => 0, fun _ => 0, fun i => if i = 0 then δ else if i = 1 then Δ else 0⟩
  imem := fun i => if i = 0 then (n : ℤ) else if i = 1 then (k : ℤ) else 0
  tapePos := 0
  work := 0
  queries := 0
  strongSet := ∅
  halted := false

/-- The state after `t` steps of `P` on the inputs `n, k, δ, Δ`, the weak table `w`, the metric `d`
and the tape `ω`. -/
noncomputable def run (P : Program) (n k : ℕ) (δ Δ : ℝ) (w d : Fin n → Fin n → ℝ) (ω : ℕ → ℝ)
    (t : ℕ) : State n :=
  (step P w d ω)^[t] (initState n k δ Δ)

/-- The state has halted with the solution `(σ, ctr, rad)` at the output addresses:
`imem (−1 − v) = σ v`, `imem (−1 − n − j) = ctr j`, `mem (−1 − j) = rad j`. -/
def OutputsSolution {n k : ℕ} (s : State n) (σ : Fin n → Fin k) (ctr : Fin k → Fin n)
    (rad : Fin k → ℝ) : Prop :=
  s.halted = true ∧ (∀ v : Fin n, s.imem (-1 - (v : ℤ)) = ((σ v : ℕ) : ℤ)) ∧
    (∀ j : Fin k, s.imem (-1 - (n : ℤ) - (j : ℤ)) = ((ctr j : ℕ) : ℤ)) ∧
    (∀ j : Fin k, s.cfg.mem (-1 - (j : ℤ)) = rad j)

end WeakStrongMSR


