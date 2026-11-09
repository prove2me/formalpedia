-- Prove2me | Definitions.Def_MinSumFPT_Machine
-- name    : MinSumFPT_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:15:38.701631+00:00
-- url     : https://prove2.me/theorems/f5103270-8b7e-4863-8caf-1a35c9365bc4
-- title:
--   The randomized distance-oracle real RAM
-- statement:
--   The **randomized distance-oracle real RAM** is the machine model in which the running times of the mission are counted. The input is a finite set $A=\{0,\dots,n-1\}$ of points with a distance function $d$, and the algorithm may learn $d(x,y)$ for any two points at unit cost.
--
--   A machine state consists of finitely many real registers, integer pointer registers, a real memory and an integer memory, together with a step counter. The instructions are those of the published real RAM core (real constants, $+,-,\times,/$ on real registers, indirect loads and stores, pointer constants, increments, decrements and comparisons, conditional jumps), plus:
--
--   1. integer pointer addition and subtraction, and an integer memory;
--   2. the cast of a pointer value to a real (one way only: there is no floor and no real-to-integer cast);
--   3. `unif`: read the next real $\omega_j$ of a random tape $\omega\in\mathbb R^{\mathbb N}$;
--   4. `uniformIndex`: from the next tape real $u$ and a bound $m\ge1$, the index $\min(m,\max(1,\lceil mu\rceil))\in\{1,\dots,m\}$;
--   5. `dist`: the distance $d(x,y)$ of the two points named by two pointers, the only access to $d$;
--   6. `halt`: record a real output and stop.
--
--   Every executed instruction costs one unit of work. Under the tape law, the coordinates of $\omega$ are independent and uniform on $[0,1]$, so `uniformIndex` returns a uniform index. A program is a finite list of instructions; it is **admissible** if its real constants are rational.
--
--   The input is $n$ and $k$ in the integer memory at addresses $0,1$ and $\varepsilon,\delta$ in the real memory at addresses $0,1$. A program outputs a labelling of the points by writing the label of point $v$ at integer address $-1-v$, or a collection of point sets at the negative integer addresses, or a real number.
--
--   **Formalization Note** The paper counts "arithmetic operations, assuming that computing $d(x,y)$ is a single operation" and names no machine; this model fixes that count. It omits floor, logarithm, exponential, square root and pointer multiplication, so every running-time statement made with it is at least as strong as with a richer machine. A halted state does not change and costs nothing further; an invalid program counter is stuck and keeps costing.
-- source:
--   Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), Theorem 1, p.1 (cost model) and Theorems 5, 7, 8 (randomized algorithms), pp.9–11

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM

open scoped Classical

namespace MinSumFPT

/-!
# The randomized distance-oracle real RAM

Karthik C. S., Lee, Rabani, Schwiegelshohn, Zhou, *A Fixed Parameter Sublinear Time Approximation
Scheme for Metric Min-Sum Clustering*, arXiv:2610.15148 (held version of November 2, 2026, sha256
12e81235…), Theorem 1, p.1: "using n^{1+o(1)} ⋅ 2^{2^{O(k log(k/ε))}} arithmetic operations, assuming
that for any x, y ∈ A computing d(x, y) is a single operation"; the algorithms of Theorems 5, 7, 8
are randomized.

This module bundles the instruction set, the configurations, the step function, the input layout,
the output conventions and the law of the random tape of one machine model (a family of tightly
coupled definitions, kept in one module).

**Formalization Note.** The page names no machine. The model is a unit-cost real RAM built on the
published core `SmaleNinth.RAMInstr`, with
* integer pointer `+` and `−` and an integer memory `imem : ℤ → ℤ`;
* the pointer-to-real cast, one way only: there is no floor and no real-to-integer cast;
* `unif`, which reads the next real of the random tape `ω : ℕ → ℝ` (each coordinate uniform on
  `[0, 1]` under `tapeLaw`), and `uniformIndex`, which turns the next tape real into an index in
  `{1, …, p[a]}` (uniform under `tapeLaw`);
* the distance oracle `dist`, the only instruction that reads `d`, one unit of cost;
* `halt`, which records the real output `r[src]` and stops.
There is no pointer multiplication, exp, log or square root. `Admissible` restricts real literals to
rationals and excludes the core's `accept`/`reject`. Each omitted instruction makes the machine
weaker and the theorems stronger.

Every executed instruction costs one unit of `work`, including jumps, `unif`, `uniformIndex`, `dist`
and `halt`. An invalid program counter is stuck and charged; a halted state stutters at no cost.

**Input**: `imem 0 = n`, `imem 1 = k`, real memory `mem 0 = ε`, `mem 1 = δ`; everything else, and
all registers and pointers, `0`. The points are `Fin n`, addressed by the pointer values
`0, …, n − 1`.

**Outputs**: a labelling is read from the negative integer addresses, the label of point `v` being
`imem (−1 − v)`; a collection of point sets is read by `outputSets` (`imem (−1)` sets, then each set
as its length followed by its entries, at decreasing addresses); a real output is `output`. -/

/-- One instruction: a core real-RAM instruction or one of the additions of this module. -/
inductive Instr : Type
  /-- A core instruction of `SmaleNinth.RAMInstr`. -/
  | core (i : SmaleNinth.RAMInstr)
  /-- `p[d] := p[a] + p[b]`. -/
  | pointerAdd (d a b : ℕ)
  /-- `p[d] := p[a] − p[b]`. -/
  | pointerSub (d a b : ℕ)
  /-- `p[d] := imem[p[a]]`. -/
  | integerLoad (d a : ℕ)
  /-- `imem[p[a]] := p[b]`. -/
  | integerStore (a b : ℕ)
  /-- `r[d] := (p[a] : ℝ)`. -/
  | pointerReal (d a : ℕ)
  /-- `r[d] := ω j`, the next real of the tape. -/
  | unif (d : ℕ)
  /-- If `p[a] ≥ 1`: `p[d] := min p[a] (max 1 ⌈p[a] ⋅ ω j⌉)`, else `p[d] := 0`; reads one tape real. -/
  | uniformIndex (d a : ℕ)
  /-- `r[d] := d(p[a], p[b])` if both pointers are points of `Fin n`, else `0`; one query always. -/
  | dist (d a b : ℕ)
  /-- Output `r[src]` and stop. -/
  | halt (src : ℕ)

/-- A program: a finite list of instructions, executed from position `0`. -/
abbrev Program := List Instr

/-- Real literals are rational, and the core `accept`/`reject` do not occur. -/
def Admissible (P : Program) : Prop :=
  ∀ i ∈ P, (∀ d c, i = .core (.const d c) → ∃ q : ℚ, c = (q : ℝ)) ∧
    i ≠ .core .accept ∧ i ≠ .core .reject

/-- The core instruction at a program position (the additions are never passed to `RAMStep`). -/
def Instr.coreOf : Instr → SmaleNinth.RAMInstr
  | .core i => i
  | _ => .accept

/-- A configuration of the machine. -/
structure State where
  /-- Program counter, real registers, pointers, real memory. -/
  cfg : SmaleNinth.RAMConfig
  /-- The integer memory. -/
  imem : ℤ → ℤ
  /-- The number of tape reals read. -/
  tapePos : ℕ
  /-- The number of instructions executed. -/
  work : ℕ
  /-- The number of distance queries. -/
  queries : ℕ
  /-- Whether `halt` has been executed. -/
  halted : Bool
  /-- The real output (meaningful once halted). -/
  output : ℝ

/-- A pointer value as a point of `Fin n`. -/
def toPoint (n : ℕ) (x : ℤ) : Option (Fin n) :=
  if h : 0 ≤ x ∧ x.toNat < n then some ⟨x.toNat, h.2⟩ else none

/-- The distance oracle's answer on two pointer values. -/
noncomputable def oracleAnswer {n : ℕ} (d : Fin n → Fin n → ℝ) (x y : ℤ) : ℝ :=
  match toPoint n x, toPoint n y with
  | some u, some v => d u v
  | _, _ => 0

/-- The uniform index drawn from the tape real `u` for the bound `m`. -/
noncomputable def drawIndex (m : ℤ) (u : ℝ) : ℤ :=
  if 1 ≤ m then min m (max 1 ⌈(m : ℝ) * u⌉) else 0

/-- Advance by one instruction with new registers and pointers. -/
def State.next (s : State) (regs : ℕ → ℝ) (ptrs : ℕ → ℤ) : State :=
  { s with cfg := ⟨s.cfg.pc + 1, regs, ptrs, s.cfg.mem⟩, work := s.work + 1 }

/-- One step on the instance `d` and the tape `ω`. A halted state stutters at no cost; an invalid
program counter is stuck and charged. -/
noncomputable def step (P : Program) {n : ℕ} (d : Fin n → Fin n → ℝ) (ω : ℕ → ℝ) (s : State) :
    State :=
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
        { s.next r (Function.update p t (drawIndex (p a) (ω s.tapePos))) with
            tapePos := s.tapePos + 1 }
    | some (.dist t a b) =>
        { s.next (Function.update r t (oracleAnswer d (p a) (p b))) p with
            queries := s.queries + 1 }
    | some (.halt src) => { s with halted := true, output := r src, work := s.work + 1 }

/-- The start state on the inputs `n, k, ε, δ`. -/
noncomputable def initState (n k : ℕ) (ε δ : ℝ) : State where
  cfg := ⟨0, fun _ => 0, fun _ => 0, fun i => if i = 0 then ε else if i = 1 then δ else 0⟩
  imem := fun i => if i = 0 then (n : ℤ) else if i = 1 then (k : ℤ) else 0
  tapePos := 0
  work := 0
  queries := 0
  halted := false
  output := 0

/-- The state after `t` steps of `P` on the inputs `n, k, ε, δ`, the instance `d` and the tape `ω`. -/
noncomputable def run (P : Program) (n k : ℕ) (ε δ : ℝ) (d : Fin n → Fin n → ℝ) (ω : ℕ → ℝ)
    (t : ℕ) : State :=
  (step P d ω)^[t] (initState n k ε δ)

/-- The law of the random tape: independent coordinates, each uniform on `[0, 1]`. -/
noncomputable def tapeLaw : MeasureTheory.Measure (ℕ → ℝ) :=
  MeasureTheory.Measure.infinitePi
    (fun _ : ℕ => (MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Icc (0 : ℝ) 1))

/-- The state `s` has halted with the labelling `σ` written at the output addresses:
`imem (−1 − v) = σ v` for every point `v`. -/
def OutputsLabelling {n k : ℕ} (s : State) (σ : Fin n → Fin k) : Prop :=
  s.halted = true ∧ ∀ v : Fin n, s.imem (-1 - (v : ℤ)) = ((σ v : ℕ) : ℤ)

/-- The entries of the set stored at address `pos`: its length `imem pos`, then the entries at
`pos − 1, pos − 2, …`. -/
def readSet (imem : ℤ → ℤ) (pos : ℤ) : List ℤ :=
  (List.range (imem pos).toNat).map (fun t => imem (pos - 1 - (t : ℤ)))

/-- `N` consecutive sets starting at address `pos`. -/
def readSets (imem : ℤ → ℤ) : ℕ → ℤ → List (List ℤ)
  | 0, _ => []
  | N + 1, pos => readSet imem pos :: readSets imem N (pos - 1 - ((imem pos).toNat : ℤ))

/-- The collection of sets output by a halted state: `imem (−1)` sets, starting at address `−2`. -/
def outputSets (s : State) : List (List ℤ) :=
  readSets s.imem (s.imem (-1)).toNat (-2)

/-- The point set of an output entry list (every entry a point of `Fin n` under `ValidSets`). -/
def toPointSet (n : ℕ) (l : List ℤ) : Finset (Fin n) :=
  (l.filterMap (toPoint n)).toFinset

/-- The state has halted and every entry of every output set is a point of `Fin n`. -/
def ValidSets (n : ℕ) (s : State) : Prop :=
  s.halted = true ∧ 0 ≤ s.imem (-1) ∧ ∀ l ∈ outputSets s, ∀ e ∈ l, 0 ≤ e ∧ e < (n : ℤ)

end MinSumFPT


