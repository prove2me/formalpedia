-- Prove2me | Definitions.Def_WalkTreeCluster_Machine
-- name    : WalkTreeCluster_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:41:13.965177+00:00
-- url     : https://prove2.me/theorems/c8ec7802-977f-45de-b723-825139eb597a
-- title:
--   The randomized neighbor-query real RAM (the cost model of Section 10.1)
-- statement:
--   The algorithm of Theorem 1.3 is a program of a unit-cost real RAM. Its core is the published real pointer machine `SmaleNinth.RAMInstr` (real registers, integer pointers, real memory, $+,-,\times,\div$, rational literals, indirect load/store, pointer set/copy/increment/decrement, comparison jumps, accept, reject). It adds: integer pointer addition and subtraction; an integer memory; the cast of a pointer to a real; the scalar evaluation $r\mapsto|r|^{s}$; a fair coin; a uniform choice of an index in $\{1,\dots,m\}$; and the neighbor query, which returns the $r$-th neighbor of a vertex and is the only access to the graph.
--
--   Every executed instruction costs one unit of work and each neighbor query is counted ("Arithmetic operations, scalar evaluations, random choices, and operations on vertex identifiers and neighbor indices each count as one unit of work", Section 10.1). A run halts at accept (answer *same*) or reject (answer *different*). The input is $n,d,u,v$ in integer memory and $\epsilon,\phi$ in real memory; the randomness is a sequence of independent uniform $[0,1]$ values, of which the coin and the index choice read one each. Total work and total queries are the suprema over time of the counters, infinite for a run that never stops.
--
--   **Formalization Note.** There is no floor, real-to-integer cast, logarithm, exponential, square root, pointer multiplication or biased coin, and a tape value never enters a register; each omission makes the machine weaker and Theorem 1.3 stronger. An invalid program counter is charged and does not halt. The page names no machine; this module is the mission's reading of its cost model.
-- source:
--   Kapralov–Kochetkova, Sublinear Time Clustering: Taming Random Walks in Arbitrary Noise, STOC 2027 submission (manuscript sha256 638eeef1…), Theorem 1.3, p.2; Section 4 (graph access model), p.16; Section 10.1, p.69

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM

open MeasureTheory

namespace WalkTreeCluster

/-!
# The randomized neighbor-query real RAM

Kapralov–Kochetkova, *Sublinear Time Clustering: Taming Random Walks in Arbitrary Noise*, STOC 2027
submission (manuscript sha256 638eeef1…), Theorem 1.3, p.2; graph access model, Section 4, p.16;
cost model, Section 10.1, p.69: "a query (u, r) returns the r-th neighbor of u in O(1) time. A lazy
random-walk step uses at most one query and O(1) work. Arithmetic operations, scalar evaluations,
random choices, and operations on vertex identifiers and neighbor indices each count as one unit of
work."

**Formalization Note.** The page names no machine; this module is the mission's reading of it.
* The scalar core is the published `SmaleNinth.RAMInstr` pointer machine over `ℝ` (real registers,
  integer pointers, real memory `ℤ → ℝ`, `+ − × ÷` with `x / 0 = 0`, literals, indirect load and
  store, pointer set/copy/increment/decrement, two comparison jumps, `accept`, `reject`).
* Additions: integer pointer `+` and `−`; an integer memory `ℤ → ℤ`; the pointer-to-real cast (one
  way only); `rpow` (`r[d] := |r[a]| ^ r[b]`, `Real.rpow`: the page's unit-cost "scalar
  evaluations"); a fair `coin`; `uniformIndex` (`p[d] :=` a uniform element of `{1, …, p[a]}`: the
  page's unit-cost "random choice" of a neighbor index); and the neighbor query `nbr`, the only
  instruction that reads the graph, charged one query in every case.
* There is no floor, no real-to-integer cast, no log, exp or square root, no pointer multiplication,
  no biased coin, and the tape value never enters a register. Each omission makes the machine weaker
  and the theorem stronger. `Admissible` restricts real literals to rationals.
* Every executed instruction costs one unit of `work` (including jumps, coins, `uniformIndex` and
  queries). A state whose program counter holds the core `accept`/`reject` is halted, with output
  `true` ("same") or `false` ("different"); it stutters at no cost. An invalid program counter is
  stuck and charged, so a program cannot halt by running off its end.
* Randomness is one tape `ω : ℕ → ℝ` of independent uniform `[0, 1]` values; `coin` and
  `uniformIndex` each read the next cell. `coin` writes `1` iff `ω k < 1/2`; `uniformIndex` with
  `m = p[a] ≥ 1` writes `min m (max 1 ⌈m · ω k⌉)` (uniform on `{1, …, m}`), and `0` if `m < 1`.
* Input: integer memory `I 0 = n`, `I 1 = d`, `I 2 = u`, `I 3 = v` (vertices as integers in
  `[0, n)`), real memory `mem 0 = ϵ`, `mem 1 = ϕ`, all else `0`.
* `totalWork` and `totalQueries` are the suprema over time of the counters, in `ℕ∞` (`⊤` for a run
  that never halts with unbounded work).
-/

/-- One instruction of the machine. -/
inductive Instr : Type
  /-- A core instruction of `SmaleNinth.RAMInstr`. -/
  | core (i : SmaleNinth.RAMInstr)
  /-- `p[d] := p[a] + p[b]`. -/
  | pointerAdd (d a b : ℕ)
  /-- `p[d] := p[a] − p[b]`. -/
  | pointerSub (d a b : ℕ)
  /-- `p[d] := I[p[a]]` (integer memory). -/
  | integerLoad (d a : ℕ)
  /-- `I[p[a]] := p[b]` (integer memory). -/
  | integerStore (a b : ℕ)
  /-- `r[d] := (p[a] : ℝ)`. -/
  | pointerReal (d a : ℕ)
  /-- `r[d] := |r[a]| ^ r[b]` (`Real.rpow`). -/
  | rpow (d a b : ℕ)
  /-- `r[d] := 1` if the next tape value is `< 1/2`, else `0`. -/
  | coin (d : ℕ)
  /-- `p[d] :=` a uniform element of `{1, …, p[a]}` (from the next tape value), or `0` if `p[a] < 1`. -/
  | uniformIndex (d a : ℕ)
  /-- `p[d] :=` the `p[b]`-th neighbor of vertex `p[a]` if `0 ≤ p[a] < n` and `1 ≤ p[b] ≤ d`, else
  `−1`; one graph query in every case. -/
  | nbr (d a b : ℕ)

/-- A program: a finite list of instructions, executed from position `0`. -/
abbrev Program := List Instr

/-- Every real literal of the program is rational. -/
def Admissible (P : Program) : Prop :=
  ∀ i ∈ P, ∀ (dst : ℕ) (c : ℝ), i = .core (.const dst c) → ∃ q : ℚ, c = (q : ℝ)

/-- The core table of `P`; positions holding an addition of this module carry a placeholder that
`step` never executes. -/
def coreProgram (P : Program) : SmaleNinth.RAMProgram :=
  P.map fun i => match i with
    | .core c => c
    | _ => .const 0 0

/-- A machine state. -/
structure State where
  /-- Program counter, real registers, pointer registers and real memory. -/
  cfg : SmaleNinth.RAMConfig
  /-- The integer memory. -/
  imem : ℤ → ℤ
  /-- The tape cursor: the number of tape cells read. -/
  cursor : ℕ
  /-- The number of instructions executed. -/
  work : ℕ
  /-- The number of neighbor queries. -/
  queries : ℕ

/-- The output of a halted state: `some true` at a core `accept`, `some false` at a core `reject`,
`none` otherwise. -/
def outputOf (P : Program) (s : State) : Option Bool :=
  match P[s.cfg.pc]? with
  | some (.core .accept) => some true
  | some (.core .reject) => some false
  | _ => none

/-- The answer to the neighbor query `(x, r)`: the `r`-th neighbor of `x`, or `−1` when `x` is not a
vertex or `r ∉ {1, …, d}`. -/
def nbrAnswer {n d : ℕ} (nbr : Fin n → Fin d → Fin n) (x r : ℤ) : ℤ :=
  if h : 0 ≤ x ∧ x < n ∧ 1 ≤ r ∧ r ≤ d then
    ((nbr ⟨x.toNat, by omega⟩ ⟨(r - 1).toNat, by omega⟩ : ℕ) : ℤ)
  else -1

/-- The uniform index read from tape value `w`: `min m (max 1 ⌈m w⌉)` if `m ≥ 1`, else `0`. -/
noncomputable def uniformOf (m : ℤ) (w : ℝ) : ℤ :=
  if 1 ≤ m then min m (max 1 ⌈(m : ℝ) * w⌉) else 0

/-- Advance the program counter with new registers and pointers, charging one unit of work. -/
def State.next (s : State) (regs : ℕ → ℝ) (ptrs : ℕ → ℤ) : State :=
  { s with cfg := ⟨s.cfg.pc + 1, regs, ptrs, s.cfg.mem⟩, work := s.work + 1 }

/-- One step of `P` on the graph `nbr` and the tape `ω`. A halted state stutters at no cost; an
invalid program counter is stuck and charged. The graph occurs only in the `nbr` branch and the tape
only in `coin` and `uniformIndex`. -/
noncomputable def step (P : Program) {n d : ℕ} (nbr : Fin n → Fin d → Fin n) (ω : ℕ → ℝ)
    (s : State) : State :=
  match outputOf P s with
  | some _ => s
  | none =>
    let r := s.cfg.regs
    let p := s.cfg.ptrs
    match P[s.cfg.pc]? with
    | none => { s with work := s.work + 1 }
    | some (.core _) =>
        { s with cfg := SmaleNinth.RAMStep (coreProgram P) s.cfg, work := s.work + 1 }
    | some (.pointerAdd d a b) => s.next r (Function.update p d (p a + p b))
    | some (.pointerSub d a b) => s.next r (Function.update p d (p a - p b))
    | some (.integerLoad d a) => s.next r (Function.update p d (s.imem (p a)))
    | some (.integerStore a b) => { s.next r p with imem := Function.update s.imem (p a) (p b) }
    | some (.pointerReal d a) => s.next (Function.update r d (p a : ℝ)) p
    | some (.rpow d a b) => s.next (Function.update r d (|r a| ^ r b)) p
    | some (.coin d) =>
        { s.next (Function.update r d (if ω s.cursor < 1 / 2 then 1 else 0)) p with
          cursor := s.cursor + 1 }
    | some (.uniformIndex d a) =>
        { s.next r (Function.update p d (uniformOf (p a) (ω s.cursor))) with
          cursor := s.cursor + 1 }
    | some (.nbr d a b) =>
        { s.next r (Function.update p d (nbrAnswer nbr (p a) (p b))) with
          queries := s.queries + 1 }

/-- The state after `t` steps from `s`. -/
noncomputable def run (P : Program) {n d : ℕ} (nbr : Fin n → Fin d → Fin n) (ω : ℕ → ℝ)
    (s : State) (t : ℕ) : State :=
  (step P nbr ω)^[t] s

/-- The start state on input `(n, d, u, v, ϵ, ϕ)`: `I 0 = n`, `I 1 = d`, `I 2 = u`, `I 3 = v`,
`mem 0 = ϵ`, `mem 1 = ϕ`; everything else `0`. -/
noncomputable def input (n d : ℕ) (u v : Fin n) (ϵ ϕ : ℝ) : State where
  cfg := ⟨0, fun _ => 0, fun _ => 0, fun z => if z = 0 then ϵ else if z = 1 then ϕ else 0⟩
  imem := fun z =>
    if z = 0 then (n : ℤ) else if z = 1 then (d : ℤ) else if z = 2 then ((u : ℕ) : ℤ)
    else if z = 3 then ((v : ℕ) : ℤ) else 0
  cursor := 0
  work := 0
  queries := 0

/-- The run halts with output `b`. -/
def HaltsWith (P : Program) {n d : ℕ} (nbr : Fin n → Fin d → Fin n) (ω : ℕ → ℝ) (s : State)
    (b : Bool) : Prop :=
  ∃ t, outputOf P (run P nbr ω s t) = some b

/-- Total work of the run (`⊤` if unbounded). -/
noncomputable def totalWork (P : Program) {n d : ℕ} (nbr : Fin n → Fin d → Fin n) (ω : ℕ → ℝ)
    (s : State) : ℕ∞ :=
  ⨆ t, ((run P nbr ω s t).work : ℕ∞)

/-- Total number of neighbor queries of the run (`⊤` if unbounded). -/
noncomputable def totalQueries (P : Program) {n d : ℕ} (nbr : Fin n → Fin d → Fin n)
    (ω : ℕ → ℝ) (s : State) : ℕ∞ :=
  ⨆ t, ((run P nbr ω s t).queries : ℕ∞)

/-- The tape: independent uniform `[0, 1]` values. -/
noncomputable def tape : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1))

end WalkTreeCluster


