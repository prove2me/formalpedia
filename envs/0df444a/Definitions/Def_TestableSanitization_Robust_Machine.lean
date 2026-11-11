-- Prove2me | Definitions.Def_TestableSanitization_Robust_Machine
-- name    : TestableSanitization_Robust_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:52:38.132761+00:00
-- url     : https://prove2.me/theorems/bf172b80-5797-40f2-9fae-456ee7c881b5
-- title:
--   The randomized oracle real RAM: rational literals, sqrt/exp/log, uniform and unit-ball draws, sample access to $D$, query access to $f$
-- statement:
--   The paper measures an algorithm by "its number of samples from $D$, oracle queries to $f$, and running time" (Definition 2) and names no machine; this definition fixes one. It is a unit-cost randomized real RAM built on the published core `SmaleNinth.RAMInstr` (exact $+,-,\times,\div$, comparison jumps, integer pointer registers, indirect access to a real memory indexed by $\mathbb Z$).
--
--   A **program** is a finite list of instructions: the core instructions (with **rational literals only**, and without the core's own accept/reject: `Admissible`), and
--   - `pointerReal` (cast a pointer to a real), `sqrt`, `exp`, `log`: one step each;
--   - `unif`: the next uniform $[0,1]$ real, one step;
--   - `ball`: writes the $d$ coordinates of the next draw from $U=U(B_1)$ to $d$ consecutive memory cells, **$d$ steps**;
--   - `sample`: writes the $d$ coordinates of the next draw from $D$, $d$ steps, **one sample**;
--   - `query`: reads $d$ consecutive cells as a point $x$ and writes $f(x)$ to a register, $d$ steps, **one query**;
--   - `accept`, `reject` (halt a construction program) and `ret` (halt an evaluation program with a register's value).
--
--   There is no floor and no real-to-integer conversion. A program is **deterministic** if it has no `unif`, `ball` or `sample` instruction. The random inputs are three independent streams — draws from $D$ (law $D^{\mathbb N}$), uniform reals (law $\mathrm{Unif}[0,1]^{\mathbb N}$) and draws from $U$ (law $U^{\mathbb N}$) — with joint law `streamLaw D`; the $i$-th instruction of a kind reads the $i$-th entry of its stream. A construction program starts with the input reals in cells $0,1,\dots$ and pointer $0$ holding $d$ (`initial`); `inputs d α η ζ μ r` is the input list $[d,\alpha,\eta,\zeta,\mu,r]$. `AcceptsWith P d f inp ω M`: the run accepts and its final memory is $M$. An evaluation program starts on a stored memory $M$ with the query point $y$ written to cells $-d,\dots,-1$ (`evalInit`); `EvalsTo E d f M y v`: it halts returning $v$; `EvalTotal`: it returns a value in $\{\pm1\}$ at every $y$; `outputFn E d f M` is the resulting function $y\mapsto g^f(y)$.
--
--   **Formalization Note.** A program counter outside the program is stuck: every further step is charged one step and the run never halts; halted states are left unchanged, so counters stop. Counters `samples`, `queries` and `work` (steps) are natural numbers. `log` is `Real.log` (so $\log 0=0$), division by $0$ gives $0$; programs must avoid both if they matter. `outputFn` is $0$ where the evaluation returns nothing, which soundness (Definition 2) counts as a failure.
-- source:
--   Cai, Mamali, Sotiraki, Yu, Zampetakis, Testable Sanitization via Boundary Geometry, STOC 2027 submission (manuscript sha256 bcf6434f…), p. 6 (PDF 8), §2 Notation (oracle access, g^f); p. 8 (PDF 10), Definition 2 (efficiency measures); p. 27 (PDF 29), proof of Theorem 1 (cost of generating perturbed points). The paper names no machine model.

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_TestableSanitization_Robust_Boundary

/-!
# The randomized oracle real RAM with sample access to `D` and query access to `f`

Cai, Mamali, Sotiraki, Yu, Zampetakis, *Testable Sanitization via Boundary Geometry*, STOC 2027
submission (manuscript sha256 bcf6434f…), §2 p. 6 ("We assume oracle access to an evaluator of
such functions. We write g^f for a function g: R^d → {±1} with oracle access to f."),
Definition 2 p. 8 ("The efficiency of algorithm A is measured by its number of samples from D,
oracle queries to f, and running time."), p. 27 ("Generating each perturbed point takes O(d)
time."). The paper names no machine; this file fixes one.

Encoding.
* The core is the published real RAM `SmaleNinth.RAMInstr` (exact `+ − × ÷`, real literals,
  pointer registers, indirect memory, comparison jumps). `Admissible` restricts its literals to
  rationals and forbids its own `accept`/`reject`.
* Added instructions, each costing one step unless stated: `pointerReal` (pointer to real cast),
  `sqrt`, `exp`, `log` (`Real.sqrt`, `Real.exp`, `Real.log`); `unif` (the next uniform `[0, 1]`
  real); `ball` (writes the `d` coordinates of the next draw from `U` at the address held in a
  pointer, cost `d`); `sample` (writes the `d` coordinates of the next draw from `D`, cost `d`,
  one sample); `query` (reads `d` coordinates from memory and writes `f` of that point to a
  register, cost `d`, one query); `accept`, `reject` (halt the construction program) and `ret`
  (halt an evaluation program with the value of a register). There is no floor and no
  real-to-integer conversion.
* The random inputs are three independent streams: draws from `D` (law `D^ℕ`), uniform reals
  (law `Unif[0,1]^ℕ`, as values in `unitInterval`) and draws from `U` (law `U^ℕ`); `streamLaw D`
  is their joint law. The `i`-th instruction of a kind reads the `i`-th entry of its stream.
* A program that runs off its end is stuck: every further step is charged and it never halts.
  A halted state is left unchanged.
* `initial d inp`: input reals `inp` in memory cells `0, 1, …`, pointer `0` holds `d`, all else
  `0`. `inputs d α η ζ μ r` is the list `[d, α, η, ζ, μ, r]`.
* `evalInit d M y`: an evaluation program starts on the stored memory `M`, with the point `y`
  written to cells `-d, …, -1`, pointer `0` holding `d` and pointer `1` holding `-d`.
-/

open MeasureTheory

namespace TestableSanitization.Robust

/-- An instruction of the randomized oracle real RAM. -/
inductive Instr where
  /-- An instruction of the published real-RAM core. -/
  | core (i : SmaleNinth.RAMInstr)
  /-- `r[dst] := (p[src] : ℝ)`. -/
  | pointerReal (dst src : ℕ)
  /-- `r[dst] := √(r[src])`. -/
  | sqrt (dst src : ℕ)
  /-- `r[dst] := exp(r[src])`. -/
  | exp (dst src : ℕ)
  /-- `r[dst] := log(r[src])`. -/
  | log (dst src : ℕ)
  /-- `r[dst] :=` the next uniform `[0, 1]` real. -/
  | unif (dst : ℕ)
  /-- `M[p[addr] + j] :=` coordinate `j` of the next draw from `U`, for `j < d` (cost `d`). -/
  | ball (addr : ℕ)
  /-- `M[p[addr] + j] :=` coordinate `j` of the next draw from `D`, for `j < d` (cost `d`). -/
  | sample (addr : ℕ)
  /-- `r[dst] := f(M[p[addr]], …, M[p[addr] + d − 1])` (cost `d`). -/
  | query (dst addr : ℕ)
  /-- Halt and accept. -/
  | accept
  /-- Halt and reject. -/
  | reject
  /-- Halt and return the value `r[src]`. -/
  | ret (src : ℕ)

/-- A program: a finite list of instructions, executed from position `0`. -/
abbrev Program := List Instr

/-- Rational literals only, and none of the core's own `accept`/`reject`. -/
def Admissible (P : Program) : Prop :=
  ∀ i ∈ P, (∀ dst c, i = .core (.const dst c) → ∃ q : ℚ, c = (q : ℝ)) ∧
    i ≠ .core .accept ∧ i ≠ .core .reject

/-- A deterministic program: no uniform draws, no ball draws, no samples from `D`. -/
def Deterministic (P : Program) : Prop :=
  ∀ i ∈ P, (∀ dst, i ≠ .unif dst) ∧ (∀ addr, i ≠ .ball addr) ∧ (∀ addr, i ≠ .sample addr)

/-- Whether the machine is running or how it halted. -/
inductive Status where
  | running
  | accepted
  | rejected
  | returned (v : ℝ)

/-- A machine state: the core configuration, the stream positions and the cost counters. -/
structure State where
  /-- Program counter, real registers, pointer registers and memory. -/
  cfg : SmaleNinth.RAMConfig
  /-- Number of samples drawn from `D`. -/
  samples : ℕ
  /-- Number of uniform reals drawn. -/
  unifs : ℕ
  /-- Number of draws from `U`. -/
  balls : ℕ
  /-- Number of oracle queries to `f`. -/
  queries : ℕ
  /-- Number of time steps. -/
  work : ℕ
  /-- Running or halted. -/
  status : Status

/-- The three random streams: draws from `D`, uniform reals, draws from `U`. -/
abbrev Streams (d : ℕ) := (ℕ → Pt d) × (ℕ → unitInterval) × (ℕ → Pt d)

/-- The joint law of the three independent streams. -/
noncomputable def streamLaw {d : ℕ} (D : Measure (Pt d)) [IsProbabilityMeasure D] :
    Measure (Streams d) :=
  (Measure.infinitePi fun _ : ℕ => D).prod
    ((Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval)).prod
      (Measure.infinitePi fun _ : ℕ => U d))

/-- The core instruction at a position (non-core positions are never passed to the core). -/
def Instr.coreOf : Instr → SmaleNinth.RAMInstr
  | .core i => i
  | _ => .accept

/-- The point of `ℝ^d` stored in cells `b, …, b + d − 1`. -/
noncomputable def readVec (d : ℕ) (mem : ℤ → ℝ) (b : ℤ) : Pt d :=
  WithLp.toLp 2 (fun j : Fin d => mem (b + (j : ℤ)))

/-- Memory with the coordinates of `v` written to cells `b, …, b + d − 1`. -/
noncomputable def writeVec {d : ℕ} (mem : ℤ → ℝ) (b : ℤ) (v : Pt d) : ℤ → ℝ :=
  fun j => if h : b ≤ j ∧ j < b + (d : ℤ) then v ⟨(j - b).toNat, by omega⟩ else mem j

/-- Advance the program counter, replace the registers, charge `c` steps. -/
def State.next (S : State) (regs : ℕ → ℝ) (c : ℕ) : State :=
  { S with cfg := { S.cfg with pc := S.cfg.pc + 1, regs := regs }, work := S.work + c }

/-- One step of program `P` in dimension `d` with oracle `f` on streams `ω`. -/
noncomputable def step (P : Program) (d : ℕ) (f : Pt d → ℝ) (ω : Streams d) (S : State) :
    State :=
  match S.status with
  | .accepted => S
  | .rejected => S
  | .returned _ => S
  | .running =>
    let r := S.cfg.regs
    match P[S.cfg.pc]? with
    | none => { S with work := S.work + 1 }
    | some (.core _) =>
        { S with cfg := SmaleNinth.RAMStep (P.map Instr.coreOf) S.cfg, work := S.work + 1 }
    | some (.pointerReal dst src) => S.next (Function.update r dst (S.cfg.ptrs src : ℝ)) 1
    | some (.sqrt dst src) => S.next (Function.update r dst (Real.sqrt (r src))) 1
    | some (.exp dst src) => S.next (Function.update r dst (Real.exp (r src))) 1
    | some (.log dst src) => S.next (Function.update r dst (Real.log (r src))) 1
    | some (.unif dst) =>
        { S.next (Function.update r dst (ω.2.1 S.unifs : ℝ)) 1 with unifs := S.unifs + 1 }
    | some (.ball addr) =>
        { S with
          cfg := { S.cfg with pc := S.cfg.pc + 1,
                              mem := writeVec S.cfg.mem (S.cfg.ptrs addr) (ω.2.2 S.balls) }
          balls := S.balls + 1
          work := S.work + d }
    | some (.sample addr) =>
        { S with
          cfg := { S.cfg with pc := S.cfg.pc + 1,
                              mem := writeVec S.cfg.mem (S.cfg.ptrs addr) (ω.1 S.samples) }
          samples := S.samples + 1
          work := S.work + d }
    | some (.query dst addr) =>
        { S.next (Function.update r dst (f (readVec d S.cfg.mem (S.cfg.ptrs addr)))) d with
          queries := S.queries + 1 }
    | some .accept => { S with status := .accepted, work := S.work + 1 }
    | some .reject => { S with status := .rejected, work := S.work + 1 }
    | some (.ret src) => { S with status := .returned (r src), work := S.work + 1 }

/-- The state after `t` steps. -/
noncomputable def run (P : Program) (d : ℕ) (f : Pt d → ℝ) (ω : Streams d) (S : State) (t : ℕ) :
    State :=
  (step P d f ω)^[t] S

/-- The start state of a construction program: input reals in cells `0, 1, …`, pointer `0`
holding `d`, everything else `0`. -/
noncomputable def initial (d : ℕ) (inp : List ℝ) : State :=
  ⟨⟨0, fun _ => 0, fun j => if j = 0 then (d : ℤ) else 0,
    fun j => if 0 ≤ j then inp.getD j.toNat 0 else 0⟩, 0, 0, 0, 0, 0, .running⟩

/-- The input list `[d, α, η, ζ, μ, r]` of Theorem 1's algorithm. -/
def inputs (d : ℕ) (α η ζ μ r : ℝ) : List ℝ :=
  [(d : ℝ), α, η, ζ, μ, r]

/-- `P` run on `inp` with oracle `f` and streams `ω` halts with `accept` and final memory `M`. -/
def AcceptsWith (P : Program) (d : ℕ) (f : Pt d → ℝ) (inp : List ℝ) (ω : Streams d)
    (M : ℤ → ℝ) : Prop :=
  ∃ t, (run P d f ω (initial d inp) t).status = .accepted ∧
    (run P d f ω (initial d inp) t).cfg.mem = M

/-- `P` run on `inp` with oracle `f` and streams `ω` halts with `accept`. -/
def Accepts (P : Program) (d : ℕ) (f : Pt d → ℝ) (inp : List ℝ) (ω : Streams d) : Prop :=
  ∃ M, AcceptsWith P d f inp ω M

/-- The start state of an evaluation program on stored memory `M` at the point `y`. -/
noncomputable def evalInit (d : ℕ) (M : ℤ → ℝ) (y : Pt d) : State :=
  ⟨⟨0, fun _ => 0, fun j => if j = 0 then (d : ℤ) else if j = 1 then -(d : ℤ) else 0,
    writeVec M (-(d : ℤ)) y⟩, 0, 0, 0, 0, 0, .running⟩

/-- Fixed streams for a deterministic evaluation program (it never reads them). -/
def noStreams (d : ℕ) : Streams d :=
  (fun _ => 0, fun _ => 0, fun _ => 0)

/-- The evaluation program `E` on stored memory `M`, with oracle `f`, halts at `y` returning `v`. -/
def EvalsTo (E : Program) (d : ℕ) (f : Pt d → ℝ) (M : ℤ → ℝ) (y : Pt d) (v : ℝ) : Prop :=
  ∃ t, (run E d f (noStreams d) (evalInit d M y) t).status = .returned v

/-- `E` on `M` with oracle `f` defines a `±1` value at every point. -/
def EvalTotal (E : Program) (d : ℕ) (f : Pt d → ℝ) (M : ℤ → ℝ) : Prop :=
  ∀ y, ∃ v, (v = 1 ∨ v = -1) ∧ EvalsTo E d f M y v

open Classical in
/-- The output classifier `g^f`: the value returned by `E` on `M` at `y` (`0` where `E` returns
nothing; this branch is only reached when `EvalTotal` fails, which soundness counts as failure). -/
noncomputable def outputFn (E : Program) (d : ℕ) (f : Pt d → ℝ) (M : ℤ → ℝ) : Pt d → ℝ :=
  fun y => if h : ∃ v, EvalsTo E d f M y v then Classical.choose h else 0

end TestableSanitization.Robust


