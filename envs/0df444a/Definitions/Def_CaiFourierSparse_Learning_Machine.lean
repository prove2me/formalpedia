-- Prove2me | Definitions.Def_CaiFourierSparse_Learning_Machine
-- name    : CaiFourierSparse_Learning_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T15:11:22.10664+00:00
-- url     : https://prove2.me/theorems/82809053-5990-450e-8a7a-82269ba5fcae
-- title:
--   The randomized, costed point-query machine: programs, runs, step and query counts, and the random tape
-- statement:
--   An algorithm is a finite **program** (`Program`, a list of `Instr`) for a unit-cost random-access machine whose registers $r[0],r[1],\dots$ hold complex numbers. Instructions: rational constants, $\pi$ and $i$; $+,-,\times,\div$ (division by $0$ gives $0$); conjugation, real part, complex $\exp$, $\sqrt{\cdot}$ and $\ln$ of a real part, floor; indirect load and store at address $\lfloor\operatorname{Re} r[a]\rfloor$; conditional jump on $\operatorname{Re} r[a]<\operatorname{Re} r[b]$ and unconditional jump; `rand`, which writes the next entry of the random tape; `query`, which writes $y(\operatorname{Re} r[a])$ and **fails** the run if $\operatorname{Re} r[a]$ is outside the query domain $D$; `out`, which appends a register to the output list; and `halt`.
--
--   The run on inputs $(v_0,v_1,\dots)$ starts with these values in registers $0,1,\dots$ and all other registers $0$ (`initConfig`); `step` executes one instruction and leaves a halted or failed configuration unchanged; `run` iterates it. **Running time** is the number of executed steps and the **sample count** is the number of executed queries. `HaltsWith P D y ω input T Q Good` says that on tape $\omega$ the run halts within $T$ steps after at most $Q$ queries with an output satisfying `Good`; `OutputSatisfies` drops the bounds. The **random tape** $\omega$ is an i.i.d. sequence of uniform $[0,1]$ draws with law `tapeLaw` (infinite product). For vectors $v\in\mathbb C^m$ the query domain is $\{0,\dots,m-1\}$ and the oracle returns $v[a]$ (`vecDomain`, `vecOracle`); for signals the domain is the window $[-1,1]$.
--
--   The program is a fixed finite object: it receives only its numerical inputs and oracle answers, never the hidden amplitudes, frequencies, clusters or noise, and every operation it performs is counted.
--
--   **Formalization Note.** Unit-cost exact arithmetic over $\mathbb C$ (with $\exp$, $\sqrt{\cdot}$, $\ln$, floor) is the reading of the paper's operation counts; it is not a bit-complexity model.
-- source:
--   Cai, Chen, Shao, Wang (2026), Learning Fourier-Sparse Signals and Multiband Signals, arXiv:2609.02977 (supplied manuscript, SHA-256 0ce139ab…), §2 and §5 (cost model of Theorems 1.3, 5.1, 8.1 and Lemma 5.5), printed pp. 6, 24–30 (PDF pp. 8, 26–32)

import Mathlib

namespace CaiFourierSparse.Learning

open MeasureTheory
open scoped ENNReal

/-! # The randomized, costed point-query machine (Cai–Chen–Shao–Wang, §§2, 5, 8)

An algorithm is a finite program for a unit-cost random-access machine whose registers hold
complex numbers. Its only access to the unknown input is the `query` instruction, which reads the
oracle `y` at the real part of a register; a query outside the allowed domain (the window
`[-1,1]` for signals, the index set `{0,…,m-1}` for vectors) makes the run fail. Randomness comes
from the `rand` instruction, which reads the next entry of an i.i.d. uniform `[0,1]` tape. Every
executed instruction costs one step (unit-cost exact arithmetic over `ℂ`, including `exp`,
`√` and `log` of a real part, and floor); the query count is the number of executed `query`
instructions. The output is the list written by `out` instructions. The program is a fixed finite
object: it never sees the hidden signal, its amplitudes, frequencies or clusters, and depends on
the oracle only through the answers of its queries. -/

/-- The instruction set. Registers are indexed by `ℕ`; `⌊·⌋` is applied to real parts for
indirect addressing. Division by zero returns `0` (Lean convention). -/
inductive Instr where
  /-- `r[d] := q` for a rational constant written in the program. -/
  | const (d : ℕ) (q : ℚ)
  /-- `r[d] := π`. -/
  | pi (d : ℕ)
  /-- `r[d] := i`. -/
  | imagUnit (d : ℕ)
  | add (d a b : ℕ)
  | sub (d a b : ℕ)
  | mul (d a b : ℕ)
  | div (d a b : ℕ)
  /-- `r[d] := conj r[a]`. -/
  | conj (d a : ℕ)
  /-- `r[d] := Re r[a]`. -/
  | re (d a : ℕ)
  /-- `r[d] := exp r[a]` (complex exponential). -/
  | cexp (d a : ℕ)
  /-- `r[d] := √(Re r[a])` (real square root, `0` for negative arguments). -/
  | sqrt (d a : ℕ)
  /-- `r[d] := log (Re r[a])` (natural logarithm; Lean's `Real.log`). -/
  | log (d a : ℕ)
  /-- `r[d] := ⌊Re r[a]⌋`. -/
  | floor (d a : ℕ)
  /-- Indirect load `r[d] := r[⌊Re r[a]⌋]` (negative addresses read register `0`). -/
  | load (d a : ℕ)
  /-- Indirect store `r[⌊Re r[a]⌋] := r[s]`. -/
  | store (a s : ℕ)
  /-- Jump to instruction `L` if `Re r[a] < Re r[b]`. -/
  | jlt (a b L : ℕ)
  /-- Unconditional jump. -/
  | jmp (L : ℕ)
  /-- `r[d] :=` the next uniform `[0,1]` draw of the random tape. -/
  | rand (d : ℕ)
  /-- Point query `r[d] := y(Re r[a])`; fails if `Re r[a]` is outside the query domain. -/
  | query (d a : ℕ)
  /-- Append `r[a]` to the output. -/
  | out (a : ℕ)
  | halt

/-- A program is a finite list of instructions; execution starts at instruction `0`. -/
abbrev Program := List Instr

/-- Run status. -/
inductive Status where
  | running
  | halted
  | failed
  deriving DecidableEq

/-- A machine configuration: program counter, registers, output so far, number of random
draws and of queries consumed, and status. -/
structure Config where
  pc : ℕ
  reg : ℕ → ℂ
  out : List ℂ
  draws : ℕ
  queries : ℕ
  status : Status

/-- The random tape: an infinite sequence of independent uniform `[0,1]` draws. -/
abbrev Tape := ℕ → unitInterval

/-- The law of the random tape (product of uniform measures on `[0,1]`). -/
noncomputable def tapeLaw : Measure Tape :=
  Measure.infinitePi (fun _ : ℕ => (volume : Measure unitInterval))

/-- Initial configuration: the inputs are written into registers `0, 1, …`; all other registers
are `0`. -/
def initConfig (input : List ℂ) : Config where
  pc := 0
  reg := fun i => input.getD i 0
  out := []
  draws := 0
  queries := 0
  status := .running

/-- Address read from a register: `⌊Re r⌋` as a natural number (negative values give `0`). -/
noncomputable def addr (z : ℂ) : ℕ := (Int.floor z.re).toNat

open Classical in
/-- One step of the machine with query domain `D`, oracle `y` and tape `ω`. A halted or failed
configuration is left unchanged; running past the end of the program halts. -/
noncomputable def step (P : Program) (D : Set ℝ) (y : ℝ → ℂ) (ω : Tape) (c : Config) :
    Config :=
  if c.status ≠ .running then c else
  match P[c.pc]? with
  | none => { c with status := .halted }
  | some ins =>
    let u : Config := { c with pc := c.pc + 1 }
    let set (d : ℕ) (v : ℂ) : Config := { u with reg := Function.update c.reg d v }
    match ins with
    | .const d q => set d (q : ℂ)
    | .pi d => set d (Real.pi : ℂ)
    | .imagUnit d => set d Complex.I
    | .add d a b => set d (c.reg a + c.reg b)
    | .sub d a b => set d (c.reg a - c.reg b)
    | .mul d a b => set d (c.reg a * c.reg b)
    | .div d a b => set d (c.reg a / c.reg b)
    | .conj d a => set d ((starRingEnd ℂ) (c.reg a))
    | .re d a => set d ((c.reg a).re : ℂ)
    | .cexp d a => set d (Complex.exp (c.reg a))
    | .sqrt d a => set d (Real.sqrt (c.reg a).re : ℂ)
    | .log d a => set d (Real.log (c.reg a).re : ℂ)
    | .floor d a => set d ((Int.floor (c.reg a).re : ℤ) : ℂ)
    | .load d a => set d (c.reg (addr (c.reg a)))
    | .store a s => { u with reg := Function.update c.reg (addr (c.reg a)) (c.reg s) }
    | .jlt a b L => if (c.reg a).re < (c.reg b).re then { u with pc := L } else u
    | .jmp L => { u with pc := L }
    | .rand d =>
        { u with reg := Function.update c.reg d (((ω c.draws : unitInterval) : ℝ) : ℂ),
                 draws := c.draws + 1 }
    | .query d a =>
        if (c.reg a).re ∈ D then
          { u with reg := Function.update c.reg d (y (c.reg a).re), queries := c.queries + 1 }
        else { c with status := .failed }
    | .out a => { u with out := c.out ++ [c.reg a] }
    | .halt => { c with status := .halted }

/-- The configuration after `n` steps from the initial configuration on `input`. -/
noncomputable def run (P : Program) (D : Set ℝ) (y : ℝ → ℂ) (ω : Tape) (input : List ℂ)
    (n : ℕ) : Config :=
  (step P D y ω)^[n] (initConfig input)

/-- The run on tape `ω` halts within `T` steps having made at most `Q` queries, and its output
satisfies `Good`. (A halted configuration never changes, so the configuration after `n` steps is
the final one.) -/
def HaltsWith (P : Program) (D : Set ℝ) (y : ℝ → ℂ) (ω : Tape) (input : List ℂ) (T Q : ℝ)
    (Good : List ℂ → Prop) : Prop :=
  ∃ n : ℕ, (n : ℝ) ≤ T ∧ (run P D y ω input n).status = .halted ∧
    ((run P D y ω input n).queries : ℝ) ≤ Q ∧ Good (run P D y ω input n).out

/-- The run on tape `ω` halts (within any number of steps) with an output satisfying `Good`. -/
def OutputSatisfies (P : Program) (D : Set ℝ) (y : ℝ → ℂ) (ω : Tape) (input : List ℂ)
    (Good : List ℂ → Prop) : Prop :=
  ∃ n : ℕ, (run P D y ω input n).status = .halted ∧ Good (run P D y ω input n).out

/-- Query domain for vectors `v ∈ ℂ^m`: the indices `0, …, m-1`. -/
def vecDomain (m : ℕ) : Set ℝ := {a | ∃ j : ℕ, j < m ∧ a = j}

/-- Query oracle of a vector `v ∈ ℂ^m`: `a ↦ v[a]` at an index, `0` elsewhere. -/
noncomputable def vecOracle {m : ℕ} (v : Fin m → ℂ) (a : ℝ) : ℂ :=
  ∑ j : Fin m, if ((j : ℕ) : ℝ) = a then v j else 0

end CaiFourierSparse.Learning


