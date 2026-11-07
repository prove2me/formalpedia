-- Prove2me | Definitions.Def_RealAPSP_Machine
-- name    : RealAPSP_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:56:22.590441+00:00
-- url     : https://prove2.me/theorems/cd9b1504-b3be-4e4c-a00d-74f039991c41
-- title:
--   The comparison-addition machine, with coins in memory, and its deterministic and randomized runs
-- statement:
--   The **comparison-addition model** is the word RAM augmented with two real-valued operations, comparisons and additions. This definition makes it a concrete machine.
--
--   A program is a finite list of instructions together with a word exponent $c$. The integer bank has registers and an indirectly addressed memory, with an integer literal, addition, subtraction, multiplication, floor division, shifts, bit length, load, store and a jump on $\le$. The real bank has registers and a memory addressed by integers, with the literal $0$, addition, copy, load, store, a three-way comparison and negation. There is no other real literal, no real multiplication, division or floor, and no cast between the banks.
--
--   On a run with word bound $W=\mathrm{width}^c$, an integer result, address or shift outside $[-W,W]$ makes the machine stuck forever. Every instruction costs one step. Fair coin bits are preloaded in the odd negative integer cells.
--
--   A **deterministic run** within time $T$ is a run on the all-false coin tape that has halted after $\lfloor T\rfloor$ steps, with a good final state. A **randomized run** within time $T$ and failure probability $\delta$ has halted after $\lfloor T\rfloor$ steps on every tape, and has a good final state on a measurable set of tapes of probability at least $1-\delta$.
--
--   These are the machine statements of the whole mission: Theorem 1.1 and every algorithmic lemma are run predicates on this machine.
--
--   **Formalization Note** The instruction set reuses the published `GuardedSSSP.Machine.Instr`, and adds real negation because the page's comparisons $\sum_i n_i\alpha_i\ge 0$ have arbitrary non-zero integer coefficients. The page's "realistic" variant of the model is not formalized.
-- source:
--   Fischer, Polak, Schmidt, Real-to-Integer Reduction for All-Pairs Shortest Paths, arXiv:2611.04847 (held file sha256 a3dc0096…), §1.2, p.3 (PDF p.5)

import Mathlib
import Definitions.Def_GuardedSSSP_Machine

open MeasureTheory

namespace RealAPSP

/-!
# The comparison-addition machine, run on a coin tape

N. Fischer, A. Polak, J. Schmidt, *Real-to-Integer Reduction for All-Pairs Shortest Paths*,
arXiv:2611.04847 (held file sha256 a3dc0096…), §1.2, p.3 (PDF p.5): "All our reductions work in the
comparison-addition model, which is the word RAM model augmented with only two real-valued operations:
comparisons and additions."

The instruction set is the published `GuardedSSSP.Machine.Instr`, with one added real instruction `rneg`.

* **Integer bank.** Registers and an indirectly addressed memory; literal, `+`, `−`, `×`, floor division,
  shifts, bit length, load, store, and the jump on `≤`.
* **Real bank.** Registers and a memory addressed by integers; the literal `0`, `+`, copy, load, store,
  the three-way compare, and `rneg`. No real literal other than `0`, no real multiplication, division or
  floor, and no cast between the banks. A program computes only integer combinations of its input reals.

**Formalization Note.**
* **`rneg`.** The page's comparisons `∑ nᵢαᵢ ≥ 0` have "arbitrary non-zero integer coefficients", so negative
  coefficients are in the model. A machine without `rneg` simulates it by pairs `(p, q)` standing for `p − q`
  at constant overhead, so `rneg` adds convenience and no power.
* **Word bound.** An integer result, memory address or shift amount outside `[−W, W]` sends the machine to a
  stuck state, which never halts. Here `W = width ^ P.wordExp`, with `P.wordExp` fixed with the program and
  `width` a function of the instance chosen by each statement. So words have `O(log width)` bits.
* **Cost.** Unit cost: every executed instruction, including `halt`, is one step. A halted state stutters, so
  "halted after `⌊T⌋` steps" says the running time is at most `T`, and the state then is the final state.
  The page's "realistic" variant, which defers to [FPS26, Section 1.1], is not formalized.
* **Coins.** Fair bits are preloaded: integer cell `−(2t+1)` holds bit `t` of the tape, read at unit cost like
  any other cell. There is no coin instruction. A deterministic run is a run on the all-false tape.
* **Input.** Integer cell `z ≥ 0` holds the `z`-th entry of `ints`, real cell `z ≥ 0` the `z`-th entry of
  `reals`; every other cell and every register starts at `0`.
* **Output.** Integer outputs are in the even negative cells `outCell k = −(2k+2)`, real outputs in the negative
  real cells `routCell k = −1−k`. Each statement fixes its own layout.
-/

/-- A machine state: that of the published machine (pc, both banks, `halted`, `stuck`). -/
abbrev State : Type := GuardedSSSP.Machine.State

/-- An instruction: one of the published machine, or the real negation `rneg d a` (`§1.2`, p.3). -/
inductive Instr : Type
  | core (i : GuardedSSSP.Machine.Instr)
  | rneg (d a : ℕ)

/-- A program: a finite instruction list and the exponent of its word bound. -/
structure Program : Type where
  code : List Instr
  wordExp : ℕ

/-- The word bound `W = width ^ wordExp`. -/
def wordBound (P : Program) (width : ℕ) : ℤ := (width : ℤ) ^ P.wordExp

/-- One step under word bound `W`. Halted and stuck states stutter; an invalid program counter is stuck. -/
noncomputable def step (P : Program) (W : ℤ) (σ : State) : State :=
  if σ.halted || σ.stuck then σ else
    match P.code[σ.pc]? with
    | none => σ.toStuck
    | some (.core i) => GuardedSSSP.Machine.exec1 W σ i
    | some (.rneg d a) => GuardedSSSP.Machine.setR σ d (-(σ.rreg a))

/-- Integer cell holding coin `t`. -/
def coinCell (t : ℕ) : ℤ := -(2 * (t : ℤ) + 1)

/-- Integer output cell `k`. -/
def outCell (k : ℕ) : ℤ := -(2 * (k : ℤ) + 2)

/-- Real output cell `k`. -/
def routCell (k : ℕ) : ℤ := -1 - (k : ℤ)

/-- The initial state on a coin tape and the input cells. -/
noncomputable def initState (tape : ℕ → Bool) (ints : List ℤ) (reals : List ℝ) : State where
  pc := 0
  ireg := fun _ => 0
  imem := fun z =>
    if 0 ≤ z then ints.getD z.toNat 0
    else if z % 2 = 1 then (if tape ((-z - 1) / 2).toNat then 1 else 0)
    else 0
  rreg := fun _ => 0
  rmem := fun z => if 0 ≤ z then reals.getD z.toNat 0 else 0
  halted := false
  stuck := false

/-- The state after `t` steps. -/
noncomputable def stateAt (P : Program) (width : ℕ) (tape : ℕ → Bool) (ints : List ℤ) (reals : List ℝ)
    (t : ℕ) : State :=
  (step P (wordBound P width))^[t] (initState tape ints reals)

/-- The state after `⌊T⌋` steps, which is the final state when the run halts within `T`. -/
noncomputable def finalState (P : Program) (width : ℕ) (tape : ℕ → Bool) (ints : List ℤ) (reals : List ℝ)
    (T : ℝ) : State :=
  stateAt P width tape ints reals ⌊T⌋₊

/-- The run has halted within `T` steps. -/
def HaltsBy (P : Program) (width : ℕ) (tape : ℕ → Bool) (ints : List ℤ) (reals : List ℝ) (T : ℝ) : Prop :=
  (finalState P width tape ints reals T).halted = true

/-- The law of the coin tape: independent fair bits. -/
noncomputable def coinTape : Measure (ℕ → Bool) :=
  Measure.infinitePi (fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure)

/-- The all-false tape, on which a run is deterministic. -/
def zeroTape : ℕ → Bool := fun _ => false

/-- Deterministic run: on the all-false tape the program halts within `T`, and its final state is good. -/
def Runs (P : Program) (width : ℕ) (ints : List ℤ) (reals : List ℝ) (T : ℝ) (Good : State → Prop) : Prop :=
  HaltsBy P width zeroTape ints reals T ∧ Good (finalState P width zeroTape ints reals T)

/-- Randomized run: on every tape the program halts within `T` (worst-case time), and there is a measurable
set of tapes of probability at least `1 − fail` on which the final state is good. -/
def RunsWhp (P : Program) (width : ℕ) (ints : List ℤ) (reals : List ℝ) (T fail : ℝ)
    (Good : State → Prop) : Prop :=
  (∀ tape, HaltsBy P width tape ints reals T) ∧
    ∃ E : Set (ℕ → Bool), MeasurableSet E ∧ ENNReal.ofReal (1 - fail) ≤ coinTape E ∧
      ∀ tape ∈ E, Good (finalState P width tape ints reals T)

/-- A later program starting on an earlier final state: registers and counter reset, the memory kept, and `v`
written to integer cell `cell`. Used only for the evaluator of Lemma 4.8. -/
noncomputable def restart (σ : State) (cell v : ℤ) : State where
  pc := 0
  ireg := fun _ => 0
  imem := Function.update σ.imem cell v
  rreg := fun _ => 0
  rmem := σ.rmem
  halted := false
  stuck := false

/-- The state after `⌊T⌋` steps of `P` from an arbitrary state. -/
noncomputable def resume (P : Program) (width : ℕ) (σ : State) (T : ℝ) : State :=
  (step P (wordBound P width))^[⌊T⌋₊] σ

end RealAPSP


