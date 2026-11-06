-- Prove2me | Definitions.Def_NearLinIsing_Prog
-- name    : NearLinIsing_Prog
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:40:57.281404+00:00
-- url     : https://prove2.me/theorems/1dfc7df4-7f7d-49be-a0ac-632c8e547aa3
-- title:
--   Instrumented randomized programs: tape, cursor, operation counter and charged input access
-- statement:
--   This is the computational model of §2.6. A program reads an i.i.d. sequence of uniform numbers in $[0,1]$ through a cursor and increments an operation counter. One unit pays for a real $+,-,\times,\div$, comparison, $\lfloor\cdot\rfloor$, $\lceil\cdot\rceil$, $\log$, $\exp$ or $\sqrt{\cdot}$; a natural-number operation; an array or list cell read or write, a list cons or an array push; a loop dispatch; one read of an input cell; and one uniform draw. Allocating an array of length $k$ costs $k$. A Bernoulli($p$) draw is one uniform and one comparison, and a uniform index in $\{0,\dots,k-1\}$ is $\min(k-1,\lceil Uk\rceil-1)$, uniform up to a null event.
--
--   The input graph is read only through charged accessors. Run on a tape, a program gives a value and a cost. Expected work is the integral of the cost against the product law of the tape.
--
--   **Formalization Note** The counter is the published `Work` monad. This tape is uniform only; `SparseSDP.TwoSided.Prog` has a different tape, with Gaussian slots, so it is not the same machine. Binding a name to a computed value and creating an empty list pay nothing, which is a bounded amount per charged line.
-- source:
--   Miao, Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness Threshold, arXiv:2611.04786, §2.6, p. 9

import Mathlib
import Definitions.Def_CapacitatedAssort_General_Work
import Definitions.Def_NearLinIsing_IncGraph

open MeasureTheory

namespace NearLinIsing

open CapacitatedAssort.General (Work charge)

/-- The random tape: an i.i.d. sequence of uniform numbers in `[0, 1]` (§2.6, reading R3). -/
abbrev Tape : Type := ℕ → unitInterval

/-- The law of the tape: the infinite product of the uniform law on `[0, 1]`. -/
noncomputable def tapeLaw : Measure Tape :=
  Measure.infinitePi fun _ => (volume : Measure unitInterval)

/-- Instrumented randomized real-arithmetic programs (§2.6, p. 9; readings R2–R3): a read-only
tape, a cursor into it, and the operation counter of the published `Work` monad.

Miao, *Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness
Threshold*, arXiv:2611.04786, §2.6, p. 9.

Cost model (the complete list of unit-cost operations, reading R2): a real `+ − × ÷`, comparison,
`⌊·⌋`, `⌈·⌉`, `log`, `exp`, `√`; a natural-number operation or comparison; a Boolean test; an array
or list cell read or write, a list cons, an array push; one loop dispatch; one input-cell read
(`qN`, `qM`, `qEnd`, `qDeg`, `qInc`); one uniform draw from the tape. Allocating an array of length
`k` costs `k`. Every line of a program pays through `tick` or `op`, with a comment listing the
operations a grouped charge stands for. Binding a name to a value already computed and creating an
empty list or array pay nothing: there is a bounded number of these per charged line. A program
reads the input graph only through the charged accessors below and never reads the counter. -/
abbrev Prog (α : Type) : Type := ReaderT Tape (StateT ℕ Work) α

variable {α : Type}

/-- Run a program on a tape from a cursor and a counter: `((value, cursor), counter)`. -/
def Prog.exec (p : Prog α) (tape : Tape) (cur cnt : ℕ) : (α × ℕ) × ℕ :=
  StateT.run (StateT.run (p tape) cur) cnt

/-- The value of a run from cursor `0`. -/
def runVal (p : Prog α) (tape : Tape) : α := (p.exec tape 0 0).1.1

/-- The cost of a run: the final counter, from cursor `0` and count `0`. -/
def runCost (p : Prog α) (tape : Tape) : ℕ := (p.exec tape 0 0).2

/-- Pay `k` operations. -/
def tick (k : ℕ) : Prog Unit := fun _ => StateT.lift (charge k)

/-- `k` unit operations computing the value `v`. -/
def op (k : ℕ) (v : α) : Prog α := do tick k; pure v

/-- One uniform draw from the tape, at unit cost; the cursor advances. -/
def drawU : Prog ℝ := do
  tick 1
  fun tape => do
    let c ← (get : StateT ℕ Work ℕ)
    set (σ := ℕ) (c + 1)
    pure ((tape c : unitInterval) : ℝ)

/-- A Bernoulli(`p`) draw: one uniform `U`, one comparison, result `U < p` (reading R3). -/
noncomputable def bernoulli (p : ℝ) : Prog Bool := do
  let u ← drawU
  tick 1 -- comparison
  pure (decide (u < p))

/-- A uniform index in `{0, …, k−1}` (the paper's `{1, …, k}` shifted by one): one draw `U`, then
`min(k − 1, ⌈U k⌉ − 1)`, which is uniform up to the null event `U ∈ {0, 1/k, …}` (reading R3). -/
noncomputable def uniformIdx (k : ℕ) : Prog ℕ := do
  let u ← drawU
  tick 4 -- multiplication, ceiling, subtraction, minimum
  pure (min (k - 1) (⌈u * k⌉₊ - 1))

/-- Allocate an array of length `k` filled with `v`, at cost `k`. -/
def alloc (k : ℕ) (v : α) : Prog (Array α) := op k (Array.replicate k v)

/-- Read the number of vertices of the input (one input-cell read). -/
def qN (G : IncGraph) : Prog ℕ := op 1 G.n

/-- Read the number of edges of the input (one input-cell read). -/
def qM (G : IncGraph) : Prog ℕ := op 1 G.m

/-- Read the endpoint pair of edge `e` (one input-cell read); `(0, 0)` out of range. -/
def qEnd (G : IncGraph) (e : ℕ) : Prog (ℕ × ℕ) :=
  op 1 (if h : e < G.m then ((G.ends ⟨e, h⟩).1.val, (G.ends ⟨e, h⟩).2.val) else (0, 0))

/-- Read the length of the incidence list of `v` (one input-cell read); `0` out of range. -/
def qDeg (G : IncGraph) (v : ℕ) : Prog ℕ :=
  op 1 (if h : v < G.n then (G.inc ⟨v, h⟩).length else 0)

/-- Read the `i`-th entry of the incidence list of `v` (one input-cell read); `0` out of range. -/
def qInc (G : IncGraph) (v i : ℕ) : Prog ℕ :=
  op 1 (if h : v < G.n then (((G.inc ⟨v, h⟩)[i]?).map Fin.val).getD 0 else 0)

end NearLinIsing


