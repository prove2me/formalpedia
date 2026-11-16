-- Prove2me | Definitions.Def_LocalPush_Supplement_SampleMachine
-- name    : LocalPush_Supplement_SampleMachine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:17:35.487181+00:00
-- url     : https://prove2.me/theorems/5cea4e20-dfe5-463b-9d9a-cf4aa121e62a
-- title:
--   The sampling machine: the base real RAM plus a unit-cost uniform random integer; expected work and queries
-- statement:
--   The **sampling machine** extends the base mission's randomized real RAM (`LocalPush.Machine`) by one instruction, $\mathtt{randInt}(d,b)$: if the pointer register $p[b]$ holds an integer $b\ge1$, it writes a uniformly random integer from $\{0,\dots,b-1\}$ into $p[d]$, otherwise it writes $0$. It costs one unit of work and no graph query. Every other instruction is executed by the base machine's step function, with unchanged work and query counters; a program is admissible when its base part is admissible in the base sense (rational literals).
--
--   The randomness consists of two independent tapes: the base machine's fair coins, and a tape $u_0,u_1,\dots$ of independent uniform reals in $[0,1]$; the $j$-th executed $\mathtt{randInt}$ returns $\min\{\lfloor u_j b\rfloor,b-1\}$. For a program $P$, a graph and an input, the **work** (respectively **query count**) of a run is its counter at the first halting step, and $+\infty$ if the run never halts; the **expected running time** and **expected number of graph queries** are the expectations of these quantities over both tapes, as extended nonnegative reals.
--
--   The machine is the computational model of the single-pair upper bounds (Theorems 6.1 and 6.3), whose algorithms sample uniform random neighbours at constant cost each.
--
--   **Formalization Note** The paper charges $O(1)$ time per sample of a random neighbour (proof of Lemma 6.2, p.31), which fair coins cannot provide in a bounded number of steps; this is why the instruction is added. The value $u_j=1$ (a null event) is clamped to $b-1$.
-- source:
--   Cui, Wei, Yang, Revisiting Local Push, STOC 2027 submission (manuscript sha256 4c36279a…), §1.1, p.4 (PDF p.4) (adjacency-list model); proof of Lemma 6.2, p.31 (PDF p.31) ("Each sample uses O(1/α) expected time"); Theorems 6.1 and 6.3, pp.30, 32

import Mathlib
import Definitions.Def_LocalPush_Machine

open MeasureTheory

namespace LocalPush

namespace Supplement

/-!
# The sampling machine: the base machine plus a unit-cost uniform random integer; joint tapes and expectations

Cui, Wei, Yang, *Revisiting Local Push: Faster Algorithms and Optimal Query Complexity for PageRank and
Effective Resistance*, STOC 2027 submission (manuscript sha256 4c36279a…), §1.1, p.4 (PDF p.4) (the
adjacency-list model) and the proof of Lemma 6.2, p.31 (PDF p.31): "Each sample uses O(1/α) expected time and
graph queries." Theorems 6.1 (p.30) and 6.3 (p.32) bound expected graph queries and expected time.

**Formalization Note.**
* `SInstr` is the base instruction set of `LocalPush.Machine` plus one instruction `randInt dst bound`: if
  `p[bound] ≥ 1` it sets `p[dst]` to a uniformly random integer in `{0, …, p[bound] − 1}`, else `p[dst] := 0`.
  It costs one unit of work and no query. Sampling a uniform neighbour is charged `O(1)` time in the paper
  (p.31), which fair coins alone cannot provide in a bounded number of steps.
* Every other instruction is executed by the published `LocalPush.step` on `baseProgram P` (where `randInt`
  is replaced by a placeholder that is never dispatched), so the base semantics, work counter and query
  counter are unchanged. `SAdmissible P` is the base `Admissible (baseProgram P)`.
* The random integer comes from a second tape `u : ℕ → [0, 1]` of independent uniform reals: the `j`-th
  executed `randInt` returns `min ⌊u_j · p[bound]⌋ (p[bound] − 1)` (the `min` only matters on the null event
  `u_j = 1`). `jointTape` is the product of the base fair-coin tape and this tape.
* `haltWork` / `haltQueries` are the work and query counters at the first halting step, as `ℝ≥0∞`, and `∞`
  on a run that never halts; `expWork` / `expQueries` are their expectations over `jointTape`.
-/

/-- An instruction of the sampling machine: a base instruction, or `randInt dst bound`. -/
inductive SInstr where
  | base (instruction : Instr)
  | randInt (dst bound : ℕ)

/-- A program of the sampling machine: one finite list of instructions, the same for every input. -/
abbrev SProgram := List SInstr

/-- The base program executed for every non-`randInt` instruction; `randInt` becomes a placeholder `halt`,
which is never dispatched by `sstep`. -/
def baseProgram (P : SProgram) : Program :=
  P.map fun op => match op with
    | .base i => i
    | .randInt _ _ => .halt

/-- Admissibility is the base one: rational real literals, no core `accept`/`reject`. -/
def SAdmissible (P : SProgram) : Prop :=
  Admissible (baseProgram P)

/-- A state of the sampling machine: a base state and the cursor of the uniform tape. -/
structure SState where
  st : State
  sampleCursor : ℕ

/-- A uniform index from `u ∈ [0, 1]` and a bound `b`: `min ⌊u·b⌋ (b − 1)` if `b ≥ 1`, else `0`. -/
noncomputable def uniformIndex (u : unitInterval) (b : ℤ) : ℤ :=
  if 1 ≤ b then min ⌊(u : ℝ) * (b : ℝ)⌋ (b - 1) else 0

/-- One step of the sampling machine on the graph `nbrs`, the coin tape `ω` and the uniform tape `u`.
Halted states stutter at no cost; `randInt` costs one unit of work; everything else is the base `step`. -/
noncomputable def sstep (P : SProgram) {n : ℕ} (nbrs : Fin n → List (Fin n)) (ω : ℕ → Bool)
    (u : ℕ → unitInterval) (x : SState) : SState :=
  if x.st.halted then x else
    match P[x.st.core.pc]? with
    | some (.randInt d b) =>
        { st := { x.st with
            work := x.st.work + 1
            core := { x.st.core with
              pc := x.st.core.pc + 1
              ptrs := Function.update x.st.core.ptrs d
                (uniformIndex (u x.sampleCursor) (x.st.core.ptrs b)) } }
          sampleCursor := x.sampleCursor + 1 }
    | _ => { x with st := step (baseProgram P) nbrs ω x.st }

/-- The state after `t` steps of `P` from the base state `s₀` (uniform-tape cursor `0`). -/
noncomputable def srun (P : SProgram) {n : ℕ} (nbrs : Fin n → List (Fin n)) (s₀ : State) (ω : ℕ → Bool)
    (u : ℕ → unitInterval) (t : ℕ) : SState :=
  (sstep P nbrs ω u)^[t] ⟨s₀, 0⟩

/-- The uniform tape: independent uniform reals in `[0, 1]`. -/
noncomputable def sampleTape : Measure (ℕ → unitInterval) :=
  Measure.infinitePi (fun _ : ℕ => (volume : Measure unitInterval))

/-- The joint randomness of the sampling machine: fair coins and uniform reals, independent. -/
noncomputable def jointTape : Measure ((ℕ → Bool) × (ℕ → unitInterval)) :=
  coinTape.prod sampleTape

/-- The work counter at the first halting step, or `∞` if the run never halts. -/
noncomputable def haltWork (P : SProgram) {n : ℕ} (nbrs : Fin n → List (Fin n)) (s₀ : State)
    (p : (ℕ → Bool) × (ℕ → unitInterval)) : ENNReal :=
  ⨅ (t : ℕ) (_ : (srun P nbrs s₀ p.1 p.2 t).st.halted = true), ((srun P nbrs s₀ p.1 p.2 t).st.work : ENNReal)

/-- The query counter at the first halting step, or `∞` if the run never halts. -/
noncomputable def haltQueries (P : SProgram) {n : ℕ} (nbrs : Fin n → List (Fin n)) (s₀ : State)
    (p : (ℕ → Bool) × (ℕ → unitInterval)) : ENNReal :=
  ⨅ (t : ℕ) (_ : (srun P nbrs s₀ p.1 p.2 t).st.halted = true),
    ((srun P nbrs s₀ p.1 p.2 t).st.queries : ENNReal)

/-- The expected running time (work) of `P` on input `s₀`. -/
noncomputable def expWork (P : SProgram) {n : ℕ} (nbrs : Fin n → List (Fin n)) (s₀ : State) : ENNReal :=
  ∫⁻ p, haltWork P nbrs s₀ p ∂jointTape

/-- The expected number of graph queries of `P` on input `s₀`. -/
noncomputable def expQueries (P : SProgram) {n : ℕ} (nbrs : Fin n → List (Fin n)) (s₀ : State) :
    ENNReal :=
  ∫⁻ p, haltQueries P nbrs s₀ p ∂jointTape

end Supplement

end LocalPush


