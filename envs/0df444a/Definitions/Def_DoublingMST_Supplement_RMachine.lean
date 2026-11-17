-- Prove2me | Definitions.Def_DoublingMST_Supplement_RMachine
-- name    : DoublingMST_Supplement_RMachine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:16:04.936806+00:00
-- url     : https://prove2.me/theorems/1a8e77f8-f576-4085-b0f2-498a7052370c
-- title:
--   The randomized real RAM of Definition 2.1 (coins, uniform reals, one-step integer operations) and its Euclidean input layout
-- statement:
--   The **randomized real RAM** extends the published deterministic machine of Definition 2.1 (`DoublingMST.Machine`: real and integer registers, exact $+,-,\times,/$ and comparisons on reals, integer $+,-$, comparisons and indirect addressing, a unit-cost exact-distance oracle, output as $n-1$ pairs of labels) by an input-independent random tape. A program is a finite list of instructions; besides every instruction of the base machine (with its published semantics) it may use
--
--   1. `coin`: write the next bit of a sequence of independent fair bits (as $0$ or $1$) into an integer register;
--   2. `unif`: write the next entry of a sequence of independent uniform reals in $[0,1]$ into a real register;
--   3. `intOp f`: apply an arbitrary function $f:\mathbb Z\times\mathbb Z\to\mathbb Z$ to two integer registers, in one step.
--
--   The tape law $\mathbb P$ makes the bit sequence and the uniform sequence independent, each i.i.d. Every executed instruction costs one unit; the **running time** $T(\omega)\in\mathbb N\cup\{\infty\}$ of a run on tape $\omega$ is the number of executed steps up to and including `halt`, and $\infty$ if the run never halts. A program is **coin-only** if it uses no `unif` and no `intOp` instruction.
--
--   For Euclidean inputs $x_0,\dots,x_{n-1}\in\mathbb R^{\dim}$ the input layout stores $n$ in integer register $0$, $\epsilon$ in real register $0$, and coordinate $j$ of $x_i$ in real memory cell $i\cdot\dim+j$; there are no labels, no distance oracle and no square root. The output pairs are point indices $0,\dots,n-1$.
--
--   This machine is the model of the paper's expected-time Euclidean algorithm (Theorem 1.2) and of its randomized lower bound (Theorem 1.3).
--
--   **Formalization Note** The base machine is reused unchanged: a `base` instruction is executed by `DoublingMST.step`. Running times are in $\mathbb N_\infty$, so expectations are lower Lebesgue integrals in $[0,\infty]$. A Euclidean run is a run with zero labels, so a distance-oracle call gets stuck (never halts). Theorem 1.2 restricts to coin-only programs (a weaker machine, so the existence claim is stronger); Theorem 1.3 allows every instruction (a richer machine, so the lower bound is stronger).
-- source:
--   Höckendorff–Hommelsheim–Sohler–Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b3…be759), Definition 2.1, p.11 (PDF p.13): random tape and Euclidean coordinate inputs; used by Theorem 1.2 (pp.2–3) and Theorem 1.3 (p.3)

import Mathlib
import Definitions.Def_DoublingMST_Machine
open scoped Classical

namespace DoublingMST.Supplement

open MeasureTheory

/-!
# The randomized real RAM of Definition 2.1

Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning
Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759),
Definition 2.1, p.11 (PDF p.13): "Randomized algorithms use an input-independent random tape."
Used by Theorem 1.2 (p.2, Euclidean inputs) and Theorem 1.3 (p.3, lower bound).

The machine extends the published deterministic machine `DoublingMST.Machine` without changing it:
a `base` instruction runs with exactly the published semantics (`DoublingMST.step`), and three
instructions are added.

**Formalization Note.**
* `coin dst`: `p[dst] :=` the next bit of a fair-bit tape, as `1` (true) or `0` (false).
* `unif dst`: `r[dst] :=` the next cell of a tape of independent uniform reals in `[0, 1]`.
* `intOp f dst a b`: `p[dst] := f p[a] p[b]` for an arbitrary `f : ℤ → ℤ → ℤ`, in one step (any
  "ordinary RAM operation" on integers, and more).
* The tape is a pair (bits, uniforms) with law `tapeLaw`: the bits are i.i.d. fair, the uniforms
  i.i.d. uniform on `[0, 1]`, and the two sequences are independent. One read counter per tape;
  each read consumes a fresh cell, so the tape is input-independent.
* Every executed instruction costs one step, as in the base machine. `haltTime` is the number of
  steps until the `halt` instruction has executed (`⊤` if the run never halts, including a stuck
  run: an invalid program counter, or an oracle call on a non-label argument).
* Theorem 1.2 restricts to `CoinOnly` programs (no `unif`, no `intOp`): a weaker machine, so an
  existence statement over it is stronger. Theorem 1.3 quantifies over all programs: a richer
  machine, so a lower bound over it is stronger.
* Euclidean input layout (`initEuclid`, Theorem 1.2): pointer register `0` holds `n`; real register
  `0` holds `ϵ`; real memory cell `i · dim + j` (`0 ≤ i < n`, `0 ≤ j < dim`) holds coordinate `j`
  of point `i`; every other register and cell, and all integer memory, is `0`. There are no labels
  and no oracle: a Euclidean run uses `noLabels`/`noDist` (zero points), so a `dist` instruction is
  stuck. There is no square root (Definition 2.1: "square-root operations can be avoided").
  Output pairs are point indices `0, …, n − 1`, laid out as in `DoublingMST.outputPairs`.
* All events and running times used in the theorems are measurable functions of the tape: each
  step reads finitely many tape cells, and the state after `k` steps is obtained from them by
  arithmetic, comparisons and countably many discrete branches.
-/

/-- An instruction of the randomized machine. -/
inductive RInstr where
  | base (i : DoublingMST.Instr)
  | coin (dst : ℕ)
  | unif (dst : ℕ)
  | intOp (f : ℤ → ℤ → ℤ) (dst a b : ℕ)

/-- A program: one finite list of instructions. -/
abbrev RProgram := List RInstr

/-- The base-machine table of `P`: added instructions are placeholders, always dispatched by
`rstep` before the table is consulted. Indices (and so jump targets) are unchanged. -/
def baseProgram (P : RProgram) : DoublingMST.Program :=
  P.map fun op => match op with
    | .base i => i
    | _ => .halt

/-- A state: the base machine's state and the read positions on the two tapes. -/
structure RState where
  st : DoublingMST.State
  coinPos : ℕ
  unifPos : ℕ

/-- The random tape: a sequence of bits and a sequence of reals in `[0, 1]`. -/
abbrev Tape := (ℕ → Bool) × (ℕ → unitInterval)

/-- The law of the tape: i.i.d. fair bits, independent of i.i.d. uniform reals on `[0, 1]`. -/
noncomputable def tapeLaw : Measure Tape :=
  (Measure.infinitePi fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure).prod
    (Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval))

instance : IsProbabilityMeasure tapeLaw := by
  unfold tapeLaw; infer_instance

/-- One step of `P` on labels `ι`, oracle `d` and tape `ω`. -/
noncomputable def rstep {n : ℕ} (P : RProgram) (ι : Fin n → ℤ) (d : Fin n → Fin n → ℝ)
    (ω : Tape) (r : RState) : RState :=
  if r.st.halted || r.st.stuck then r else
    let s := r.st
    let adv : DoublingMST.State :=
      { s with work := s.work + 1, core := { s.core with pc := s.core.pc + 1 } }
    match P[s.core.pc]? with
    | none => { r with st := { s with work := s.work + 1, stuck := true } }
    | some (.base _) => { r with st := DoublingMST.step (baseProgram P) ι d s }
    | some (.coin dst) =>
        ⟨{ adv with core := { adv.core with
            ptrs := Function.update s.core.ptrs dst (if ω.1 r.coinPos then 1 else 0) } },
          r.coinPos + 1, r.unifPos⟩
    | some (.unif dst) =>
        ⟨{ adv with core := { adv.core with
            regs := Function.update s.core.regs dst ((ω.2 r.unifPos : unitInterval) : ℝ) } },
          r.coinPos, r.unifPos + 1⟩
    | some (.intOp f dst a b) =>
        { r with st := { adv with core := { adv.core with
            ptrs := Function.update s.core.ptrs dst (f (s.core.ptrs a) (s.core.ptrs b)) } } }

/-- The state after `k` steps from the base state `s₀`, with both tapes read from position `0`. -/
noncomputable def rrun {n : ℕ} (P : RProgram) (ι : Fin n → ℤ) (d : Fin n → Fin n → ℝ)
    (ω : Tape) (s₀ : DoublingMST.State) (k : ℕ) : RState :=
  (rstep P ι d ω)^[k] ⟨s₀, 0, 0⟩

/-- The running time: the least `k` such that the run is halted after `k` steps, `⊤` if none. -/
noncomputable def haltTime {n : ℕ} (P : RProgram) (ι : Fin n → ℤ) (d : Fin n → Fin n → ℝ)
    (ω : Tape) (s₀ : DoublingMST.State) : ℕ∞ :=
  ⨅ (k : ℕ) (_ : (rrun P ι d ω s₀ k).st.halted = true), (k : ℕ∞)

/-- The run halts, and at halting its `m − 1` output pairs (`DoublingMST.outputPairs m`) are
`out`. After `halt` the state stutters, so the output is that of any halted step. -/
def HaltsWith {n : ℕ} (P : RProgram) (ι : Fin n → ℤ) (d : Fin n → Fin n → ℝ) (ω : Tape)
    (s₀ : DoublingMST.State) (m : ℕ) (out : List (ℤ × ℤ)) : Prop :=
  ∃ k : ℕ, (rrun P ι d ω s₀ k).st.halted = true ∧
    DoublingMST.outputPairs m (rrun P ι d ω s₀ k).st = out

/-- `P` uses only base instructions and fair coins. -/
def CoinOnly (P : RProgram) : Prop :=
  ∀ op ∈ P, (∃ i, op = RInstr.base i) ∨ ∃ dst, op = RInstr.coin dst

/-- No labels: the empty label map, for Euclidean runs (no oracle). -/
def noLabels : Fin 0 → ℤ := Fin.elim0

/-- No oracle: the empty distance function, for Euclidean runs. -/
def noDist : Fin 0 → Fin 0 → ℝ := fun a _ => a.elim0

/-- The Euclidean input layout: `p[0] = n`, `r[0] = ϵ`, real memory cell `i · dim + j` holds
coordinate `j` of point `i`, everything else `0`. -/
noncomputable def initEuclid {n dim : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin dim)) (ϵ : ℝ) :
    DoublingMST.State where
  core := ⟨0, Function.update (fun _ => 0) 0 ϵ, Function.update (fun _ => 0) 0 (n : ℤ),
    fun c => if h : ∃ (i : Fin n) (j : Fin dim), c = (i : ℤ) * dim + j
      then x h.choose h.choose_spec.choose else 0⟩
  integerMemory := fun _ => 0
  halted := false
  stuck := false
  work := 0

end DoublingMST.Supplement


