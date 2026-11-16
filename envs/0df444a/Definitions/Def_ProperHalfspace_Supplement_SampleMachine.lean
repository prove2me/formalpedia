-- Prove2me | Definitions.Def_ProperHalfspace_Supplement_SampleMachine
-- name    : ProperHalfspace_Supplement_SampleMachine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:49:48.305863+00:00
-- url     : https://prove2.me/theorems/3e578469-b9e7-4e4b-9ab2-d92e6b1fd4ab
-- title:
--   The sample-access real RAM with fair coins, and the probability over coins and independent examples
-- statement:
--   The machine of the mission (a unit-cost real RAM with exact $+,-,\times,\div$, integer pointers, fair coins and rational literals, and no square root, logarithm, exponential, floor or eigensolver) with its membership query removed and a **sample instruction** added. The sample instruction reads the next labeled example $(x,y)$ from the sample stream, writes $x_1,\dots,x_n$ into $n$ consecutive memory cells and $y$ into a register, and costs $n+1$ units of work. A program is **admissible** if its real literals are rational and it uses neither the core accept/reject instructions nor the membership query, so it reads the distribution only through samples. Every other instruction costs one unit of work.
--
--   For a labeled distribution $D$ and a budget $B$, the probability of an event $A$ of the coin tape and the sample stream is
--   $$\Pr[A]=\sum_{\tau\in\{0,1\}^B}\ \sum_{\sigma\in(\{\pm1\}^n\times\{\pm1\})^B}2^{-B}\Big(\prod_{k<B}D(\sigma_k)\Big)\,\mathbf 1[A(\tau,\sigma)],$$
--   that is, fair coins and $B$ independent examples from $D$, independent of the coins. A run within $B$ units of work reads at most $B$ coins and at most $B$ examples.
--
--   This is the computational model of "an algorithm using only independent labeled examples from $D$" whose running time counts arithmetic operations.
--
--   **Formalization Note** Non-sample instructions execute exactly as in the mission's published machine `ProperHalfspace.Machine`. Tape positions past $B$ read $0$ and stream positions past $B$ read the fixed example $(1,\dots,1;1)$. A halted machine stutters at no cost.
-- source:
--   De, Mossel, Nadimpalli, Neeman, Efficient Proper Agnostic Learning of Halfspaces, arXiv:2611.02344 (Nov. 1, 2026), Theorem 2, p.2 (real-RAM model, p.2); §5, pp.30–34

import Mathlib
import Definitions.Def_ProperHalfspace_Machine
import Definitions.Def_ProperHalfspace_Supplement_LabeledDist

namespace ProperHalfspace

/-!
# The sample-access real RAM with fair coins

De, Mossel, Nadimpalli, Neeman, arXiv:2611.02344 (Nov. 1, 2026), Theorem 2, p.2 (PDF p.4) and §5, pp.30–34 (PDF pp.32–36):
"there is an algorithm using only independent labeled examples from D"; "All running-time bounds in this paper count
arithmetic operations in the real-RAM model" (p.2).

**Formalization Note.** The machine is the published `ProperHalfspace.Machine` (the `SmaleNinth.RAMInstr` core with exact
`+ − × ÷` and `x/0 = 0`, integer pointer `+`/`−` and integer memory, the one-way pointer-to-real cast, fair coins, `halt`;
no square root, exponential, logarithm, floor, eigensolver or uniform real draw), with its membership query replaced by a
sample instruction:
* `sample d q` reads the next example `(x, y)` of the sample stream, writes `M[p[q] + i] := xᵢ ∈ {±1}` for `i < n` and
  `r[d] := y ∈ {±1}`, adds one to `samples` and `n + 1` to `work` (it writes `n + 1` values).
* `SAdmissible` keeps the published restrictions (rational literals, no core `accept`/`reject`) and also forbids the
  published `query`, so the program reads `D` only through `sample`.
Every non-`sample` instruction executes exactly as in the published `step` (the oracle passed there is never consulted by
an admissible program). Every executed instruction costs at least one unit of work; an invalid program counter is stuck and
charged; a halted machine stutters at no cost.

Randomness: a run within `B` units of work reads at most `B` coins and at most `B` samples. `sampleProb D B A` is the
probability of an event `A` of (coin tape, sample stream) when the coins are fair and the first `B` samples are independent
draws from `D`, independent of the coins: a finite sum over the `2^B` tapes and the streams of length `B`, weighted by
`2^{−B} ∏_{k<B} D(σₖ)`. Positions past `B` read `false` and the fixed example `(1, …, 1; 1)`.
-/

namespace Supplement

/-- One instruction: an instruction of the published machine, or `sample`. -/
inductive SInstr : Type
  /-- An instruction of the published `ProperHalfspace.Instr`. -/
  | base (i : Instr)
  /-- `sample d q`: read the next labeled example `(x, y)`; `M[p[q] + i] := xᵢ` for `i < n`, `r[d] := y`. -/
  | sample (d q : ℕ)

/-- A program: a finite list of instructions, executed from position `0`. -/
abbrev SProgram := List SInstr

/-- Real literals are rational, the core `accept`/`reject` do not occur, and there is no membership query. -/
def SAdmissible (P : SProgram) : Prop :=
  ∀ i ∈ P, ∀ j : Instr, i = .base j →
    (∀ d c, j = .core (.const d c) → ∃ q : ℚ, c = (q : ℝ)) ∧
      j ≠ .core .accept ∧ j ≠ .core .reject ∧ ∀ d q, j ≠ .query d q

/-- The published instruction executed at a position; `sample` is never executed through it. -/
def SInstr.toInstr : SInstr → Instr
  | .base i => i
  | .sample _ _ => .halt

/-- A configuration: a configuration of the published machine and the number of samples read. -/
structure SState where
  /-- The published configuration (core state, integer memory, coins, queries, work, halted). -/
  st : State
  /-- The number of labeled examples read. -/
  samples : ℕ

/-- The real memory after `sample` writes the cube point `x` into the `n` cells starting at `base`. -/
noncomputable def writePoint {n : ℕ} (mem : ℤ → ℝ) (base : ℤ) (x : Cube n) : ℤ → ℝ := fun a =>
  if h : base ≤ a ∧ a < base + n then coord x ⟨(a - base).toNat, by omega⟩ else mem a

/-- One step. A halted state stutters at no cost. The sample stream occurs only in the `sample` branch; every other
instruction is executed by the published `step`. -/
noncomputable def sstep (P : SProgram) {n : ℕ} (stream : ℕ → Example n) (tape : ℕ → Bool) (s : SState) : SState :=
  if s.st.halted then s else
    match P[s.st.cfg.pc]? with
    | some (.sample d q) =>
        let z := stream s.samples
        { st := { s.st with
            cfg := ⟨s.st.cfg.pc + 1, Function.update s.st.cfg.regs d ((z.2 : ℤ) : ℝ), s.st.cfg.ptrs,
              writePoint s.st.cfg.mem (s.st.cfg.ptrs q) z.1⟩
            work := s.st.work + (n + 1) }
          samples := s.samples + 1 }
    | _ => { s with st := step (P.map SInstr.toInstr) (fun _ : Cube n => (0 : ℝ)) tape s.st }

/-- The state after `t` steps from `s₀`. -/
noncomputable def srun (P : SProgram) {n : ℕ} (stream : ℕ → Example n) (tape : ℕ → Bool) (s₀ : SState) (t : ℕ) :
    SState :=
  (sstep P stream tape)^[t] s₀

/-- Theorem 2's input, the layout of the published goal: pointer `0` holds `n`, `M[0] = ε`, everything else `0`; no sample
read yet. -/
noncomputable def sInit (n : ℕ) (ε : ℝ) : SState := ⟨goalInit n ε, 0⟩

/-- A stream of `B` examples extended by the fixed example `(1, …, 1; 1)`. -/
def extendStream {n B : ℕ} (σ : Fin B → Example n) (k : ℕ) : Example n :=
  if h : k < B then σ ⟨k, h⟩ else (fun _ => 1, 1)

open Classical in
/-- The probability of an event of (coin tape, sample stream): fair coins, and `B` independent examples from `D`. -/
noncomputable def sampleProb {n : ℕ} (D : Example n → ℝ) (B : ℕ)
    (A : (ℕ → Bool) → (ℕ → Example n) → Prop) : ℝ :=
  ∑ τ : Fin B → Bool, ∑ σ : Fin B → Example n,
    ((2 : ℝ) ^ B)⁻¹ * (∏ k, D (σ k)) * if A (extendTape τ) (extendStream σ) then 1 else 0

end Supplement

end ProperHalfspace


