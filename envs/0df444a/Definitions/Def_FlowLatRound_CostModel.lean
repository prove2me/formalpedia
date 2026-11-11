-- Prove2me | Definitions.Def_FlowLatRound_CostModel
-- name    : FlowLatRound_CostModel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:54:57.483474+00:00
-- url     : https://prove2.me/theorems/a44dcbe3-919e-4926-9804-5ee41db80673
-- title:
--   App. B, pp.18–19 — the bit-cost counter, fair-bit tape, rejection sampling, halting, cost and expected cost
-- statement:
--   The computational model of Appendix B: rationals in binary, exact arithmetic, expected time over the random choices, rejection sampling for uniform choices.
--
--   1. A deterministic program carries a cost counter. An arithmetic operation or comparison on rationals $a,b$ costs $(\mathrm{bits}(a)+\mathrm{bits}(b)+1)^2$, where $\mathrm{bits}(q)$ is the binary length of numerator and denominator plus one; a list or array step costs $1$.
--   2. A randomized program reads independent fair bits from a tape $\omega\in\{0,1\}^{\mathbb N}$ (each read costs $1$). A uniform element of $\{0,\dots,N-1\}$ is drawn by rejection sampling: read $\lceil\log_2N\rceil$ bits and retry while the value is $\ge N$.
--   3. Loops take a fuel bound; a program **halts** on $\omega$ if some fuel suffices, and its output and cost are those at the least sufficient fuel. A non-halting run costs $+\infty$.
--   4. The tape law is the product of fair coins, and the expected cost is the integral of the cost over it.
--
--   **Formalization Note** A single charge may cover an explicitly counted group of operations, and index comparisons may be charged with the largest index (an upper bound); no charge is an asymptotic bound.
-- source:
--   Chang, Replicable Mean Estimation via Random Lattice Rounding (manuscript, STOC 2027 submission, sha256 35bd3e4b…aeac), Appendix B, "Computational model", pp.18–19 (PDF 20–21)

import Mathlib

namespace FlowLatRound

open MeasureTheory
open scoped ENNReal

/-! # The computational model: bit-cost counter and fair-bit tape

Chang, *Replicable Mean Estimation via Random Lattice Rounding* (manuscript, STOC 2027
submission, sha256 35bd3e4b…aeac), Appendix B, "Computational model", pp.18–19 (PDF 20–21):
rationals in binary, exact arithmetic, expected time over the random choices, and rejection
sampling for uniform choices from sets whose size is not a power of two.

**Formalization Note.** A deterministic program is a `Counted α = StateM ℕ α`, the state being
the cost spent so far. An integer or rational operation (or comparison) on operands `a, b`
charges `opCost a b = (ratBits a + ratBits b + 1)^2`, where `ratBits q` is the binary length of
numerator and denominator; a list or array step charges `1`. A charge may cover an explicitly
counted group of operations (never an asymptotic bound), and a comparison of indices `≤ N` may
be charged `opCost N N` (an upper bound). A randomized program is
`RProg α = ReaderT (ℕ → Bool) (StateT (ℕ × ℕ) Option) α`: it reads a tape of fair bits, its
state is (tape position, cost), and `none` means "ran out of fuel". Programs with loops take a
fuel argument `N` (every rejection loop may retry at most `N` times); a program **halts** on a
tape if some fuel suffices, and its output and cost are those at the least such fuel. The cost
of a non-halting run is `⊤`, so a finite expected cost forces almost sure halting. The tape is
the product of fair coins. Sets of tapes are measured with the outer measure and costs are
integrated with the lower Lebesgue integral `∫⁻`; the sets and functions here are measurable
(each depends on finitely many bits on each halting run), so these are the usual values. -/

/-- A deterministic program with a cost counter. -/
abbrev Counted (α : Type) := StateM ℕ α

/-- Add `k` to the cost counter. -/
def charge (k : ℕ) : Counted Unit := modify (· + k)

/-- The binary length of a rational number: bits of the numerator's absolute value, of the
denominator, and a sign bit. -/
def ratBits (q : ℚ) : ℕ := Nat.size q.num.natAbs + Nat.size q.den + 1

/-- The charge of one arithmetic operation or comparison on `a` and `b`. -/
def opCost (a b : ℚ) : ℕ := (ratBits a + ratBits b + 1) ^ 2

/-- A randomized program reading fair bits from a tape `ℕ → Bool`; state = (position, cost). -/
abbrev RProg (α : Type) := ReaderT (ℕ → Bool) (StateT (ℕ × ℕ) Option) α

/-- Add `k` to the cost counter of a randomized program. -/
def rcharge (k : ℕ) : RProg Unit := modify (fun s => (s.1, s.2 + k))

/-- Out of fuel. -/
def outOfFuel {α : Type} : RProg α := fun _ _ => none

/-- Run a deterministic charged program inside a randomized one (its cost is added). -/
def liftC {α : Type} (c : Counted α) : RProg α :=
  fun _ s => let r := c.run s.2; some (r.1, (s.1, r.2))

/-- Read the next fair bit from the tape, at cost `1`. -/
def coin : RProg Bool := fun ω s => some (ω s.1, (s.1 + 1, s.2 + 1))

/-- Read `k` fair bits and return the number they encode in binary, uniform on `[0, 2^k)`. -/
def drawBits : ℕ → RProg ℕ
  | 0 => pure 0
  | k + 1 => do
      let b ← coin
      let v ← drawBits k
      rcharge (opCost (2 * v) 1)
      pure (2 * v + if b then 1 else 0)

/-- A uniform element of `{0, …, N − 1}` by rejection sampling (Appendix B): draw
`⌈log₂ N⌉` fair bits and retry while the value is `≥ N`; at most `fuel` tries. For `N ≤ 1` the
answer `0` is returned without reading bits. -/
def uniformBelow : ℕ → ℕ → RProg ℕ
  | 0, _ => outOfFuel
  | fuel + 1, N => do
      if N ≤ 1 then
        pure 0
      else
        let v ← drawBits (Nat.clog 2 N)
        rcharge (opCost v N)
        if v < N then pure v else uniformBelow fuel N

/-- The program `P` (indexed by fuel) halts on the tape `ω`: some fuel suffices. -/
def halts {α : Type} (P : ℕ → RProg α) (ω : ℕ → Bool) : Prop :=
  ∃ N, ((P N).run ω).run (0, 0) ≠ none

open Classical in
/-- Output and cost of `P` on `ω` at the least sufficient fuel, `none` if `P` does not halt. -/
noncomputable def result {α : Type} (P : ℕ → RProg α) (ω : ℕ → Bool) : Option (α × ℕ) :=
  if h : halts P ω then
    (((P (Nat.find h)).run ω).run (0, 0)).map (fun r => (r.1, r.2.2))
  else none

/-- The output of `P` on `ω` (`none` if it does not halt). -/
noncomputable def outputOf {α : Type} (P : ℕ → RProg α) (ω : ℕ → Bool) : Option α :=
  (result P ω).map Prod.fst

/-- The cost of `P` on `ω`, `⊤` if it does not halt. -/
noncomputable def costOf {α : Type} (P : ℕ → RProg α) (ω : ℕ → Bool) : ℝ≥0∞ :=
  match result P ω with
  | some r => (r.2 : ℝ≥0∞)
  | none => ⊤

/-- The law of the tape: independent fair bits. -/
noncomputable def tape : Measure (ℕ → Bool) :=
  Measure.infinitePi (fun _ => (PMF.uniformOfFintype Bool).toMeasure)

end FlowLatRound


