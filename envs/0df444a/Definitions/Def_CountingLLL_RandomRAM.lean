-- Prove2me | Definitions.Def_CountingLLL_RandomRAM
-- name    : CountingLLL_RandomRAM
-- status  : Definition
-- author  : @wcysai
-- created : 2026-11-13T04:55:56.420342+00:00
-- url     : https://prove2.me/theorems/d8268571-793b-4087-9c91-cf4a3ac3f387
-- title:
--   Fair-bit oracle RAM for counting and sampling LLL
-- statement:
--   A concrete extension of the deterministic CSP oracle RAM by independent unbiased random bits. Programs are finite instruction lists; each random-bit instruction consumes the next bit, costs one unit of bit time, and makes no evaluation-oracle call. The tape has the countable fair-product distribution. Execution records first-halt state, oracle calls, and bit time, with infinite cost on nontermination. A sampler returns a pointer and length identifying its assignment in memory. This is an explicit implementation of the abstract bit-cost model, intended to state and verify randomized counting and sampling algorithms; it does not assert their existence.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 submission #442, §2.5 (PDF p. 8), Theorems 1.3–1.4 (PDF p. 4), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_DetCount_Machine

set_option autoImplicit false

namespace CountingLLL.RandomRAM

open MeasureTheory
open scoped ENNReal

abbrev CSP := CountingLLL.DetCount.CSP
abbrev Base := CountingLLL.DetCount.Instr
abbrev BaseState := CountingLLL.DetCount.State

/-- An instruction of the bit-cost CSP machine, or a fresh unbiased bit. A random-bit
instruction costs one unit of time and no oracle calls. -/
inductive Instr where
  | base (i : Base)
  | bit (d : ℕ)
  deriving DecidableEq

abbrev Program := List Instr
abbrev Tape := ℕ → Bool

/-- Fair product measure on the countably infinite stream of independent random bits. -/
noncomputable def tapeMeasure : Measure Tape :=
  Measure.infinitePi (fun _ : ℕ => (1 / 2 : ℝ≥0∞) • Measure.dirac false +
    (1 / 2 : ℝ≥0∞) • Measure.dirac true)

structure State where
  base : BaseState
  used : ℕ

/-- Instruction projection used for the deterministic machine. The placeholder for `bit`
is never executed: the random instruction is handled before calling the base transition. -/
def baseProgram (P : Program) : CountingLLL.DetCount.Program :=
  P.map fun ins => match ins with
    | .base i => i
    | .bit _ => .halt 0 0

/-- One step driven by the next unused tape bit. Base instructions retain the bit and oracle
accounting of the deterministic machine. Halted or out-of-program states stutter. -/
noncomputable def step (Φ : CSP) (P : Program) (ω : Tape) (s : State) : State :=
  match s.base.out with
  | some _ => s
  | none =>
    match P[s.base.pc]? with
    | none => s
    | some (.base _) => { s with base := CountingLLL.DetCount.step Φ (baseProgram P) s.base }
    | some (.bit d) =>
      { base := { s.base with
          reg := Function.update s.base.reg d (if ω s.used then 1 else 0)
          pc := s.base.pc + 1
          time := s.base.time + 1
          steps := s.base.steps + 1 },
        used := s.used + 1 }

noncomputable def run (Φ : CSP) (P : Program) (ω : Tape) (s : State) (t : ℕ) : State :=
  (step Φ P ω)^[t] s

def initial (M : ℤ → ℤ) (R : ℕ → ℤ) : State :=
  ⟨CountingLLL.DetCount.initState M R, 0⟩

def Halts (Φ : CSP) (P : Program) (ω : Tape) (s : State) : Prop :=
  ∃ t : ℕ, (run Φ P ω s t).base.out.isSome

/-- The state at the first halt; its value on a nonterminating tape is the initial state and
must only be interpreted under a separate halting assumption. -/
noncomputable def finalState (Φ : CSP) (P : Program) (ω : Tape) (s : State) : State := by
  classical
  exact if h : Halts Φ P ω s then run Φ P ω s (Nat.find h) else s

/-- Cost is infinite on nonterminating tapes. This rules out treating divergence as zero cost. -/
noncomputable def oracleCost (Φ : CSP) (P : Program) (ω : Tape) (s : State) : ℝ≥0∞ := by
  classical
  exact if Halts Φ P ω s then ((finalState Φ P ω s).base.oracle : ℝ≥0∞) else ⊤

noncomputable def timeCost (Φ : CSP) (P : Program) (ω : Tape) (s : State) : ℝ≥0∞ := by
  classical
  exact if Halts Φ P ω s then ((finalState Φ P ω s).base.time : ℝ≥0∞) else ⊤

noncomputable def expectedOracleCost (Φ : CSP) (P : Program) (s : State) : ℝ≥0∞ :=
  ∫⁻ ω, oracleCost Φ P ω s ∂tapeMeasure

noncomputable def expectedTimeCost (Φ : CSP) (P : Program) (s : State) : ℝ≥0∞ :=
  ∫⁻ ω, timeCost Φ P ω s ∂tapeMeasure

/-- A sampler outputs a pointer and length in its halt pair. The pointed-to memory words
must equal the domain indices of the full assignment, in variable-index order. -/
def OutputConfig (Φ : CSP) (s : State) (x : Φ.Config) : Prop :=
  ∃ a len, s.base.out = some (a, len) ∧ len = Φ.n ∧
    ∀ v : Fin Φ.n, s.base.mem (a + v.val) = (x v).val

/-- Probability of returning this particular assignment. -/
noncomputable def outputProbability (Φ : CSP) (P : Program) (s : State) (x : Φ.Config) : ℝ≥0∞ :=
  tapeMeasure {ω | Halts Φ P ω s ∧ OutputConfig Φ (finalState Φ P ω s) x}

end CountingLLL.RandomRAM


