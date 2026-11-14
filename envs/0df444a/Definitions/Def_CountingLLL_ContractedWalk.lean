-- Prove2me | Definitions.Def_CountingLLL_ContractedWalk
-- name    : CountingLLL_ContractedWalk
-- status  : Definition
-- author  : @wcysai
-- created : 2026-11-13T07:20:55.683767+00:00
-- url     : https://prove2.me/theorems/215dc025-ada5-4ee1-b9a7-d9a88b706162
-- title:
--   Contracted reciprocal-test random walk
-- statement:
--   An absorbed random walk for the analysis of Algorithm 6. From each positive level it moves down by one with probability $1-\theta$ and up by two with probability $\theta$; zero is absorbing. Independent increments drive the walk, while extended-valued variables count the number of changes and increases before absorption. This is the paper’s contracted walk after suppressing self-loops and early return tests; coupling it to the full machine remains to be established.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 #442, proof of Lemma 6.5, PDF p. 27, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Mathlib

set_option autoImplicit false

/-! The contracted walk used in the proof of #442 Lemma 6.5. The upward step
has probability θ; the downward step has probability 1−θ. Zero is absorbing.
The model suppresses early return checks and self-loops exactly as in the proof.
It is an abstract IID walk; its coupling to Algorithm 6 is a separate theorem. -/
namespace CountingLLL.ContractedWalk

open MeasureTheory
open scoped ENNReal

abbrev Tape := ℕ → Bool

noncomputable def bitLaw (θ : ℝ≥0∞) : Measure Bool :=
  (1-θ) • Measure.dirac false + θ • Measure.dirac true

noncomputable def tapeLaw (θ : ℝ≥0∞) : Measure Tape :=
  Measure.infinitePi (fun _ : ℕ => bitLaw θ)

def level (ω : Tape) (start : ℕ) : ℕ → ℕ
  | 0 => start
  | t+1 =>
    let i := level ω start t
    if i = 0 then 0 else if ω t then i+2 else i-1

/-- Total number of nonabsorbed steps; it is infinite for a nonabsorbing path. -/
noncomputable def changes (ω : Tape) (start : ℕ) : ℝ≥0∞ :=
  ∑' t : ℕ, (if level ω start t = 0 then 0 else 1)

/-- Total number of upward steps before absorption. -/
noncomputable def increases (ω : Tape) (start : ℕ) : ℝ≥0∞ :=
  ∑' t : ℕ, (if level ω start t ≠ 0 ∧ ω t = true then 1 else 0)

noncomputable def expectedChanges (θ : ℝ≥0∞) (start : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, changes ω start ∂tapeLaw θ

end CountingLLL.ContractedWalk


