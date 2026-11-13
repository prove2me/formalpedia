-- Prove2me | Definitions.Def_CountingLLL_RandomSpec
-- name    : CountingLLL_RandomSpec
-- status  : Definition
-- author  : @wcysai
-- created : 2026-11-13T04:57:55.408982+00:00
-- url     : https://prove2.me/theorems/3f01953a-01c0-47c7-86c3-b9936d8248f0
-- title:
--   Randomized counting and exact sampling specifications
-- statement:
--   Formal specifications for randomized counting and exact sampling as stated in Theorems 1.3 and 1.4, expressed for the fair-bit oracle RAM. The counting input encodes a dyadic tolerance eta=2^(-s), s>=1. For an arbitrary tolerance epsilon in (0,1), choosing s=max(1,ceil(log_2(1/epsilon))) gives eta <= epsilon and 2^s < 2/epsilon. A fixed program must satisfy a three-quarter success bound and explicit polynomial and polylogarithmic worst-case cost majorants on every tape. A sampling program must halt almost surely, return each satisfying assignment with probability 1/Z and every other assignment with probability zero, and satisfy the expected oracle and bit-time bounds. The exponents and constants are global, independent of the instance. These specifications instantiate the source computational model; they do not assert the existence of the programs.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovasz Local Lemma, STOC 2027 submission #442, Theorems 1.3 and 1.4 (PDF p. 4) and Section 2.5 (PDF p. 8), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_RandomRAM

set_option autoImplicit false

namespace CountingLLL.RandomRAM

open MeasureTheory
open scoped ENNReal

/-- Dyadic accuracy request represented by the positive input integer `s`. -/
noncomputable def epsilon (s : ℕ) : ℝ := ((2 : ℝ) ^ s)⁻¹

/-- Positive factors bounding the polynomial dependence on the local parameters. -/
noncomputable def localSize (Φ : CSP) : ℕ := Φ.kmax + Φ.Dmax + Φ.qmax + 1

/-- An explicit polylogarithmic base for the sampler. -/
noncomputable def sampleLogs (Φ : CSP) : ℕ :=
  1 + Nat.log2 (Φ.m + 1) + Nat.log2 (Φ.n + 1) + Nat.log2 (Φ.qmax + 1)

/-- The counting bound also allows a polynomial in log(1/ε), equal to `s` here. -/
noncomputable def countLogs (Φ : CSP) (s : ℕ) : ℕ := sampleLogs Φ + s

noncomputable def countingStart (Φ : CSP) (s : ℕ) : State :=
  initial (CountingLLL.DetCount.countingInput Φ s) (fun _ => 0)

noncomputable def sampleStart (Φ : CSP) : State :=
  initial (CountingLLL.DetCount.preprocessInput Φ) (fun _ => 0)

/-- Successful randomized counting outputs a rational with positive denominator and the stated
relative error. A divergent tape, malformed output, or failed approximation is outside this event. -/
noncomputable def countSuccess (Φ : CSP) (P : Program) (s : ℕ) : Set Tape :=
  {ω | Halts Φ P ω (countingStart Φ s) ∧
    ∃ a b : ℤ, (finalState Φ P ω (countingStart Φ s)).base.out = some (a, b) ∧
      0 < b ∧
      (1 - epsilon s) * Φ.ZPhi ≤ (a : ℝ) / b ∧
      (a : ℝ) / b ≤ (1 + epsilon s) * Φ.ZPhi}

/-- Concrete target for the counting theorem, with global constants and an explicit polynomial
majorant. Costs are bounded on every random tape. -/
noncomputable def IsApproxCounter (P : Program) (C e r : ℕ) : Prop :=
  ∀ (Φ : CSP), Φ.Standing → Φ.Condition11 → ∀ s : ℕ, 1 ≤ s →
    (∀ ω, Halts Φ P ω (countingStart Φ s) ∧
      oracleCost Φ P ω (countingStart Φ s) ≤
        (C * localSize Φ ^ e * (Φ.n * 2 ^ s) ^ 2 : ℕ) ∧
      timeCost Φ P ω (countingStart Φ s) ≤
        (C * localSize Φ ^ e * (Φ.n * 2 ^ s) ^ 2 * countLogs Φ s ^ r : ℕ)) ∧
    (3 / 4 : ℝ≥0∞) ≤ tapeMeasure (countSuccess Φ P s)

/-- Concrete target for the exact sampler. It terminates almost surely, outputs each satisfying
configuration with probability `1/Z`, and has the asserted expected costs. -/
noncomputable def IsExactSampler (P : Program) (C r : ℕ) : Prop := by
  classical
  exact ∀ (Φ : CSP), Φ.Standing → Φ.Condition11 →
    tapeMeasure {ω | Halts Φ P ω (sampleStart Φ)} = 1 ∧
    (∀ x : Φ.Config, outputProbability Φ P (sampleStart Φ) x =
      if Φ.SatAll Finset.univ x then (Φ.ZPhi : ℝ≥0∞)⁻¹ else 0) ∧
    expectedOracleCost Φ P (sampleStart Φ) ≤ (C * Φ.m : ℕ) ∧
    expectedTimeCost Φ P (sampleStart Φ) ≤
      (C * (Φ.n + Φ.kmax * Φ.m * Φ.Dmax ^ 2) * sampleLogs Φ ^ r : ℕ)

end CountingLLL.RandomRAM


