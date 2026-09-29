-- Prove2me | Definitions.Def_EthierKurtz_kmtApproximation
-- name    : EthierKurtz_kmtApproximation
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-09-26T20:09:38.345437+00:00
-- url     : https://prove2.me/theorems/9da6cee2-2042-4f58-a30c-1375bf8b8759
-- title:
--   KMT approximation property for a real law
-- statement:
--   The KMT coupling conclusion for a real probability law, with drift equal to its mean and Brownian scale equal to its standard deviation.
-- source:
--   Ethier and Kurtz, Markov Processes: Characterization and Convergence, Chapter 7, Section 5, Theorem 5.1 and equation (5.1), p. 356.

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace EthierKurtz

/-- The KMT coupling conclusion for a real probability law, with its own mean and variance. -/
def kmtApproximation (μ : ProbabilityMeasure Real) : Prop :=
  ∃ Q : ProbabilityMeasure ((ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b}),
    iIndepFun (fun (i : ℕ) (z : (ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b}) => z.1 i)
      (Q : Measure ((ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b})) ∧
    (∀ i : ℕ, HasLaw (fun (z : (ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b}) => z.1 i)
      (μ : Measure ℝ) (Q : Measure ((ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b}))) ∧
    IsBrownianReal (fun t (z : (ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b}) => z.2.val t)
      (Q : Measure ((ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b})) ∧
    ∃ C K lam : ℝ, 0 < C ∧ 0 < K ∧ 0 < lam ∧
      let m := ∫ x : ℝ, x ∂(μ : Measure ℝ)
      let σ := Real.sqrt (variance (fun x : ℝ => x) (μ : Measure ℝ))
      let W := fun (t : ℝ≥0)
          (z : (ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b}) =>
        m * (t : ℝ) + σ * z.2.val t
      ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ, 0 < x →
        (Q : Measure ((ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b}))
          {z | ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧
            C * Real.log (n : ℝ) + x <
              |(∑ i ∈ Finset.range k, z.1 i) - W (k : ℝ≥0) z|} <
          ENNReal.ofReal (K * Real.exp (-lam * x))

end EthierKurtz


