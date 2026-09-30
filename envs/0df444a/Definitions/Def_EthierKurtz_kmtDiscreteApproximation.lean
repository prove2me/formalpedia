-- Prove2me | Definitions.Def_EthierKurtz_kmtDiscreteApproximation
-- name    : EthierKurtz_kmtDiscreteApproximation
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-09-29T20:21:50.548139+00:00
-- url     : https://prove2.me/theorems/a10e5492-0fb8-4cd8-b85c-03699ae1cd4c
-- title:
--   Discrete KMT coupling with Gaussian increments
-- statement:
--   A law has a discrete KMT approximation if it admits a joint coupling of an iid sequence with that law and an iid standard Gaussian sequence, where the maximal difference of their partial sums through n has a strict exponential tail above a logarithmic threshold. The two sequences may depend on one another.
-- source:
--   Ethier and Kurtz, Markov Processes: Characterization and Convergence, Chapter 7, Section 5, Theorem 5.1, p. 356; discrete integer-time formulation of the KMT coupling.

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace EthierKurtz

/-- A KMT coupling at integer times, using independent standard Gaussian increments.
The two increment sequences may be dependent on each other. -/
def kmtDiscreteApproximation (μ : ProbabilityMeasure ℝ) : Prop :=
  ∃ Q : ProbabilityMeasure ((ℕ → ℝ) × (ℕ → ℝ)),
    iIndepFun (fun (i : ℕ) (z : (ℕ → ℝ) × (ℕ → ℝ)) => z.1 i)
      (Q : Measure ((ℕ → ℝ) × (ℕ → ℝ))) ∧
    (∀ i : ℕ, HasLaw (fun (z : (ℕ → ℝ) × (ℕ → ℝ)) => z.1 i)
      (μ : Measure ℝ) (Q : Measure ((ℕ → ℝ) × (ℕ → ℝ)))) ∧
    iIndepFun (fun (i : ℕ) (z : (ℕ → ℝ) × (ℕ → ℝ)) => z.2 i)
      (Q : Measure ((ℕ → ℝ) × (ℕ → ℝ))) ∧
    (∀ i : ℕ, HasLaw (fun (z : (ℕ → ℝ) × (ℕ → ℝ)) => z.2 i)
      (gaussianReal 0 1) (Q : Measure ((ℕ → ℝ) × (ℕ → ℝ)))) ∧
    ∃ C K lam : ℝ, 0 < C ∧ 0 < K ∧ 0 < lam ∧
      ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ, 0 < x →
        (Q : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
          {z | ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧
            C * Real.log (n : ℝ) + x <
              |(∑ i ∈ Finset.range k, z.1 i) -
                (∑ i ∈ Finset.range k, z.2 i)|} <
          ENNReal.ofReal (K * Real.exp (-lam * x))

end EthierKurtz


