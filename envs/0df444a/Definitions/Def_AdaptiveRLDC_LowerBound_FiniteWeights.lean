-- Prove2me | Definitions.Def_AdaptiveRLDC_LowerBound_FiniteWeights
-- name    : AdaptiveRLDC_LowerBound_FiniteWeights
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T14:55:22.692753+00:00
-- url     : https://prove2.me/theorems/420ad1a2-54f4-415d-8db5-3ad3db32ae02
-- title:
--   Finite weights and independent binary sampling
-- statement:
--   A sub-distribution on a finite set $A$ has arbitrary real weights $\mu(a)\ge0$ with $\sum_a\mu(a)\le1$. Probability laws of mass one use the published finite-distribution predicate. Expectations and event masses are the corresponding finite sums.
--
--   For independent binary coordinates with parameters $\pi_i\in[0,1]$, the exact joint weight at $x$ is
--   $$\prod_i \pi_i^{x_i}(1-\pi_i)^{1-x_i}.$$
--   The same product gives the sampling law on subsets $W$, with common parameter $p$. Indicator vectors, binary words and finite coordinate sets provide the shared interface. Endpoint probabilities and empty products retain their usual meanings. These objects support both concentration and observable sampling without measure-theoretic integrability defaults.
-- source:
--   Guy Goldberg, Tom Gur, Sidhant Saraogi, Lower Bounds for Adaptive Relaxed Locally Decodable Codes via the Capped Horvitz–Thompson Estimator, STOC 2027 submission #1071 (October 2026), §3.1; independent binary vectors in §4.4; Definition 5.2, printed p.13, PDF p.14; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1071.pdf; sha256 fc1b12e269801cef0033faea9f18d9873b62d5b18dbd21242a4daefc43048a5b. Title-page date November 3, 2026; submission status does not assert acceptance. Exact per-concept locations: §3.1 printed p.13/PDF p.14; §4.4 printed p.21/PDF p.22; Definition 5.2 printed p.27/PDF p.28.

import Mathlib
import Definitions.Def_FuchsVdGraaf_IsProbDist

open scoped BigOperators
noncomputable section

namespace AdaptiveRLDC.LowerBound

open Classical

/-- §3.1: finite real sub-probability weights; no rationality or uniformity restriction. -/
def IsSubdistribution {A : Type} [Fintype A] (μ : A → ℝ) : Prop :=
  (∀ a, 0 ≤ μ a) ∧ ∑ a, μ a ≤ 1

/-- Finite expectation with respect to the actual weights. -/
def mean {A : Type} [Fintype A] (μ : A → ℝ) (f : A → ℝ) : ℝ :=
  ∑ a, μ a * f a

/-- Finite event mass (a probability when the weights have total mass one). -/
def eventMass {A : Type} [Fintype A] (μ : A → ℝ) (E : A → Prop) : ℝ :=
  ∑ a, if E a then μ a else 0

abbrev Cube (n : ℕ) := Fin n → Bool
abbrev Sets (n : ℕ) := Finset (Fin n)

/-- Independent binary coordinates, allowing distinct probabilities and deterministic coordinates. -/
def productWeight {n : ℕ} (π : Fin n → ℝ) (x : Cube n) : ℝ :=
  ∏ i, if x i then π i else 1 - π i

/-- The exact law of a binomially sampled coordinate set, including p=1. -/
def sampleWeight {n : ℕ} (p : ℝ) (W : Sets n) : ℝ :=
  ∏ i : Fin n, if i ∈ W then p else 1 - p

/-- Indicator of the sampled set. -/
def indicator {n : ℕ} (W : Sets n) : Cube n := fun i => decide (i ∈ W)

end AdaptiveRLDC.LowerBound


