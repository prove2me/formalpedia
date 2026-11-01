-- Prove2me | Definitions.Def_SupermodDRO_scenarioSet
-- name    : SupermodDRO_scenarioSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:30:57.499453+00:00
-- url     : https://prove2.me/theorems/0ccf072a-58ad-4992-9768-608198f9b760
-- title:
--   Ambiguity set $\mathcal F^k$ of a fixed scenario, (4)
-- statement:
--   Fix a scenario $k$ with mean vector $\mu^k\in\mathbb R^n$, mean-absolute-deviation bounds $\delta^k\in\mathbb R^n$ and support bounds $\underline z^k,\overline z^k\in\mathbb R^n$. The ambiguity set of the scenario is
--   $$
--   \mathcal F^k=\Bigl\{\mathbb P^k \;:\; \mathbb E_{\mathbb P^k}[\tilde z]=\mu^k,\ \ \mathbb E_{\mathbb P^k}\bigl[|\tilde z_i-\mu_i^k|\bigr]\le\delta_i^k\ \ \forall i\in[n],\ \ \mathbb P^k(\underline z^k\le\tilde z\le\overline z^k)=1\Bigr\},
--   $$
--   the set of Borel probability distributions on $\mathbb R^n$ with the given mean, mean absolute deviations at most $\delta^k$ and support in the box $[\underline z^k,\overline z^k]$.
--
--   **Formalization Note** $\mathbb R^n$ is the space of functions on $\{0,\dots,n-1\}$ with the product (Borel) σ-algebra. Because the support condition holds, every integrand in the moment conditions is bounded almost surely, so the integrals are the usual expectations.
-- source:
--   Long, Qi & Zhang, Supermodularity in Two-Stage Distributionally Robust Optimization, author manuscript (June 2022; PDF sha256 9e6840ad…5b09160b02b5e47), §2.2, (4), p.7

import Mathlib

open MeasureTheory

namespace SupermodDRO

/-- **The ambiguity set `𝓕ᵏ` of a fixed scenario, (4).** Long, Qi & Zhang, *Supermodularity in
Two-Stage Distributionally Robust Optimization*, author manuscript (June 2022), §2.2, (4), p.7:
"𝓕ᵏ = {ℙᵏ | E_{ℙᵏ}[z̃] = µᵏ, E_{ℙᵏ}[|z̃ᵢ − µᵢᵏ|] ≤ δᵢᵏ ∀ i ∈ [n], ℙᵏ(z̲ᵏ ≤ z̃ ≤ z̄ᵏ) = 1}".

For vectors `μ, δ, zl, zu ∈ ℝⁿ` (the paper's `µᵏ, δᵏ, z̲ᵏ, z̄ᵏ`), the set of Borel probability
measures `P` on `ℝⁿ` with `P(zl ≤ z ≤ zu) = 1`, mean `μ` (coordinatewise) and mean absolute
deviation of the `i`-th coordinate at most `δ i` for every `i`.

**Formalization Note** `ℝⁿ` is `Fin n → ℝ` with its product (= Borel) σ-algebra; coordinates are
0-based. The support condition comes first: under it every integrand `z ↦ z i` and
`z ↦ |z i − μ i|` is bounded `P`-a.e., so the Bochner integrals are the honest expectations. -/
def scenarioSet {n : ℕ} (μ δ zl zu : Fin n → ℝ) : Set (Measure (Fin n → ℝ)) :=
  {P | IsProbabilityMeasure P ∧ P (Set.Icc zl zu) = 1 ∧
    (∀ i, ∫ z, z i ∂P = μ i) ∧ (∀ i, ∫ z, |z i - μ i| ∂P ≤ δ i)}

end SupermodDRO


