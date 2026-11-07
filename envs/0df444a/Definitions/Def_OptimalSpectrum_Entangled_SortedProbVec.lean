-- Prove2me | Definitions.Def_OptimalSpectrum_Entangled_SortedProbVec
-- name    : OptimalSpectrum_Entangled_SortedProbVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:04.680253+00:00
-- url     : https://prove2.me/theorems/34581f21-2957-416f-8f05-6090166e3261
-- title:
--   Sorted probability vectors $\{x\in\mathbb R^d: x_1\ge\cdots\ge x_d\ge0,\ \sum_i x_i=1\}$
-- statement:
--   The set of **sorted probability vectors** of length $d$ is
--
--   $$\Delta^{\downarrow}_d=\Big\{x\in\mathbb R^d:\ x_1\ge x_2\ge\cdots\ge x_d,\ \ x_i\ge0,\ \ \sum_{i=1}^d x_i=1\Big\},$$
--
--   with the Borel $\sigma$-algebra it inherits from $\mathbb R^d$. It is the output space of a spectrum estimation algorithm in Theorem 1.1, so the conclusion "outputs a sorted probability vector" is part of the type of the measurement.
-- source:
--   Bakshi, Singh, Tan, Optimal spectrum estimation, arXiv:2609.30171, Theorem 1.1, p. 1 (PDF p. 3)

import Mathlib

namespace OptimalSpectrum.Entangled

/-- **Sorted probability vectors on `d` outcomes.**
Bakshi, Singh, Tan, *Optimal spectrum estimation*, arXiv:2609.30171, §1 (Theorem 1.1), printed p. 1 (PDF p. 3): the algorithm "outputs a sorted probability
vector α̂".

`SortedProbVec d` is the set of `x ∈ ℝ^d` with `x₁ ≥ ⋯ ≥ x_d`, `xᵢ ≥ 0` and `∑ xᵢ = 1`, carrying the
subspace σ-algebra of the Borel σ-algebra of `ℝ^d` (the product σ-algebra on `Fin d → ℝ`).

**Formalization Note.** "Sorted" is nonincreasing, the order of `spec`. It is an `abbrev` so that the
subtype's measurable-space instance is found. -/
abbrev SortedProbVec (d : ℕ) : Type :=
  {x : Fin d → ℝ // Antitone x ∧ (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}

end OptimalSpectrum.Entangled


