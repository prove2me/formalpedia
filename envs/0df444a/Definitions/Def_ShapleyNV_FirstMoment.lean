-- Prove2me | Definitions.Def_ShapleyNV_FirstMoment
-- name    : ShapleyNV_FirstMoment
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:51:08.721982+00:00
-- url     : https://prove2.me/theorems/2faf6211-9686-4a61-8f75-705fc1c94ba8
-- title:
--   Finite first moment with respect to a cost $c$
-- statement:
--   A measure $\mathbb P$ on $E$ has finite first moment with respect to the ground cost $c$ if
--
--   $$
--   \mathbb E_{\xi \sim \mathbb P}\big[c(\xi, \xi_0)\big] < \infty \quad \text{for some } \xi_0 \in E .
--   $$
--
--   With $c$ the cost $\|x - x'\| + |z - z'|$, the probability measures with this property form the set $\mathcal P_1(\mathcal X \times \mathcal Z)$ of the paper.
--
--   **Formalization Note** By the triangle inequality the choice of $\xi_0$ is irrelevant for the costs of this mission.
-- source:
--   Zhang, Yang, Gao, Optimal Robust Policy for Feature-Based Newsvendor (author manuscript, 2022-10-17), §2.2, p.5 (𝒫₁(𝒳 × 𝒵), distributions with finite first moment)

import Mathlib

open MeasureTheory NNReal ENNReal

namespace ShapleyNV

/-- **Finite first moment** with respect to a ground cost `c`: some point `ξ₀` has
`E_P[c(ξ, ξ₀)] < ∞`.
Zhang, Yang, Gao, *Optimal Robust Policy for Feature-Based Newsvendor* (author manuscript, 2022-10-17), §2.2, p.5: "Let 𝒫₁(𝒳 × 𝒵) be the set of probability distributions on 𝒳 × 𝒵 with finite first
moment."

**Formalization Note.** With `c` the sum cost `‖x − x₀‖ + |z − z₀|` this is the paper's finite first
moment; by the triangle inequality the choice of `ξ₀` does not matter. -/
def FirstMoment {α : Type*} [MeasurableSpace α] (c : α → α → ℝ) (P : Measure α) : Prop :=
  ∃ ξ₀ : α, ∫⁻ ξ, ENNReal.ofReal (c ξ ξ₀) ∂P < ⊤

end ShapleyNV


