-- Prove2me | Definitions.Def_ShapleyNV_PhatIn
-- name    : ShapleyNV_PhatIn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:51:56.164987+00:00
-- url     : https://prove2.me/theorems/eb1d64c8-5448-49f3-952e-13b4a3fede9c
-- title:
--   In-sample empirical distribution on $\widehat{\mathcal X}\times\mathcal Z$
-- statement:
--   Let $\widehat{\mathcal X} = \{\hat x_k : k \in [K]\}$ be the set of observed feature values. The empirical distribution $\widehat{\mathbb P}$ is supported on $\widehat{\mathcal X} \times \mathcal Z$, and this definition views it as a distribution on that smaller space:
--
--   $$
--   \widehat{\mathbb P} = \frac1n \sum_{k=1}^K \sum_{i=1}^{n_k} \delta_{(\hat x_k, \hat z_{ki})} \quad\text{on } \widehat{\mathcal X} \times \mathcal Z .
--   $$
--
--   It is the center of the Wasserstein ball in the in-sample problem $(\widehat{\mathrm P})$.
--
--   **Formalization Note** $\widehat{\mathcal X}$ is encoded by the index set $[K]$ through the injective map $k \mapsto \hat x_k$; the atom $(\hat x_k, \hat z_{ki})$ is written $(k, \hat z_{ki})$.
-- source:
--   Zhang, Yang, Gao, Optimal Robust Policy for Feature-Based Newsvendor (author manuscript, 2022-10-17), §2.2, p.5 (𝒳̂ := {x̂_k : k ∈ [K]}, P̂) and Theorem 1 (I), (P̂), p.6

import Mathlib
import Definitions.Def_ShapleyNV_Data

open MeasureTheory NNReal ENNReal

namespace ShapleyNV

/-- **In-sample copy of the empirical distribution**: `P̂` viewed as a distribution on `𝒳̂ × 𝒵`,
where `𝒳̂ = {x̂_k : k ∈ [K]}`.
Zhang, Yang, Gao, *Optimal Robust Policy for Feature-Based Newsvendor* (author manuscript, 2022-10-17), §2.2, p.5 (`𝒳̂ := {x̂_k : k ∈ [K]}`) and Theorem 1 (I), p.6 (the in-sample problem (P̂)
uses distributions on `𝒳̂ × 𝒵`).

**Formalization Note.** `𝒳̂` is encoded as `Fin K` through the injective map `k ↦ x̂_k`; the atom
`(x̂_k, ẑ_ki)` becomes `(k, ẑ_ki)`, with weight `1/n`. `Fin K` carries the discrete σ-algebra. -/
noncomputable def PhatIn {X : Type*} (D : Data X) : Measure (Fin D.K × ℝ≥0) :=
  ∑ k, ∑ i, (((∑ k', D.m k' : ℕ) : ℝ≥0∞)⁻¹) • Measure.dirac (k, D.zhat k i)

end ShapleyNV


