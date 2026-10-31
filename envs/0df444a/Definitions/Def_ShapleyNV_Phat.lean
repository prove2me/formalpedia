-- Prove2me | Definitions.Def_ShapleyNV_Phat
-- name    : ShapleyNV_Phat
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:51:56.905423+00:00
-- url     : https://prove2.me/theorems/cded9bf4-eab0-4543-bbfd-012eae379ea4
-- title:
--   Empirical distribution $\widehat{\mathbb P} = \frac1n\sum_{k,i}\delta_{(\hat x_k,\hat z_{ki})}$
-- statement:
--   The empirical distribution of the data on $\mathcal X \times \mathcal Z$ is
--
--   $$
--   \widehat{\mathbb P} = \frac1n \sum_{k=1}^K \sum_{i=1}^{n_k} \delta_{(\hat x_k, \hat z_{ki})},
--   $$
--
--   the uniform distribution over the $n$ observations (repeated observations count with multiplicity).
--
--   It is the center of the Wasserstein ball in the robust problem (P).
--
--   **Formalization Note** $\mathcal Z = \mathbb R_+$ is the type of nonnegative reals. Since every group is nonempty, $n \ge 1$ and $\widehat{\mathbb P}$ is a probability measure.
-- source:
--   Zhang, Yang, Gao, Optimal Robust Policy for Feature-Based Newsvendor (author manuscript, 2022-10-17), §2.2, display defining P̂, p.5

import Mathlib
import Definitions.Def_ShapleyNV_Data

open MeasureTheory NNReal ENNReal

namespace ShapleyNV

/-- **Empirical distribution** `P̂ = (1/n) Σ_k Σ_i δ_(x̂_k, ẑ_ki)` on `𝒳 × 𝒵`.
Zhang, Yang, Gao, *Optimal Robust Policy for Feature-Based Newsvendor* (author manuscript, 2022-10-17), §2.2, display defining P̂, p.5.

**Formalization Note.** `𝒵 = ℝ₊` is `ℝ≥0`; `n = Σ_k n_k` is `Σ k, D.m k`, which is positive
because every group is nonempty, so `P̂` is a probability measure. -/
noncomputable def Phat {X : Type*} [MeasurableSpace X] (D : Data X) : Measure (X × ℝ≥0) :=
  ∑ k, ∑ i, (((∑ k', D.m k' : ℕ) : ℝ≥0∞)⁻¹) • Measure.dirac (D.xhat k, D.zhat k i)

end ShapleyNV


