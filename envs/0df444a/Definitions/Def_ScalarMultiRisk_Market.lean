-- Prove2me | Definitions.Def_ScalarMultiRisk_Market
-- name    : ScalarMultiRisk_Market
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:16:13.786713+00:00
-- url     : https://prove2.me/theorems/d6f26911-1b32-4d79-831d-87de0530579f
-- title:
--   The market: random convex cones $K_t$ and the cone $\bar K$
-- statement:
--   A **market** with $d$ assets is the filtered probability space together with:
--
--   1. for each $t$, an $\mathcal F_t$-measurable random convex cone $K_t\subseteq\mathbb R^d$ (a solvency cone);
--   2. a convex cone $\bar K\subseteq\mathbb R^d$ with $\operatorname{int}\bar K\supseteq\mathbb R^d_+\setminus\{0\}$ and $K_T\supseteq\bar K$ almost surely.
--
--   The cones encode the trades allowed at each time, for example under bid-ask spreads.
--
--   **Formalization Note** A random convex cone is a map from $\Omega$ to convex cones containing $0$ whose graph is $\mathcal F_t\otimes\mathfrak B(\mathbb R^d)$-measurable. Closedness and $\mathbb R^d_+\subseteq K_t$ are not assumed.
-- source:
--   Feinstein, Rudloff, Scalar multivariate risk measures with a single eligible asset, arXiv:1807.10694v5, §3.1, p.7, and Assumption 3.3, p.8

import Mathlib
import Definitions.Def_ScalarMultiRisk_FilteredSpace

open MeasureTheory

namespace ScalarMultiRisk

/-- **The market with solvency cones.** arXiv:1807.10694v5, §3.1, p.7, and Assumption 3.3, p.8:
the filtered probability space with `d` assets, `F_s`-measurable random convex cones `K_s`
(the solvency cones `(K_t)_{t=0}^T`), and a convex cone `K̄ ⊆ ℝ^d` with
`int K̄ ⊇ ℝ^d₊ \ {0}` and `K_T ⊇ K̄` almost surely.

**Formalization Note.** A random convex cone is a map from `Ω` to convex cones containing `0`
(`PointedCone`) whose graph is `F_s ⊗ 𝔅(ℝ^d)`-measurable, the standard notion (Molchanov).
`0 ∈ K_s` is what makes `0 ∈ 𝕂_t`, which the paper uses after (3.1). No closedness and no
inclusion `ℝ^d₊ ⊆ K_s` is assumed beyond the `K̄` condition. -/
structure Market (Ω : Type*) [MeasurableSpace Ω] (T d : ℕ) extends FilteredSpace Ω T where
  /-- The random convex cones `K_t`, `t = 0, …, T`. -/
  K : Fin (T + 1) → Ω → PointedCone ℝ (Fin d → ℝ)
  /-- `K_s` is `F_s`-measurable: its graph is `F_s ⊗ 𝔅(ℝ^d)`-measurable. -/
  K_measurable : ∀ s, MeasurableSet[MeasurableSpace.prod (F s) inferInstance]
    {p : Ω × (Fin d → ℝ) | p.2 ∈ K s p.1}
  /-- The deterministic convex cone `K̄`. -/
  Kbar : PointedCone ℝ (Fin d → ℝ)
  /-- `int K̄ ⊇ ℝ^d₊ \ {0}`. -/
  Kbar_interior : {x : Fin d → ℝ | 0 ≤ x} \ {0} ⊆ interior (Kbar : Set (Fin d → ℝ))
  /-- `K_T ⊇ K̄` almost surely. -/
  K_last_ge : ∀ᵐ ω ∂P, ∀ x ∈ Kbar, x ∈ K (Fin.last T) ω

end ScalarMultiRisk


