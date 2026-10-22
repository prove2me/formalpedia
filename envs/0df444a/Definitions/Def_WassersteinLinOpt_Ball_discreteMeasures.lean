-- Prove2me | Definitions.Def_WassersteinLinOpt_Ball_discreteMeasures
-- name    : WassersteinLinOpt_Ball_discreteMeasures
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T16:01:47.503545+00:00
-- url     : https://prove2.me/theorems/834e7f91-e0e0-4abb-ab50-9d01175b1354
-- title:
--   Discrete measures $\mathcal D_m(Z)$ on at most $m$ points
-- statement:
--   For a measurable space $Z$ and $m\in\mathbb N$, $\mathcal D_m(Z)$ is the set of non-negative discrete measures supported on at most $m$ points of $Z$:
--
--   $$\mathcal D_m(Z)=\Big\{\sum_{z\in S} w_z\,\delta_{z}: S\subseteq Z \text{ finite},\ |S|\le m,\ w_z\ge 0\Big\}.$$
--
--   **Formalization Note.** The support is a `Finset` `s` with `s.card ≤ m` and the weights are finite, non-negative (`ℝ≥0`); weights may vanish. This is exactly "at most $m$ points": the zero measure lies in $\mathcal D_m(Z)$ for every $m$, also when $Z$ is empty (an encoding by `Fin m → Z` would make $\mathcal D_m(\emptyset)=\emptyset$ for $m\ge1$ and falsify Proposition 1 on an empty $Z$).
-- source:
--   Yue, Kuhn & Wiesemann, On linear optimization over Wasserstein balls, Math. Program. 195 (2022) 1107–1122, https://doi.org/10.1007/s10107-021-01673-8, p. 1116 (problem (9)) and p. 1121 (Proposition 1)

import Mathlib

open MeasureTheory
open scoped ENNReal NNReal

namespace WassersteinLinOpt.Ball

/-- `𝒟_m(Z)` (p. 1116 and p. 1121): the non-negative discrete measures supported on at most
`m` points of `Z`, i.e. `∑_{z ∈ s} w_z δ_z` for a finite set `s ⊆ Z` of at most `m` points and
finite weights `w_z ≥ 0`. The support set may have fewer than `m` points, so the zero measure
belongs to `𝒟_m(Z)` for every `m`, also when `Z` is empty. -/
def discreteMeasures {Z : Type*} [MeasurableSpace Z] (m : ℕ) : Set (Measure Z) :=
  {γ | ∃ (s : Finset Z) (w : Z → ℝ≥0), s.card ≤ m ∧
      γ = ∑ z ∈ s, (w z : ℝ≥0∞) • Measure.dirac z}

end WassersteinLinOpt.Ball


