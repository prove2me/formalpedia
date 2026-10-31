-- Prove2me | Definitions.Def_SweepingDesing_ContinuityAt
-- name    : SweepingDesing_ContinuityAt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:15:51.501413+00:00
-- url     : https://prove2.me/theorems/c123cc56-86ca-40eb-9987-7cc89a24054a
-- title:
--   Assumption (A3) — continuity of $H_S$ after $\bar t$
-- statement:
--   The map $S$ satisfies the **continuity assumption (A3)** at $\bar t\in\operatorname{dom}(S)$ with $\bar t<T=\sup\operatorname{dom}(S)$ if there is $\delta>0$ such that the set-valued map $H_S(t)=\partial\mathcal S\cap(\{t\}\times\mathbb R^n)$ is continuous for the Pompeiu–Hausdorff metric on $(\bar t,\bar t+\delta)$; it may be discontinuous at $\bar t$ itself.
--
--   It controls how the boundaries of the moving sets evolve when the sets $S(t)$ are neither monotone nor convex.
--
--   **Formalization Note** The Pompeiu–Hausdorff distance is Mathlib's `Metric.hausdorffEDist` on $\mathbb R\times\mathbb R^n$.
-- source:
--   Daniilidis, Tapia-García, Desingularization of the Sweeping Process Mapping, arXiv:2110.08686v1, Assumption (A3), p.8

import Mathlib
import Definitions.Def_SweepingDesing_boundarySlice
open Filter Topology MeasureTheory Set
open scoped ENNReal

namespace SweepingDesing

/-- Daniilidis, Tapia-García, Desingularization of the Sweeping Process Mapping, arXiv:2110.08686v1, §3.1, Assumption (A3), p.8: `S` satisfies the *continuity assumption* at
`t̄ ∈ dom(S)` with `t̄ < T` if there exists `δ > 0` such that `H_S` is continuous for the
Pompeiu–Hausdorff metric on `(t̄, t̄ + δ)` (it may be discontinuous at `t̄`).

**Formalization Note** The Pompeiu–Hausdorff distance is Mathlib's `Metric.hausdorffEDist` on
`ℝ × ℝⁿ` (sup of the two norms; an equivalent metric gives the same continuity). Continuity on the
open interval is continuity at each of its points. -/
def ContinuityAt {n : ℕ} (S : ℝ → Set (EuclideanSpace ℝ (Fin n))) (tbar : ℝ) : Prop :=
  (S tbar).Nonempty ∧ (∃ s, tbar < s ∧ (S s).Nonempty) ∧
    ∃ δ > (0 : ℝ), ∀ s ∈ Ioo tbar (tbar + δ),
      Tendsto (fun s' => Metric.hausdorffEDist (boundarySlice S s') (boundarySlice S s)) (𝓝 s) (𝓝 0)

end SweepingDesing


