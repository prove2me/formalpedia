-- Prove2me | Definitions.Def_SweepingDesing_IsPAC
-- name    : SweepingDesing_IsPAC
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:15:44.907+00:00
-- url     : https://prove2.me/theorems/ff1870fc-0a09-4991-a560-fdff012465d3
-- title:
--   §2.1 — piecewise absolutely continuous curves
-- statement:
--   A curve $\gamma:I\to\mathbb R^n$ is **piecewise absolutely continuous** on the interval $I$ if its possible discontinuities are contained in a closed countable set $D\subset\mathbb R$ and $\gamma$ is absolutely continuous on each interval $J_i$ of the open set $I\setminus D$.
--
--   Such curves may jump, but only on a countable closed set; their length counts only the absolutely continuous motion.
--
--   **Formalization Note** "absolutely continuous on each $J_i$" is absolute continuity on every compact interval inside $I\setminus D$.
-- source:
--   Daniilidis, Tapia-García, Desingularization of the Sweeping Process Mapping, arXiv:2110.08686v1, §2.1, p.4

import Mathlib
import Definitions.Def_SweepingDesing_IsLocallyAC
open Filter Topology MeasureTheory Set
open scoped ENNReal

namespace SweepingDesing

/-- Daniilidis, Tapia-García, Desingularization of the Sweeping Process Mapping, arXiv:2110.08686v1, §2.1, p.4: `γ` is *piecewise absolutely continuous* on `I`: its possible
discontinuities are contained in a closed countable set `D` and it is absolutely continuous on
each interval `J_i` of `I ∖ D`.

**Formalization Note** "absolutely continuous on each `J_i`" is encoded as absolute continuity on
every compact interval contained in `I ∖ D` (each such interval lies in one `J_i`), the reading
of `IsLocallyAC`. -/
def IsPAC {n : ℕ} (γ : ℝ → EuclideanSpace ℝ (Fin n)) (I : Set ℝ) : Prop :=
  ∃ D : Set ℝ, D.Countable ∧ IsClosed D ∧ IsLocallyAC γ (I \ D)

end SweepingDesing


