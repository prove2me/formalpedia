-- Prove2me | Definitions.Def_MaxWeightInstab_subcriticalRegion
-- name    : MaxWeightInstab_subcriticalRegion
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:14:23.392977+00:00
-- url     : https://prove2.me/theorems/c6b1be3f-57b6-4528-ab6b-d43a6838df32
-- title:
--   Subcritical region $\mathcal C$
-- statement:
--   The **subcritical region** $\mathcal C\subset\mathbb R^{2J+2}$ is the interior of the convex hull $\langle\mathcal S\rangle$ of the feasible schedules (3). A policy is maximally stable if the queue process is positive recurrent whenever $\boldsymbol\rho\in\mathcal C$.
--
--   **Formalization Note** $\mathcal S$ is finite, so its convex hull is closed; the interior is taken in $\mathbb R^{2J+2}$.
-- source:
--   Bramson, D'Auria, Walton, Stability and Instability of the MaxWeight Policy, arXiv:1909.10825v2, p.6 (with (3), p.3)

import Mathlib
import Definitions.Def_MaxWeightInstab_IsSchedule

namespace MaxWeightInstab

/-- The subcritical region `𝒞` of the network of Figure 1 (Bramson, D'Auria & Walton, *Stability and Instability of the MaxWeight Policy*, arXiv:1909.10825v2, p.6): "`< 𝒮 >` denotes the convex
closure of the set `𝒮`. The subcritical region `𝒞` denotes the interior of the set `< 𝒮 >`", with
`𝒮` given by (3). The schedules are cast to `ℝ^{2J+2}`.

**Formalization Note.** `𝒮` is finite, so its convex hull is closed and equals its closed convex
hull. The interior is taken in the product topology of `Queue J → ℝ`. -/
def subcriticalRegion (J ν : ℕ) : Set (Queue J → ℝ) :=
  interior (convexHull ℝ ((fun σ : State J => fun q => (σ q : ℝ)) '' {σ | IsSchedule ν σ}))

end MaxWeightInstab


