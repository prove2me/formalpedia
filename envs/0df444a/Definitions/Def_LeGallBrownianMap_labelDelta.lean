-- Prove2me | Definitions.Def_LeGallBrownianMap_labelDelta
-- name    : LeGallBrownianMap_labelDelta
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:36:51.390062+00:00
-- url     : https://prove2.me/theorems/8d76475a-5911-4b9b-8392-266d94378a55
-- title:
--   The label range $\Delta=-\min Z$
-- statement:
--   For a continuous label path $Z$ on $[0,1]$, $\Delta=-\min_{0\le s\le1}Z_s$. Since $D(s,s_*)=Z_s+\Delta$, $\Delta$ is the largest distance to the distinguished point $x_*$.
-- source:
--   Le Gall, Uniqueness and universality of the Brownian map, arXiv:1105.4842v2, §2.4, p.14

import Mathlib

namespace LeGallBrownianMap

/-- Le Gall, *Uniqueness and universality of the Brownian map*, arXiv:1105.4842v2, §2.4, p.14:
"Throughout this work, we will use the notation ∆ = −min_{0≤s≤1} Z_s."

**Formalization Note.** Written `−sInf (range Z)`, the minimum for a continuous `Z`. -/
noncomputable def labelDelta (Z : unitInterval → ℝ) : ℝ := -sInf (Set.range Z)

end LeGallBrownianMap


