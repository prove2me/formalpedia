-- Prove2me | Definitions.Def_GraphNNSphere_rStar
-- name    : GraphNNSphere_rStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:37:26.110964+00:00
-- url     : https://prove2.me/theorems/b227377f-510d-4bdc-a379-9cedef5104e5
-- title:
--   Lens boundary $r^*(\theta)$
-- statement:
--   The radius $r^*(\theta)$ defined by $\cos r^*(\theta)=\cos^2\theta$, at which the lens rate $J_\theta$ vanishes.
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), §2.3, p.16

import Mathlib

namespace GraphNNSphere

/-- The lens boundary `r*(θ)`, defined by `cos r*(θ) = cos² θ` (Lu, *Sharp Limits of Graph-Based
Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §2.3,
p.16). -/
noncomputable def rStar (θ : ℝ) : ℝ := Real.arccos (Real.cos θ ^ 2)

end GraphNNSphere


