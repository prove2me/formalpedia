-- Prove2me | Definitions.Def_GraphNNSphere_Jrate
-- name    : GraphNNSphere_Jrate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:37:25.917479+00:00
-- url     : https://prove2.me/theorems/32c10d86-855a-450f-9fb9-3cf51b772948
-- title:
--   Lens rate $J_\theta(\rho)$
-- statement:
--   The exponential loss of the lens. With $a=\cos\rho$ and $b=\cos\theta$,
--   $$J_\theta(\rho)=\begin{cases}0,&a\le b^2,\\[2pt]-\dfrac12\log\dfrac{(1-a)(a-\cos2\theta)}{\sin^4\theta},&a>b^2.\end{cases}$$
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), Lemma 2.2, p.15

import Mathlib

namespace GraphNNSphere

/-- The lens rate `J_θ(ρ)`: with `a = cos ρ` and `b = cos θ`, it is `0` if `a ≤ b²` and
`-(1/2) log((1 - a)(a - cos 2θ) / sin⁴ θ)` if `a > b²` (Lu, *Sharp Limits of Graph-Based Nearest
Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), Lemma 2.2,
p.15). -/
noncomputable def Jrate (θ ρ : ℝ) : ℝ :=
  if Real.cos ρ ≤ Real.cos θ ^ 2 then 0
  else -(1 / 2) * Real.log ((1 - Real.cos ρ) * (Real.cos ρ - Real.cos (2 * θ)) / Real.sin θ ^ 4)

end GraphNNSphere


