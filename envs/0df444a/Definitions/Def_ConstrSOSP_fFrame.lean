-- Prove2me | Definitions.Def_ConstrSOSP_fFrame
-- name    : ConstrSOSP_fFrame
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:05:21.681998+00:00
-- url     : https://prove2.me/theorems/8d25fed2-e522-4840-9d55-a07670e83fc6
-- title:
--   Framed function $\bar f$ on $[-m,N+m]^2$
-- statement:
--   The framed function $\bar f$: the grid is extended to $[-m,N+m]^2$, each new integer point gets the colour and arrow of its clamped point $P(a,b)$ with the colour function evaluated at $(a,b)$ itself, and the same biquintic interpolation is applied. It agrees with $f$ on $[0,N]^2$.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), proof of Corollary 5.6, pp.55–56

import Mathlib
import Definitions.Def_ConstrSOSP_gridN
import Definitions.Def_ConstrSOSP_frameM
import Definitions.Def_ConstrSOSP_cornerVal
import Definitions.Def_ConstrSOSP_cornerGrad
import Definitions.Def_ConstrSOSP_cellInterp

namespace ConstrSOSP

/-- **The framed function `f̄` on `[−m, N + m]²`** (arXiv:2604.02285, 2 Nov 2026, proof of
Corollary 5.6, pp.55–56: "extend the grid to [−m, N + m]^2. For each new integer grid point
(a, b), let P(a, b) = (min{N, max{0, a}}, min{N, max{0, b}}). Give (a, b) the colour and arrow of
P(a, b), evaluating its colour function Φ at (a, b) itself. Keep the same second-order and mixed
corner data and use the same biquintic interpolation. Denote the resulting function by f̄").

The piecewise biquintic interpolation (`cellInterp`) of `cornerVal`, `cornerGrad` over the cells
`Box(a, b)`, `−m ≤ a, b ≤ N + m − 1`. It agrees with `fGrid` on `[0, N]²`. -/
noncomputable def fFrame (C : Circuit) : (Fin 2 → ℝ) → ℝ :=
  cellInterp (cornerVal C) (cornerGrad C) (-(frameM C.n : ℤ)) (gridN C.n + frameM C.n)

end ConstrSOSP


