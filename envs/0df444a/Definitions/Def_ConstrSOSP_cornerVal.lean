-- Prove2me | Definitions.Def_ConstrSOSP_cornerVal
-- name    : ConstrSOSP_cornerVal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:04:01.206676+00:00
-- url     : https://prove2.me/theorems/57f5cb01-fa7b-4664-9734-c50cfdb7ab34
-- title:
--   Value prescribed at an integer grid point (with frame)
-- statement:
--   At an integer point $(a,b)$, the value is $\Phi_c(a,b)$, where $c$ is the colour of the clamped point $P(a,b)=(\min\{N,\max\{0,a\}\},\min\{N,\max\{0,b\}\})$. On $\{0,\dots,N\}^2$ this is the paper's $f(a,b)$; outside it is the frame recipe of p.55 ("Give $(a,b)$ the colour and arrow of $P(a,b)$, evaluating its colour function $\Phi$ at $(a,b)$ itself").
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), §5.3, p.30; proof of Corollary 5.6, p.55

import Mathlib
import Definitions.Def_ConstrSOSP_gridN
import Definitions.Def_ConstrSOSP_colourPhi
import Definitions.Def_ConstrSOSP_gridColour

namespace ConstrSOSP

/-- **The value prescribed at an integer grid point** (arXiv:2604.02285, 2 Nov 2026, §5.3, p.30,
and the frame of the proof of Corollary 5.6, p.55: "For each new integer grid point (a, b), let
P(a, b) = (min{N, max{0, a}}, min{N, max{0, b}}). Give (a, b) the colour and arrow of P(a, b),
evaluating its colour function Φ at (a, b) itself").

`cornerVal C a b = Φ_c(a, b)` where `c` is the colour (`gridColour`) of the clamped point
`P(a, b)` and `N = 6·2ⁿ + 6`. On the grid `{0, …, N}²` this is the paper's `f(a, b)`, since
there `P(a, b) = (a, b)`. -/
noncomputable def cornerVal (C : Circuit) (a b : ℤ) : ℝ :=
  colourPhi (gridN C.n : ℝ)
    (gridColour C (min (gridN C.n : ℤ) (max 0 a)) (min (gridN C.n : ℤ) (max 0 b))) a b

end ConstrSOSP


