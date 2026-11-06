-- Prove2me | Definitions.Def_ConstrSOSP_cornerGrad
-- name    : ConstrSOSP_cornerGrad
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:04:17.799467+00:00
-- url     : https://prove2.me/theorems/405ca107-3bfc-4e8e-9623-bfbd2f746234
-- title:
--   Gradient prescribed at an integer grid point (with frame)
-- statement:
--   At an integer point $(a,b)$, the gradient of the arrow of the clamped point $P(a,b)$. On $\{0,\dots,N\}^2$ this is the paper's $\nabla f(a,b)$.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), p.31; proof of Corollary 5.6, p.55

import Mathlib
import Definitions.Def_ConstrSOSP_gridN
import Definitions.Def_ConstrSOSP_dirGrad
import Definitions.Def_ConstrSOSP_gridArrow

namespace ConstrSOSP

/-- **The gradient prescribed at an integer grid point** (arXiv:2604.02285, 2 Nov 2026, p.31, and
the frame of the proof of Corollary 5.6, p.55: "Give (a, b) the colour and arrow of P(a, b)"):
the gradient (`dirGrad`) of the arrow (`gridArrow`) of the clamped point
`P(a, b) = (min{N, max{0, a}}, min{N, max{0, b}})`. On `{0, …, N}²` this is the paper's
`∇f(a, b)`. -/
noncomputable def cornerGrad (C : Circuit) (a b : ℤ) : Fin 2 → ℝ :=
  dirGrad (gridArrow C (min (gridN C.n : ℤ) (max 0 a)) (min (gridN C.n : ℤ) (max 0 b)))

end ConstrSOSP


