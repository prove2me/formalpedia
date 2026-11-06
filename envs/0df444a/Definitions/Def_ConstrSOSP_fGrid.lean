-- Prove2me | Definitions.Def_ConstrSOSP_fGrid
-- name    : ConstrSOSP_fGrid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:05:21.489709+00:00
-- url     : https://prove2.me/theorems/e9da2bbf-7301-451e-b160-61fe1ff5a134
-- title:
--   The constructed function $f$ on $[0,N]^2$
-- statement:
--   The function $f$ of the reduction: the piecewise biquintic interpolation over the cells of $[0,N]^2$ of the grid values (p.30) and grid gradients (p.31) of the Iter circuit $C$, with corner Hessian $-\tfrac12I$.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), §§5.1–5.3, pp.22–31

import Mathlib
import Definitions.Def_ConstrSOSP_gridN
import Definitions.Def_ConstrSOSP_cornerVal
import Definitions.Def_ConstrSOSP_cornerGrad
import Definitions.Def_ConstrSOSP_cellInterp

namespace ConstrSOSP

/-- **The constructed function `f` on `[0, N]²`** (arXiv:2604.02285, 2 Nov 2026, §§5.1–5.3,
pp.22–31): the piecewise biquintic interpolation (`cellInterp`, cells `Box(a, b)`,
`0 ≤ a, b ≤ N − 1`, corner Hessian `−½ I`) of the grid values `f(a, b)` (p.30) and grid gradients
`∇f(a, b)` (p.31) of the Iter circuit `C`, with `N = 6·2ⁿ + 6`.

**Formalization Note** Points of the plane are `Fin 2 → ℝ` (`z 0 = x`, `z 1 = y`). Outside
`[0, N]²` the function continues the boundary cells' polynomials; statements are about
`[0, N]²`. -/
noncomputable def fGrid (C : Circuit) : (Fin 2 → ℝ) → ℝ :=
  cellInterp (cornerVal C) (cornerGrad C) 0 (gridN C.n)

end ConstrSOSP


