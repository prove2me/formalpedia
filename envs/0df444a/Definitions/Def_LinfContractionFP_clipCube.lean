-- Prove2me | Definitions.Def_LinfContractionFP_clipCube
-- name    : LinfContractionFP_clipCube
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:12:35.052543+00:00
-- url     : https://prove2.me/theorems/2c3a8256-7913-4394-9b26-46eabea905e0
-- title:
--   Clipping a point onto $[0,1]^d$
-- statement:
--   For $x\in\mathbb R^\iota$, $\mathrm{clip}_{[0,1]^\iota}(x)$ is the point with coordinates $\mathrm{clip}_{[0,1]}(x_i)=\max\{0,\min\{1,x_i\}\}$. It is the nearest point of the cube in $\ell_\infty$, and the map is $\ell_\infty$-nonexpansive.
-- source:
--   Soleymani–Farina, A Quasipolynomial Algorithm for ℓ∞ Contractions, arXiv:2610.30122 (held version, sha256 595b44934c28fc12e2cc9cb0fb7c0750d40a24fcd5661627726f3915a24cc0de), Section 3, p.5

import Mathlib
import Definitions.Def_LinfContractionFP_clipInterval

namespace LinfContractionFP

/-- Coordinatewise clipping of a point onto the unit cube: `clip[0,1]^ι(x)_i = clip[0,1](x_i)`.

Soleymani–Farina, arXiv:2610.30122 (held version, sha256 595b4493…), Section 3, p.5. -/
def clipCube {ι : Type} (x : ι → ℝ) : ι → ℝ := fun i => clipInterval 0 1 (x i)

end LinfContractionFP


