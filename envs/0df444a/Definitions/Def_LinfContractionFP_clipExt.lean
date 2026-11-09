-- Prove2me | Definitions.Def_LinfContractionFP_clipExt
-- name    : LinfContractionFP_clipExt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:13:56.807257+00:00
-- url     : https://prove2.me/theorems/6a11272b-d465-48b3-b9c3-8427d76d6e56
-- title:
--   The clipped extension $x\mapsto f(\mathrm{clip}_{[0,1]^d}(x))$
-- statement:
--   For $f:\mathbb R^\iota\to\mathbb R^\iota$, the **clipped extension** is the map
--   $$x\longmapsto f\big(\mathrm{clip}_{[0,1]^\iota}(x)\big),\qquad x\in\mathbb R^\iota.$$
--   It agrees with $f$ on the cube. Throughout the paper $f$ denotes this extension (Section 3), because the algorithm produces search boxes and candidate points that may leave the cube.
-- source:
--   Soleymani–Farina, A Quasipolynomial Algorithm for ℓ∞ Contractions, arXiv:2610.30122 (held version, sha256 595b44934c28fc12e2cc9cb0fb7c0750d40a24fcd5661627726f3915a24cc0de), Section 3, p.5

import Mathlib
import Definitions.Def_LinfContractionFP_clipCube

namespace LinfContractionFP

/-- The clipped extension of `f` to all of `ℝ^ι`: `x ↦ f(clip[0,1]^ι(x))`.

Soleymani–Farina, arXiv:2610.30122 (held version, sha256 595b4493…), Section 3, p.5:
"throughout the paper we extend f to R^d by setting f(x) = f(clip[0,1]^d(x)) for x ∉ [0, 1]^d."

**Formalization Note.** On the cube `clipCube x = x`, so `clipExt f` agrees with `f` there; it
is defined by the same formula everywhere. The algorithms of this mission evaluate
`clipExt f`, never `f` off the cube. -/
def clipExt {ι : Type} (f : (ι → ℝ) → (ι → ℝ)) : (ι → ℝ) → (ι → ℝ) := fun x => f (clipCube x)

end LinfContractionFP


