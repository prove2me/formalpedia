-- Prove2me | Definitions.Def_GraphNNSphere_improvingDirs
-- name    : GraphNNSphere_improvingDirs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:39:59.1991+00:00
-- url     : https://prove2.me/theorems/2c78c984-d71e-47e3-943c-0e0b8a6fb183
-- title:
--   Improving directions at $x$
-- statement:
--   The set of directions $v$ at $x$ for which the query $q=\cos\theta\,x+\sin\theta\,v$, at distance $\theta$ from $x$, satisfies $\delta(q,y)<\theta$, so that the point $y$ is closer to $q$ than $x$ is.
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), Lemma 2.3, p.17

import Mathlib
import Definitions.Def_GraphNNSphere_DirSphere

namespace GraphNNSphere

/-- The directions `v` at `x` for which the query `q = cos θ x + sin θ v`, at distance `θ` from `x`,
has `δ(q, y) < θ` (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027
submission (manuscript sha256 93565bc5…), Lemma 2.3, p.17). -/
def improvingDirs {d : ℕ} (x y : Sph d) (θ : ℝ) : Set (DirSphere x) :=
  {v | InnerProductGeometry.angle
      (Real.cos θ • (x : EuclideanSpace ℝ (Fin d)) +
        Real.sin θ • (((v : ↥(Submodule.span ℝ {(x : EuclideanSpace ℝ (Fin d))})ᗮ)) :
          EuclideanSpace ℝ (Fin d)))
      (y : EuclideanSpace ℝ (Fin d)) < θ}

end GraphNNSphere


