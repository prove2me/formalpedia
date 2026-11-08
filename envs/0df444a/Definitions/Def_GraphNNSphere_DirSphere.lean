-- Prove2me | Definitions.Def_GraphNNSphere_DirSphere
-- name    : GraphNNSphere_DirSphere
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:38:36.633374+00:00
-- url     : https://prove2.me/theorems/a3d7468a-6c08-4ed0-9f77-2f6baa09d7dd
-- title:
--   Sphere of directions at $x$
-- statement:
--   The $(d-2)$-sphere of directions at $x\in S^{d-1}$, that is, the unit sphere of the orthogonal complement $x^\perp$. A query at distance $\theta$ from $x$ has the form $\cos\theta\,x+\sin\theta\,v$ with $v$ in this sphere.
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), Lemma 2.3, p.17

import Mathlib
import Definitions.Def_GraphNNSphere_Sph

namespace GraphNNSphere

/-- The `(d - 2)`-sphere of directions at `x`: the unit sphere of `x^⊥` (Lu, *Sharp Limits of
Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256
93565bc5…), Lemma 2.3, p.17). -/
abbrev DirSphere {d : ℕ} (x : Sph d) : Type :=
  Metric.sphere (0 : ↥(Submodule.span ℝ {(x : EuclideanSpace ℝ (Fin d))})ᗮ) 1

end GraphNNSphere


