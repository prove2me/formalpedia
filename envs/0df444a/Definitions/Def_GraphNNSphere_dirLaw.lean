-- Prove2me | Definitions.Def_GraphNNSphere_dirLaw
-- name    : GraphNNSphere_dirLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:39:53.275884+00:00
-- url     : https://prove2.me/theorems/6024535e-77ad-41d2-9328-2aba07d9859b
-- title:
--   Normalized measure on the directions at $x$
-- statement:
--   The normalized measure on the sphere of directions at $x$, under which the direction $v$ of a query at fixed distance from $x$ is uniform.
--
--   **Formalization Note** It is the published `OAI.NoiselessRegression.sphereLaw` at $E=x^\perp$.
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), Lemma 2.3, p.17

import Mathlib
import Definitions.Def_OAI_Probability_ProjectionMoments_Model
import Definitions.Def_GraphNNSphere_DirSphere

open MeasureTheory

namespace GraphNNSphere

/-- The normalized measure on the sphere of directions at `x` (Lu, *Sharp Limits of Graph-Based
Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…),
Lemma 2.3, p.17).

**Formalization Note** This is the published `OAI.NoiselessRegression.sphereLaw` at `E = x^⊥`. -/
noncomputable def dirLaw {d : ℕ} (x : Sph d) : Measure (DirSphere x) :=
  OAI.NoiselessRegression.sphereLaw (E := ↥(Submodule.span ℝ {(x : EuclideanSpace ℝ (Fin d))})ᗮ)

end GraphNNSphere


