-- Prove2me | Definitions.Def_GraphNNSphere_alphaNorm
-- name    : GraphNNSphere_alphaNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:37:24.80071+00:00
-- url     : https://prove2.me/theorems/4f2159e6-211c-4aa2-a3a7-059aaced26fb
-- title:
--   Normalizing constant $\alpha_{d-1}$
-- statement:
--   The normalizing constant of the angular density:
--   $$\alpha_{d-1}=\frac{\Gamma(d/2)}{\sqrt\pi\,\Gamma((d-1)/2)}.$$
--   For $d\ge2$, the distance from a fixed point to a uniform point of $S^{d-1}$ has density $\alpha_{d-1}(\sin t)^{d-2}$ on $[0,\pi]$.
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), Lemma 2.1, p.14

import Mathlib

namespace GraphNNSphere

/-- The normalizing constant `α_{d-1} = Γ(d/2) / (√π Γ((d-1)/2))` of the angular density (Lu, *Sharp
Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript
sha256 93565bc5…), Lemma 2.1, p.14). -/
noncomputable def alphaNorm (d : ℕ) : ℝ :=
  Real.Gamma ((d : ℝ) / 2) / (Real.sqrt Real.pi * Real.Gamma (((d : ℝ) - 1) / 2))

end GraphNNSphere


