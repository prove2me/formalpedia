-- Prove2me | Definitions.Def_GraphNNSphere_logDim
-- name    : GraphNNSphere_logDim
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:37:11.634241+00:00
-- url     : https://prove2.me/theorems/79badf8e-6873-4242-8cfa-efe82f8973fd
-- title:
--   Dimension sequence of the logarithmic regime
-- statement:
--   The dimension sequence $d=\lfloor c\log n\rfloor$ of the logarithmic regime, for a fixed $c>0$, where $\log$ is the natural logarithm.
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), §1.1, p.2

import Mathlib

namespace GraphNNSphere

/-- The dimension sequence `d = ⌊c log n⌋` of the logarithmic regime (Lu, *Sharp Limits of
Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256
93565bc5…), §1.1, p.2). -/
noncomputable def logDim (c : ℝ) (n : ℕ) : ℕ := ⌊c * Real.log (n : ℝ)⌋₊

end GraphNNSphere


