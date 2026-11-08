-- Prove2me | Definitions.Def_GraphNNSphere_IsDenseRegime
-- name    : GraphNNSphere_IsDenseRegime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:37:14.08319+00:00
-- url     : https://prove2.me/theorems/c9b6d9cb-6bd8-4c14-b79e-d0a6ecc13668
-- title:
--   Dense regime $\sqrt{\log n}\ll d\ll\log n$
-- statement:
--   A dimension sequence $d=d(n)$ is in the dense regime if $\sqrt{\log n}\ll d\ll\log n$.
--
--   **Formalization Note** The relation $\ll$ is encoded by the two limits $d/\sqrt{\log n}\to\infty$ and $d/\log n\to0$.
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), §1.1, p.2

import Mathlib

open Filter Topology

namespace GraphNNSphere

/-- The dense regime `√(log n) ≪ d ≪ log n` for a dimension sequence `d = d(n)` (Lu, *Sharp Limits
of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256
93565bc5…), §1.1, p.2).

**Formalization Note** `≪` is encoded as `d / √(log n) → ∞` and `d / log n → 0`. -/
def IsDenseRegime (d : ℕ → ℕ) : Prop :=
  Tendsto (fun n : ℕ => (d n : ℝ) / Real.sqrt (Real.log (n : ℝ))) atTop atTop ∧
    Tendsto (fun n : ℕ => (d n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 0)

end GraphNNSphere


