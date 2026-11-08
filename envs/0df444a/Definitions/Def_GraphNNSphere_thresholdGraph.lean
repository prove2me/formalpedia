-- Prove2me | Definitions.Def_GraphNNSphere_thresholdGraph
-- name    : GraphNNSphere_thresholdGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:39:18.347195+00:00
-- url     : https://prove2.me/theorems/40c49bea-1040-46c8-9b46-cd1a60b7522a
-- title:
--   Threshold graph $G_\rho$
-- statement:
--   The threshold graph $G_\rho$ lists all other data points within distance $\rho$ of each data point:
--   $$G_\rho(x)=\{y\in D_n\setminus\{x\}:\delta(x,y)\le\rho\}.$$
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), §1.2, p.3

import Mathlib
import Definitions.Def_GraphNNSphere_geo
import Definitions.Def_GraphNNSphere_NavGraph

namespace GraphNNSphere

/-- The threshold graph `G_ρ`, which lists all other data points within distance `ρ` of each data
point (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission
(manuscript sha256 93565bc5…), §1.2, p.3). "Within distance `ρ`" is `≤ ρ`. -/
noncomputable def thresholdGraph {n d : ℕ} (X : Fin n → Sph d) (ρ : ℝ) : NavGraph n :=
  fun i => Finset.univ.filter (fun j => j ≠ i ∧ geo (X i) (X j) ≤ ρ)

end GraphNNSphere


