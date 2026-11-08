-- Prove2me | Definitions.Def_GraphNNSphere_nnGraph
-- name    : GraphNNSphere_nnGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:39:14.936791+00:00
-- url     : https://prove2.me/theorems/148b944d-9d2d-4505-a4fc-807e0f2e2550
-- title:
--   Nearest-neighbor graph $N_\Delta$
-- statement:
--   The nearest-neighbor graph $N_\Delta$ lists the $\Delta$ nearest other data points of each data point.
--
--   **Formalization Note** "Nearest" is the lexicographic order on (distance, label), so distance ties are broken by label and every list has exactly $\min(\Delta,n-1)$ elements. A label is listed when fewer than $\Delta$ other labels precede it in this order.
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), §1.2, p.3

import Mathlib
import Definitions.Def_GraphNNSphere_geo
import Definitions.Def_GraphNNSphere_NavGraph

namespace GraphNNSphere

/-- The nearest-neighbor graph `N_Δ`, which lists the `Δ` nearest other data points of each data
point (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission
(manuscript sha256 93565bc5…), §1.2, p.3).

**Formalization Note** "Nearest" is the lexicographic order on (distance, label), so a distance tie
is broken by label and each list has exactly `min(Δ, n - 1)` elements. The label `j` is listed at
`i` when fewer than `Δ` other labels precede it. -/
noncomputable def nnGraph {n d : ℕ} (X : Fin n → Sph d) (Δ : ℕ) : NavGraph n :=
  fun i => Finset.univ.filter (fun j => j ≠ i ∧
    (Finset.univ.filter (fun l => l ≠ i ∧
      toLex (geo (X i) (X l), l) < toLex (geo (X i) (X j), j))).card < Δ)

end GraphNNSphere


