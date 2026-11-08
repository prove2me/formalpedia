-- Prove2me | Definitions.Def_GraphNNSphere_CEvent
-- name    : GraphNNSphere_CEvent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:41:03.623803+00:00
-- url     : https://prove2.me/theorems/31e1f586-71d4-4a31-9440-69e4762228be
-- title:
--   Cap event $C(q)$
-- statement:
--   For a fixed query $q$, the event $C(q)$: the cap $C(q,A)$ contains no false local minimum relative to $\mathrm{Top}_k(q)$, that is, no data point outside $\mathrm{Top}_k(q)$ with no closer neighbor in $G_r$.
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), §3.1, p.20

import Mathlib
import Definitions.Def_GraphNNSphere_IsTarget
import Definitions.Def_GraphNNSphere_thresholdGraph

namespace GraphNNSphere

/-- The cap event `C(q)`: `C(q, A)` contains no false local minimum, that is, no data point outside
`Top_k(q)` with no closer neighbor in `G_r` (Lu, *Sharp Limits of Graph-Based Nearest Neighbor
Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §3.1, p.20). -/
def CEvent {n d : ℕ} (k : ℕ) (X : Fin n → Sph d) (q : Sph d) (A r : ℝ) : Prop :=
  ∀ i, geo q (X i) ≤ A → ¬ IsTarget k X q i →
    ∃ j ∈ thresholdGraph X r i, geo q (X j) < geo q (X i)

end GraphNNSphere


