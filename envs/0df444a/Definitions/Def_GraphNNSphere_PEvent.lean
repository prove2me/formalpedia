-- Prove2me | Definitions.Def_GraphNNSphere_PEvent
-- name    : GraphNNSphere_PEvent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:39:14.564534+00:00
-- url     : https://prove2.me/theorems/46a83a0c-8e68-4193-9510-c11d74d9b17b
-- title:
--   Progress event $P(q)$
-- statement:
--   For a fixed query $q$, the event $P(q)$: every data point $x$ outside $C(q,A)$ has a data point $y$ with $\delta(x,y)\le r$ and $\delta(q,y)\le\delta(q,x)-h$. On any graph containing $G_r$, it forces a decrease of at least $h$ whenever an expansion outside the cap does not already succeed.
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), §3.1, p.20

import Mathlib
import Definitions.Def_GraphNNSphere_geo

namespace GraphNNSphere

/-- The progress event `P(q)`: every data point `x` outside `C(q, A)` has a data point `y` with
`δ(x, y) ≤ r` and `δ(q, y) ≤ δ(q, x) - h` (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search
on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §3.1, p.20). -/
def PEvent {n d : ℕ} (X : Fin n → Sph d) (q : Sph d) (A r h : ℝ) : Prop :=
  ∀ i, A < geo q (X i) → ∃ j, geo (X i) (X j) ≤ r ∧ geo q (X j) ≤ geo q (X i) - h

end GraphNNSphere


