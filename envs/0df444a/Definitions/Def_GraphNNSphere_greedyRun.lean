-- Prove2me | Definitions.Def_GraphNNSphere_greedyRun
-- name    : GraphNNSphere_greedyRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:42:02.621216+00:00
-- url     : https://prove2.me/theorems/04a074a7-d16f-401b-8d47-57084e546f7c
-- title:
--   Navigation run from an entry $x_0$
-- statement:
--   The navigation run from the entry $x_0$. It first evaluates $x_0$, then proceeds by repeated visits, starting with no moves and no expansions.
--
--   **Formalization Note** The fuel $n+1$ exceeds the number of labels, so the fuel bound is never reached.
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), §1.2, p.3

import Mathlib
import Definitions.Def_GraphNNSphere_greedyLoop

namespace GraphNNSphere

/-- The navigation run from the entry `x₀`, which first evaluates `x₀` (Lu, *Sharp Limits of
Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256
93565bc5…), §1.2, p.3).

**Formalization Note** The fuel `n + 1` exceeds the number of labels; see `greedyLoop`. -/
noncomputable def greedyRun {n d : ℕ} (G : NavGraph n) (X : Fin n → Sph d) (q : Sph d) (k : ℕ)
    (x₀ : Fin n) : RunOutcome :=
  greedyLoop G X q k (n + 1) x₀ {x₀} 0 0

end GraphNNSphere


