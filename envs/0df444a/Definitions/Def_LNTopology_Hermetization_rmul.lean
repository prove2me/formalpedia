-- Prove2me | Definitions.Def_LNTopology_Hermetization_rmul
-- name    : LNTopology_Hermetization_rmul
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:25:37.766614+00:00
-- url     : https://prove2.me/theorems/d3fe44f3-db1c-4903-bdda-25cf73a5d612
-- title:
--   Ticked real product
-- statement:
--   **Ticked real product.** Given reals $x,y$, it returns $xy$. It is one of the unit-cost primitives of the real-RAM model fixed by the mission's tick counter: it adds one tick to the counter and returns the exact value.
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Topology, working paper (SSRN 4439190, February 3, 2023), Theorem 3.8, p. 8 (PDF p. 9) (real-RAM cost model)

import Mathlib
import Definitions.Def_LNTopology_Hermetization_tick

namespace LNTopology.Hermetization

/-- **Ticked real product.** `rmul x y` charges one tick and returns `x * y`.
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Topology*, working paper
(SSRN 4439190, February 3, 2023), Theorem 3.8, p. 8 (real-RAM reading R4 of "polynomial-time"; see `tick`). -/
noncomputable def rmul (x y : ℝ) : StateM ℕ ℝ := do
  tick 1
  pure (x * y)

end LNTopology.Hermetization


