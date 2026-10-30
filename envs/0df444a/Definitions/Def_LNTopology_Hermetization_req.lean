-- Prove2me | Definitions.Def_LNTopology_Hermetization_req
-- name    : LNTopology_Hermetization_req
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:24:50.717905+00:00
-- url     : https://prove2.me/theorems/7997ad97-1584-4a62-8254-8de972a27fcf
-- title:
--   Ticked real equality test
-- statement:
--   **Ticked real equality test.** Given reals $x,y$, it returns whether $x=y$. It is one of the unit-cost primitives of the real-RAM model fixed by the mission's tick counter: it adds one tick to the counter and returns the exact value.
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Topology, working paper (SSRN 4439190, February 3, 2023), Theorem 3.8, p. 8 (PDF p. 9) (real-RAM cost model)

import Mathlib
import Definitions.Def_LNTopology_Hermetization_tick

namespace LNTopology.Hermetization

/-- **Ticked real equality test.** `req x y` charges one tick and returns whether `x = y`.
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Topology*, working paper
(SSRN 4439190, February 3, 2023), Theorem 3.8, p. 8 (real-RAM reading R4 of "polynomial-time"; see `tick`). -/
noncomputable def req (x y : ℝ) : StateM ℕ Bool := do
  tick 1
  pure (decide (x = y))

end LNTopology.Hermetization


