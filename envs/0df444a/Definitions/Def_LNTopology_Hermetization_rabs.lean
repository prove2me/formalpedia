-- Prove2me | Definitions.Def_LNTopology_Hermetization_rabs
-- name    : LNTopology_Hermetization_rabs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:25:15.455981+00:00
-- url     : https://prove2.me/theorems/e93ee382-fa12-4ad9-9b73-2ba9ca9d8a30
-- title:
--   Ticked absolute value
-- statement:
--   **Ticked absolute value.** Given a real $x$, it returns $|x|$. It is one of the unit-cost primitives of the real-RAM model fixed by the mission's tick counter: it adds one tick to the counter and returns the exact value.
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Topology, working paper (SSRN 4439190, February 3, 2023), Theorem 3.8, p. 8 (PDF p. 9) (real-RAM cost model)

import Mathlib
import Definitions.Def_LNTopology_Hermetization_tick

namespace LNTopology.Hermetization

/-- **Ticked absolute value.** `rabs x` charges one tick and returns `|x|`.
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Topology*, working paper
(SSRN 4439190, February 3, 2023), Theorem 3.8, p. 8 (real-RAM reading R4 of "polynomial-time"; see `tick`). -/
noncomputable def rabs (x : ℝ) : StateM ℕ ℝ := do
  tick 1
  pure |x|

end LNTopology.Hermetization


