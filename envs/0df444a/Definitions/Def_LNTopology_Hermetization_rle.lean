-- Prove2me | Definitions.Def_LNTopology_Hermetization_rle
-- name    : LNTopology_Hermetization_rle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:24:24.329686+00:00
-- url     : https://prove2.me/theorems/8dbe2b15-093b-4d06-a830-598c0ae9c72d
-- title:
--   Ticked real comparison ≤
-- statement:
--   **Ticked real comparison ≤.** Given reals $x,y$, it returns whether $x\le y$. It is one of the unit-cost primitives of the real-RAM model fixed by the mission's tick counter: it adds one tick to the counter and returns the exact value.
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Topology, working paper (SSRN 4439190, February 3, 2023), Theorem 3.8, p. 8 (PDF p. 9) (real-RAM cost model)

import Mathlib
import Definitions.Def_LNTopology_Hermetization_tick

namespace LNTopology.Hermetization

/-- **Ticked real comparison `≤`.** `rle x y` charges one tick and returns whether `x ≤ y`.
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Topology*, working paper
(SSRN 4439190, February 3, 2023), Theorem 3.8, p. 8 (real-RAM reading R4 of "polynomial-time"; see `tick`). -/
noncomputable def rle (x y : ℝ) : StateM ℕ Bool := do
  tick 1
  pure (decide (x ≤ y))

end LNTopology.Hermetization


