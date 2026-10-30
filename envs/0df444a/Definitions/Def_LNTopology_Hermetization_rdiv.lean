-- Prove2me | Definitions.Def_LNTopology_Hermetization_rdiv
-- name    : LNTopology_Hermetization_rdiv
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:26:07.734594+00:00
-- url     : https://prove2.me/theorems/01c124ce-0af9-41fd-b0e4-6fef9c7a43b2
-- title:
--   Ticked real quotient
-- statement:
--   **Ticked real quotient.** Given reals $x,y$, it returns $x/y$ (with the convention $x/0=0$). It is one of the unit-cost primitives of the real-RAM model fixed by the mission's tick counter: it adds one tick to the counter and returns the exact value.
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Topology, working paper (SSRN 4439190, February 3, 2023), Theorem 3.8, p. 8 (PDF p. 9) (real-RAM cost model)

import Mathlib
import Definitions.Def_LNTopology_Hermetization_tick

namespace LNTopology.Hermetization

/-- **Ticked real quotient.** `rdiv x y` charges one tick and returns `x / y` (Lean's `x / 0 = 0`).
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Topology*, working paper
(SSRN 4439190, February 3, 2023), Theorem 3.8, p. 8 (real-RAM reading R4 of "polynomial-time"; see `tick`). -/
noncomputable def rdiv (x y : ℝ) : StateM ℕ ℝ := do
  tick 1
  pure (x / y)

end LNTopology.Hermetization


