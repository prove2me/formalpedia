-- Prove2me | Definitions.Def_LNTopology_Hermetization_cAt
-- name    : LNTopology_Hermetization_cAt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:23:06.209173+00:00
-- url     : https://prove2.me/theorems/6e2964e6-8e66-4e72-9371-6f697f98bb22
-- title:
--   Ticked query of the cost function
-- statement:
--   **Ticked query of the cost function.** Given $c$ and $x\in\mathbb R$, it returns $c(x)$ (oracle access to $c$). It is one of the unit-cost primitives of the real-RAM model fixed by the mission's tick counter: it adds one tick to the counter and returns the exact value.
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Topology, working paper (SSRN 4439190, February 3, 2023), Theorem 3.8, p. 8 (PDF p. 9) (real-RAM cost model)

import Mathlib
import Definitions.Def_LNTopology_Hermetization_tick

namespace LNTopology.Hermetization

/-- **Ticked query of the cost function.** `cAt c x` charges one tick and returns `c x` (oracle access to `c`).
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Topology*, working paper
(SSRN 4439190, February 3, 2023), Theorem 3.8, p. 8 (real-RAM reading R4 of "polynomial-time"; see `tick`). -/
def cAt (c : ℝ → ℝ) (x : ℝ) : StateM ℕ ℝ := do
  tick 1
  pure (c x)

end LNTopology.Hermetization


