-- Prove2me | Definitions.Def_LNTopology_Hermetization_gAt
-- name    : LNTopology_Hermetization_gAt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:23:39.352549+00:00
-- url     : https://prove2.me/theorems/14fc19af-18a1-4488-9994-a54e6d6fa6ef
-- title:
--   Ticked query of $g_+$
-- statement:
--   **Ticked query of $g_+$.** Given $g_+$ and $x\in\mathbb R$, it returns $g_+(x)$ (oracle access to $g_+$). It is one of the unit-cost primitives of the real-RAM model fixed by the mission's tick counter: it adds one tick to the counter and returns the exact value.
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Topology, working paper (SSRN 4439190, February 3, 2023), Theorem 3.8, p. 8 (PDF p. 9) (real-RAM cost model)

import Mathlib
import Definitions.Def_LNTopology_Hermetization_tick

namespace LNTopology.Hermetization

/-- **Ticked query of `g₊`.** `gAt g x` charges one tick and returns `g x` (oracle access to `g₊`).
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Topology*, working paper
(SSRN 4439190, February 3, 2023), Theorem 3.8, p. 8 (real-RAM reading R4 of "polynomial-time"; see `tick`). -/
def gAt (g : ℝ → ℝ) (x : ℝ) : StateM ℕ ℝ := do
  tick 1
  pure (g x)

end LNTopology.Hermetization


