-- Prove2me | Definitions.Def_LNTopology_Hermetization_lamAt
-- name    : LNTopology_Hermetization_lamAt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:22:38.303361+00:00
-- url     : https://prove2.me/theorems/4a86bfdf-4daf-47f3-976a-56d959f5fe8a
-- title:
--   Ticked read of a channel flow
-- statement:
--   **Ticked read of a channel flow.** Given flows $\Lambda$ and nodes $i,j$, it returns $\lambda_{i,j}$. It is one of the unit-cost primitives of the real-RAM model fixed by the mission's tick counter: it adds one tick to the counter and returns the exact value.
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Topology, working paper (SSRN 4439190, February 3, 2023), Theorem 3.8, p. 8 (PDF p. 9) (real-RAM cost model)

import Mathlib
import Definitions.Def_LNTopology_Hermetization_tick

namespace LNTopology.Hermetization

/-- **Ticked read of a channel flow.** `lamAt lam i j` charges one tick and returns `lam i j`.
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Topology*, working paper
(SSRN 4439190, February 3, 2023), Theorem 3.8, p. 8 (real-RAM reading R4 of "polynomial-time"; see `tick`). -/
def lamAt {V : Type*} (lam : V → V → ℝ) (i j : V) : StateM ℕ ℝ := do
  tick 1
  pure (lam i j)

end LNTopology.Hermetization


