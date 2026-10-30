-- Prove2me | Definitions.Def_LNTopology_Hermetization_badAt
-- name    : LNTopology_Hermetization_badAt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:26:31.261995+00:00
-- url     : https://prove2.me/theorems/b27b15df-c857-406e-baa6-bb4f32b39860
-- title:
--   Ticked degree test
-- statement:
--   **Ticked degree test.** Given a decidable predicate $\mathrm{bad}$ on natural numbers and a degree $d$, it returns whether $\mathrm{bad}(d)$ holds, at the cost of one tick. The peeling algorithm of Lemma B.3 deletes a vertex when its current degree is bad.
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Topology, working paper (SSRN 4439190, February 3, 2023), Lemma B.3 and its proof, p. 12 (PDF p. 13) (real-RAM cost model)

import Mathlib
import Definitions.Def_LNTopology_Hermetization_tick

namespace LNTopology.Hermetization

/-- **Ticked degree test.**
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Topology*, working paper
(SSRN 4439190, February 3, 2023), Lemma B.3, p. 12 ("at each step, delete all the vertices of degree ≤ …"; real-RAM reading
R4, see `tick`).

`badAt bad d` charges one tick and returns whether the degree `d` fails the test, i.e. whether
`bad d` holds. In the mission's use `bad` is a decidable predicate on natural numbers. -/
def badAt (bad : ℕ → Prop) [DecidablePred bad] (d : ℕ) : StateM ℕ Bool := do
  tick 1
  pure (decide (bad d))

end LNTopology.Hermetization


