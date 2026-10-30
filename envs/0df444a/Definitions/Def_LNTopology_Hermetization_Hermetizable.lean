-- Prove2me | Definitions.Def_LNTopology_Hermetization_Hermetizable
-- name    : LNTopology_Hermetization_Hermetizable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:20:23.126016+00:00
-- url     : https://prove2.me/theorems/cb5ff543-8c92-48a5-b379-b0163a1c9aaa
-- title:
--   Hermetizable node set
-- statement:
--   A node set $U$ is **hermetizable** if hermetizing it reduces the cost:
--
--   $$c(G_U')<c(G),$$
--
--   where $G_U'$ is the hermetization of $U$ and $c(\cdot)$ is the network cost.
--
--   **Formalization Note** "Reduces its cost" is read as a strict decrease of the total cost. Hermetization changes only the channels inside $U$ and the new channels at $v_0$, so this is the same as a strict decrease of the cost carried by $U$; the identity relating the two is a milestone of the mission.
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Topology, working paper (SSRN 4439190, February 3, 2023), Definition 3.7, p. 8 (PDF p. 9)

import Mathlib
import Definitions.Def_LNTopology_Hermetization_cost
import Definitions.Def_LNTopology_Hermetization_hermetize

namespace LNTopology.Hermetization

/-- **Hermetizable node set.**
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Topology*, working paper
(SSRN 4439190, February 3, 2023), Definition 3.7, p. 8: "A set of nodes U is hermetizable if hermetizing it reduces its
cost."

`Hermetizable c lam U` holds when the cost of the hermetized network (on `Option V`) is
strictly smaller than the cost of the original network.

**Formalization Note.** Reading R1: "reduces its cost" is a strict decrease of the total cost.
Only the channels inside `U` and the new channels at `v₀` change, so this is the same as a
strict decrease of the cost carried by `U` (the identity is a milestone of the mission). -/
def Hermetizable {V : Type*} [Fintype V] [DecidableEq V] (c : ℝ → ℝ) (lam : V → V → ℝ)
    (U : Finset V) : Prop :=
  cost c (hermetize lam U) < cost c lam

end LNTopology.Hermetization


