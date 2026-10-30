-- Prove2me | Definitions.Def_LNTopology_Hermetization_LNHermetizable
-- name    : LNTopology_Hermetization_LNHermetizable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:20:57.935885+00:00
-- url     : https://prove2.me/theorems/5f9b6573-3101-4112-8c8d-07558abd6d81
-- title:
--   Hermetizable Lightning Network
-- statement:
--   A Lightning Network is **hermetizable** if some set of its nodes is hermetizable:
--
--   $$\exists\, U\subseteq V:\ c(G_U')<c(G).$$
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Topology, working paper (SSRN 4439190, February 3, 2023), Definition 3.7, p. 8 (PDF p. 9)

import Mathlib
import Definitions.Def_LNTopology_Hermetization_Hermetizable

namespace LNTopology.Hermetization

/-- **Hermetizable Lightning Network.**
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Topology*, working paper
(SSRN 4439190, February 3, 2023), Definition 3.7, p. 8: "A LN is hermetizable if there exists a set of nodes U in the LN
that is hermetizable." -/
def LNHermetizable {V : Type*} [Fintype V] [DecidableEq V] (c : ℝ → ℝ) (lam : V → V → ℝ) :
    Prop :=
  ∃ U : Finset V, Hermetizable c lam U

end LNTopology.Hermetization


