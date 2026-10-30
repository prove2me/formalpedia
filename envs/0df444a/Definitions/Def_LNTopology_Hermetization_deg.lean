-- Prove2me | Definitions.Def_LNTopology_Hermetization_deg
-- name    : LNTopology_Hermetization_deg
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:17:12.851026+00:00
-- url     : https://prove2.me/theorems/87da62c7-4a57-484e-b977-1a8fa9decc16
-- title:
--   Degree $d(v)$ of a node
-- statement:
--   The **degree** of a node $v$ is the number of channels that involve $v$:
--
--   $$d(v)=\bigl|\{w\in V:\lambda_{v,w}\neq 0\}\bigr|,$$
--
--   that is, the degree $d_V(v)$ of $v$ inside the whole node set.
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Topology, working paper (SSRN 4439190, February 3, 2023), Definition 3.4, p. 7 (PDF p. 8)

import Mathlib
import Definitions.Def_LNTopology_Hermetization_degIn

namespace LNTopology.Hermetization

/-- **Degree of a node.**
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Topology*, working paper
(SSRN 4439190, February 3, 2023), Definition 3.4, p. 7: "Denote by d(v) the degree of v, which is the number of channels
that involve v, i.e. d(v) = |{w ∈ V : λv,w ≠ 0}|". -/
noncomputable def deg {V : Type*} [Fintype V] (lam : V → V → ℝ) (v : V) : ℕ :=
  degIn lam Finset.univ v

end LNTopology.Hermetization


