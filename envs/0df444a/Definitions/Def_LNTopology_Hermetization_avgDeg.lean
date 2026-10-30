-- Prove2me | Definitions.Def_LNTopology_Hermetization_avgDeg
-- name    : LNTopology_Hermetization_avgDeg
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:17:52.953518+00:00
-- url     : https://prove2.me/theorems/94e4b686-9d40-4cb8-b71f-616464b9597a
-- title:
--   Average degree $\bar d(G)$
-- statement:
--   The **average degree** of a network on a finite node set $V$ is
--
--   $$\bar d(G)=\sum_{v\in V}\frac{d(v)}{|V|}.$$
--
--   It is the density measure in the hypothesis of Theorem 3.8.
--
--   **Formalization Note** On an empty node set the division by $0$ returns $0$, so $\bar d(G)=0$ there.
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Topology, working paper (SSRN 4439190, February 3, 2023), Definition 3.4, p. 7 (PDF p. 8)

import Mathlib
import Definitions.Def_LNTopology_Hermetization_deg

namespace LNTopology.Hermetization

/-- **Average degree d̄(G).**
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Topology*, working paper
(SSRN 4439190, February 3, 2023), Definition 3.4, p. 7: "d̄(G) = Σ_{v∈V} d(v)/|V|".

**Formalization Note.** On the empty node type Lean's `x / 0 = 0` gives `avgDeg lam = 0`. -/
noncomputable def avgDeg {V : Type*} [Fintype V] (lam : V → V → ℝ) : ℝ :=
  (∑ v, (deg lam v : ℝ)) / Fintype.card V

end LNTopology.Hermetization


