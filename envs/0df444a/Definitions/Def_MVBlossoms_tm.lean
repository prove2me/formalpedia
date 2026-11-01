-- Prove2me | Definitions.Def_MVBlossoms_tm
-- name    : MVBlossoms_tm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:40:24.815997+00:00
-- url     : https://prove2.me/theorems/219bf732-1cb7-4cc9-818d-93fedd9d4f59
-- title:
--   Minimum tenacity $t_m$
-- statement:
--   $t_m$ denotes the minimum tenacity of a vertex of $G$:
--
--   $$
--   t_m=\min_{v\in V}\mathrm{tenacity}(v).
--   $$
--
--   Always $t_m\le l_m$; the structure theory of the paper concerns the case $t_m<l_m$.
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Definition 9, p.2018

import Mathlib
import Definitions.Def_MVBlossoms_tenacity

namespace MVBlossoms

/-- **Minimum tenacity of a vertex, `t_m`.** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), Definition 9, p.2018: "Throughout, tm
will denote the tenacity of a minimum-tenacity vertex in G."

**Formalization Note.** The infimum over all vertices in `ℕ∞` (a minimum, since `ℕ∞` is
well-ordered). -/
noncomputable def tm {V : Type} {G : SimpleGraph V} (M : G.Subgraph) : ℕ∞ :=
  ⨅ v : V, tenacity M v

end MVBlossoms


