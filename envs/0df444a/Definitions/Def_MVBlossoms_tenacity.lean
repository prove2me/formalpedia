-- Prove2me | Definitions.Def_MVBlossoms_tenacity
-- name    : MVBlossoms_tenacity
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:39:10.599426+00:00
-- url     : https://prove2.me/theorems/ed000297-5999-4728-a9e7-fb9451ef5e43
-- title:
--   Tenacity of a vertex
-- statement:
--   The **tenacity** of a vertex $v$ is
--
--   $$
--   \mathrm{tenacity}(v)=\mathrm{even\ level}(v)+\mathrm{odd\ level}(v),
--   $$
--
--   with $\infty+x=\infty$. A finite tenacity is odd. An unmatched vertex $f$ satisfies $\mathrm{tenacity}(f)\ge l_m$.
--
--   Tenacity is the induction parameter of Theorem 3: blossoms and bases are built in increasing order of tenacity.
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Definition 8, p.2018

import Mathlib
import Definitions.Def_MVBlossoms_evenLevel
import Definitions.Def_MVBlossoms_oddLevel

namespace MVBlossoms

/-- **Tenacity of a vertex.** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), Definition 8, p.2018: "tenacity(v) = even level(v) +
odd level(v)."

**Formalization Note.** The sum is taken in `ℕ∞`, so the tenacity is `⊤` when either level is
infinite (the paper's tenacity(f) = ∞, Figure 6). -/
noncomputable def tenacity {V : Type} {G : SimpleGraph V} (M : G.Subgraph) (v : V) : ℕ∞ :=
  evenLevel M v + oddLevel M v

end MVBlossoms


