-- Prove2me | Definitions.Def_MVBlossoms_minLevel
-- name    : MVBlossoms_minLevel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:39:11.586233+00:00
-- url     : https://prove2.me/theorems/c33e3f77-5f92-4b99-83c1-e9e4b79fb452
-- title:
--   Min level of a vertex
-- statement:
--   For a vertex $v$, $\mathrm{min\ level}(v)$ is the smaller of $\mathrm{even\ level}(v)$ and $\mathrm{odd\ level}(v)$:
--
--   $$
--   \mathrm{min\ level}(v)=\min\{\mathrm{even\ level}(v),\ \mathrm{odd\ level}(v)\}.
--   $$
--
--   The paper defines it when at least one level is finite; here it is $\infty$ otherwise.
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Definition 5, p.2016

import Mathlib
import Definitions.Def_MVBlossoms_evenLevel
import Definitions.Def_MVBlossoms_oddLevel

namespace MVBlossoms

/-- **Min level of a vertex.** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), Definition 5, p.2016: "For a vertex v such that at
least one of even level(v) and odd level(v) is finite, ... min level(v) is defined to be the
smaller of the two."

**Formalization Note.** Defined for every vertex as the minimum in `ℕ∞`; it is `⊤` exactly when
both levels are infinite (the case the paper leaves undefined), and every statement that uses
it either assumes it finite or is unaffected by that case. -/
noncomputable def minLevel {V : Type} {G : SimpleGraph V} (M : G.Subgraph) (v : V) : ℕ∞ :=
  min (evenLevel M v) (oddLevel M v)

end MVBlossoms


