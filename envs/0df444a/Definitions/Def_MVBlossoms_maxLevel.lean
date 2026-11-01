-- Prove2me | Definitions.Def_MVBlossoms_maxLevel
-- name    : MVBlossoms_maxLevel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:39:22.235714+00:00
-- url     : https://prove2.me/theorems/2c8184d6-0169-43db-9243-2a963acdb8ba
-- title:
--   Max level of a vertex
-- statement:
--   For a vertex $v$, $\mathrm{max\ level}(v)$ is the larger of the two levels:
--
--   $$
--   \mathrm{max\ level}(v)=\max\{\mathrm{even\ level}(v),\ \mathrm{odd\ level}(v)\}.
--   $$
--
--   It is finite exactly when both levels are finite, i.e. when $v$ has finite tenacity.
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Definition 5, p.2016

import Mathlib
import Definitions.Def_MVBlossoms_evenLevel
import Definitions.Def_MVBlossoms_oddLevel

namespace MVBlossoms

/-- **Max level of a vertex.** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), Definition 5, p.2016: "max level(v) ... is defined
to be the bigger ... of the two" (even level(v) and odd level(v)).

**Formalization Note.** The maximum in `ℕ∞`; it is `⊤` when one level is infinite, and then no
path has that length, so "max level(v) path" is empty, as in the paper. -/
noncomputable def maxLevel {V : Type} {G : SimpleGraph V} (M : G.Subgraph) (v : V) : ℕ∞ :=
  max (evenLevel M v) (oddLevel M v)

end MVBlossoms


