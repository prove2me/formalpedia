-- Prove2me | Definitions.Def_MVBlossoms_IsOuter
-- name    : MVBlossoms_IsOuter
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:40:13.406019+00:00
-- url     : https://prove2.me/theorems/625a0f48-ab7d-49ed-b192-c7a679764f02
-- title:
--   Outer vertex
-- statement:
--   A vertex $v$ with finite min level is **outer** if $\mathrm{even\ level}(v)<\mathrm{odd\ level}(v)$, and **inner** otherwise.
--
--   A vertex with no alternating path from an unmatched vertex (both levels infinite) is neither outer nor inner.
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Definition 6, p.2016

import Mathlib
import Definitions.Def_MVBlossoms_evenLevel
import Definitions.Def_MVBlossoms_oddLevel
import Definitions.Def_MVBlossoms_minLevel

namespace MVBlossoms

/-- **Outer vertex.** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), Definition 6, p.2016: "A vertex v with finite min level is
said to be outer if even level(v) < odd level(v) and inner otherwise."

**Formalization Note.** "Inner" is not a separate definition: it is "finite min level and not
outer". -/
def IsOuter {V : Type} {G : SimpleGraph V} (M : G.Subgraph) (v : V) : Prop :=
  minLevel M v ≠ ⊤ ∧ evenLevel M v < oddLevel M v

end MVBlossoms


