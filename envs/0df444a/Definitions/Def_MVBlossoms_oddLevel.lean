-- Prove2me | Definitions.Def_MVBlossoms_oddLevel
-- name    : MVBlossoms_oddLevel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:38:16.365691+00:00
-- url     : https://prove2.me/theorems/58eccb4f-acc1-47b0-bd14-fdd698885492
-- title:
--   Odd level of a vertex
-- statement:
--   Fix a matching $M$ of $G$. The **odd level** of a vertex $v$, written $\mathrm{odd\ level}(v)$, is the length of a shortest alternating path of odd length from some unmatched vertex to $v$:
--
--   $$
--   \mathrm{odd\ level}(v)=\min\{|p| : p \text{ an alternating path from an unmatched vertex to } v,\ |p| \text{ odd}\},
--   $$
--
--   and $\mathrm{odd\ level}(v)=\infty$ if there is no such path.
--
--   The smallest odd level of an unmatched vertex is the length of a shortest augmenting path.
--
--   **Formalization Note** The value lies in $\mathbb N\cup\{\infty\}$ (`ℕ∞`) and is an infimum, which is $\infty$ exactly when no path exists.
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Definition 4, p.2016

import Mathlib
import Definitions.Def_MVBlossoms_IsAltPathFromUnmatched

namespace MVBlossoms

/-- **Odd level of a vertex.** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), Definition 4, p.2016: "The odd level ...
of a vertex v ... is defined to be the length of a minimum odd-length alternating path from an
unmatched vertex to v ... If there is no such path, odd level(v) ... is defined to be ∞."

**Formalization Note.** The value lies in `ℕ∞`; it is the infimum of the lengths of all
alternating paths (`IsAltPathFromUnmatched`) of odd length ending at `v`, over every unmatched
start `f`, so it is `⊤` exactly when no such path exists (the infimum of the empty family). -/
noncomputable def oddLevel {V : Type} {G : SimpleGraph V} (M : G.Subgraph) (v : V) : ℕ∞ :=
  ⨅ (f : V) (p : G.Walk f v) (_ : IsAltPathFromUnmatched M p) (_ : Odd p.length),
    (p.length : ℕ∞)

end MVBlossoms


