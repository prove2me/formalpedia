-- Prove2me | Definitions.Def_MVBlossoms_evenLevel
-- name    : MVBlossoms_evenLevel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:38:02.522901+00:00
-- url     : https://prove2.me/theorems/315e121f-7f82-465e-9686-c87bea86a41e
-- title:
--   Even level of a vertex
-- statement:
--   Fix a matching $M$ of $G$. The **even level** of a vertex $v$, written $\mathrm{even\ level}(v)$, is the length of a shortest alternating path of even length from some unmatched vertex to $v$:
--
--   $$
--   \mathrm{even\ level}(v)=\min\{|p| : p \text{ an alternating path from an unmatched vertex to } v,\ |p| \text{ even}\},
--   $$
--
--   and $\mathrm{even\ level}(v)=\infty$ if there is no such path.
--
--   The even level of an unmatched vertex is $0$.
--
--   **Formalization Note** The value lies in $\mathbb N\cup\{\infty\}$ (`ℕ∞`) and is an infimum, which is $\infty$ exactly when no path exists.
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Definition 4, p.2016

import Mathlib
import Definitions.Def_MVBlossoms_IsAltPathFromUnmatched

namespace MVBlossoms

/-- **Even level of a vertex.** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), Definition 4, p.2016: "The even level ...
of a vertex v ... is defined to be the length of a minimum even-length alternating path from an
unmatched vertex to v ... If there is no such path, even level(v) ... is defined to be ∞."

**Formalization Note.** The value lies in `ℕ∞`; it is the infimum of the lengths of all
alternating paths (`IsAltPathFromUnmatched`) of even length ending at `v`, over every unmatched
start `f`, so it is `⊤` exactly when no such path exists (the infimum of the empty family). -/
noncomputable def evenLevel {V : Type} {G : SimpleGraph V} (M : G.Subgraph) (v : V) : ℕ∞ :=
  ⨅ (f : V) (p : G.Walk f v) (_ : IsAltPathFromUnmatched M p) (_ : Even p.length),
    (p.length : ℕ∞)

end MVBlossoms


