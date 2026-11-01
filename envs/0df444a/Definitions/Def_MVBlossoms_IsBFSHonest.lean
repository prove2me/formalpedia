-- Prove2me | Definitions.Def_MVBlossoms_IsBFSHonest
-- name    : MVBlossoms_IsBFSHonest
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:39:19.865058+00:00
-- url     : https://prove2.me/theorems/bcbde27f-7334-4779-993b-317af0980f85
-- title:
--   BFS honesty on a path
-- statement:
--   Let $p$ be an even level($v$) or odd level($v$) path from an unmatched vertex $f$, and let $u$ lie on $p$. Write $|p[f\text{ to }u]|$ for the length of the part of $p$ from $f$ to $u$. The vertex $u$ is **BFS honest on $p$** if
--
--   $$
--   |p[f\text{ to }u]|=\begin{cases}\mathrm{even\ level}(u) & |p[f\text{ to }u]| \text{ even},\\ \mathrm{odd\ level}(u) & |p[f\text{ to }u]| \text{ odd},\end{cases}
--   $$
--
--   i.e. the prefix of $p$ ending at $u$ is itself a shortest alternating path to $u$ of its parity. In bipartite graphs every vertex of a shortest alternating path is BFS honest; in general graphs this fails.
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Definitions 15-16, p.2027

import Mathlib
import Definitions.Def_MVBlossoms_evenLevel
import Definitions.Def_MVBlossoms_oddLevel

namespace MVBlossoms

/-- **BFS honesty on a path.** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), Definition 16, p.2027: "Let p be an even level(v)
or odd level(v) path starting at unmatched vertex f, and let u lie on p. We will say that u is BFS
honest on p if |p[f to u]| = even level(u) (odd level(u)) if u is even (odd) w.r.t. p."

**Formalization Note.** `|p[f to u]|` (Definitions 7, 15) is `(p.takeUntil u hu).length`, the
position of `u` on the simple path `p`. -/
def IsBFSHonest {V : Type} [DecidableEq V] {G : SimpleGraph V} (M : G.Subgraph) {f v : V}
    (p : G.Walk f v) (u : V) (hu : u ∈ p.support) : Prop :=
  (Even (p.takeUntil u hu).length → ((p.takeUntil u hu).length : ℕ∞) = evenLevel M u) ∧
    (Odd (p.takeUntil u hu).length → ((p.takeUntil u hu).length : ℕ∞) = oddLevel M u)

end MVBlossoms


