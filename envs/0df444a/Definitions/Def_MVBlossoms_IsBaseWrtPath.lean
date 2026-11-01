-- Prove2me | Definitions.Def_MVBlossoms_IsBaseWrtPath
-- name    : MVBlossoms_IsBaseWrtPath
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:40:11.342531+00:00
-- url     : https://prove2.me/theorems/935253c7-2e86-4d96-93db-f3b54ca7d875
-- title:
--   The base $F(p,v)$ of $v$ with respect to $p$
-- statement:
--   Let $p$ be an even level($v$) or odd level($v$) path from an unmatched vertex $f$, and let $t=\mathrm{tenacity}(v)$. Among the vertices of $p$ of tenacity greater than $t$, the one farthest from $f$ on $p$ is $F(p,v)$, the **base of $v$ with respect to $p$**.
--
--   The predicate says that $b=F(p,v)$: $b$ lies on $p$, $\mathrm{tenacity}(b)>t$, and every vertex of $p$ farther from $f$ than $b$ has tenacity at most $t$.
--
--   **Formalization Note** A predicate rather than a function, so nothing is chosen when no such vertex exists.
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Definitions 18-19, pp.2027-2028

import Mathlib
import Definitions.Def_MVBlossoms_tenacity

namespace MVBlossoms

/-- **The base of v with respect to p, `F(p, v)`.** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), Definition 19, p.2028:
"Let t = tenacity(v), and consider all vertices of tenacity > t on p ... Among these vertices,
define the highest one to be the base of v w.r.t. p, denoted by F(p, v)." "Higher" is
Definition 18, p.2027: farther from the start `f` on `p`.

`IsBaseWrtPath M p b` (for `p : G.Walk f v`) says `b = F(p, v)`: `b` lies on `p`, has tenacity
greater than that of `v`, and every vertex of `p` strictly higher than `b` has tenacity at most
that of `v`.

**Formalization Note.** Written as a predicate rather than a function, so no value is chosen when
no vertex of `p` has larger tenacity. Positions on `p` are `(p.takeUntil _ _).length`. -/
def IsBaseWrtPath {V : Type} [DecidableEq V] {G : SimpleGraph V} (M : G.Subgraph) {f v : V}
    (p : G.Walk f v) (b : V) : Prop :=
  ∃ hb : b ∈ p.support, tenacity M v < tenacity M b ∧
    ∀ (w : V) (hw : w ∈ p.support),
      (p.takeUntil b hb).length < (p.takeUntil w hw).length → tenacity M w ≤ tenacity M v

end MVBlossoms


