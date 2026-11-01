-- Prove2me | Definitions.Def_MVBlossoms_evenLevelFrom
-- name    : MVBlossoms_evenLevelFrom
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:38:08.120299+00:00
-- url     : https://prove2.me/theorems/11bb4b23-40dd-44db-9648-62934423073d
-- title:
--   Length of an even level($b;v$) path
-- statement:
--   For vertices $b,v$, the number $\mathrm{even\ level}(b;v)$ is the minimum length of a even-length alternating path in $G$ from $b$ to $v$ that starts with an unmatched edge ($\infty$ if there is none). The minimum is over all of $G$.
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Definitions 23 and 32, pp.2031, 2037

import Mathlib
import Definitions.Def_MVBlossoms_IsAltPathFromBase

namespace MVBlossoms

/-- **Length of an even level(b;v) path.** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), Definitions 23 (p.2031) and 32
(p.2037): "by an even level(b;v) path, we mean a minimum even-length alternating path in G from
b to v that starts with an unmatched edge."

`evenLevelFrom M b v` is that minimum length.

**Formalization Note.** The minimum is taken over **all** of `G`, in `ℕ∞` (`⊤` if there is no such
path). The paper uses the notion for `b` an (iterated) base of `v`; the definition is general. -/
noncomputable def evenLevelFrom {V : Type} {G : SimpleGraph V} (M : G.Subgraph) (b v : V) : ℕ∞ :=
  ⨅ (q : G.Walk b v) (_ : IsAltPathFromBase M q) (_ : Even q.length), (q.length : ℕ∞)

end MVBlossoms


