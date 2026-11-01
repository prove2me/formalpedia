-- Prove2me | Definitions.Def_MVBlossoms_oddLevelFrom
-- name    : MVBlossoms_oddLevelFrom
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:38:05.624253+00:00
-- url     : https://prove2.me/theorems/ee423837-2167-4caf-ac1b-e8fe100e35e5
-- title:
--   Length of an odd level($b;v$) path
-- statement:
--   For vertices $b,v$, the number $\mathrm{odd\ level}(b;v)$ is the minimum length of a odd-length alternating path in $G$ from $b$ to $v$ that starts with an unmatched edge ($\infty$ if there is none). The minimum is over all of $G$.
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Definitions 23 and 32, pp.2031, 2037

import Mathlib
import Definitions.Def_MVBlossoms_IsAltPathFromBase

namespace MVBlossoms

/-- **Length of an odd level(b;v) path.** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), Definitions 23 (p.2031) and 32
(p.2037): "by an odd level(b;v) path, we mean a minimum odd-length alternating path in G from
b to v that starts with an unmatched edge."

`oddLevelFrom M b v` is that minimum length.

**Formalization Note.** The minimum is taken over **all** of `G`, in `ℕ∞` (`⊤` if there is no such
path). The paper uses the notion for `b` an (iterated) base of `v`; the definition is general. -/
noncomputable def oddLevelFrom {V : Type} {G : SimpleGraph V} (M : G.Subgraph) (b v : V) : ℕ∞ :=
  ⨅ (q : G.Walk b v) (_ : IsAltPathFromBase M q) (_ : Odd q.length), (q.length : ℕ∞)

end MVBlossoms


