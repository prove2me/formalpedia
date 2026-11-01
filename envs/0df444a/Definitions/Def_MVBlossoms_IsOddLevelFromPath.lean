-- Prove2me | Definitions.Def_MVBlossoms_IsOddLevelFromPath
-- name    : MVBlossoms_IsOddLevelFromPath
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:39:07.055609+00:00
-- url     : https://prove2.me/theorems/a2a2fd0d-b67d-4df1-8299-0cec0f237f87
-- title:
--   Odd level($b;v$) path
-- statement:
--   An **odd level($b;v$) path** is a odd-length alternating path in $G$ from $b$ to $v$ that starts with an unmatched edge and has minimum length among all such paths.
--
--   Statement 3 of Theorem 3 splits every shortest alternating path to $v$ into a shortest path to $\mathrm{base}(v)$ followed by such a path.
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Definitions 23 and 32, pp.2031, 2037

import Mathlib
import Definitions.Def_MVBlossoms_IsAltPathFromBase
import Definitions.Def_MVBlossoms_oddLevelFrom

namespace MVBlossoms

/-- **Odd level(b;v) path.** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), Definitions 23 (p.2031) and 32
(p.2037): a minimum odd-length alternating path in `G` from `b` to `v` that starts with an
unmatched edge. -/
def IsOddLevelFromPath {V : Type} {G : SimpleGraph V} (M : G.Subgraph) {b v : V} (q : G.Walk b v) : Prop :=
  IsAltPathFromBase M q ∧ Odd q.length ∧ (q.length : ℕ∞) = oddLevelFrom M b v

end MVBlossoms


