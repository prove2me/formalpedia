-- Prove2me | Definitions.Def_MVBlossoms_IsEvenLevelFromPath
-- name    : MVBlossoms_IsEvenLevelFromPath
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:39:34.117853+00:00
-- url     : https://prove2.me/theorems/65c2a06c-f6a1-4cd4-a321-7fb280df0fb1
-- title:
--   Even level($b;v$) path
-- statement:
--   An **even level($b;v$) path** is a even-length alternating path in $G$ from $b$ to $v$ that starts with an unmatched edge and has minimum length among all such paths.
--
--   Statement 3 of Theorem 3 splits every shortest alternating path to $v$ into a shortest path to $\mathrm{base}(v)$ followed by such a path.
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Definitions 23 and 32, pp.2031, 2037

import Mathlib
import Definitions.Def_MVBlossoms_IsAltPathFromBase
import Definitions.Def_MVBlossoms_evenLevelFrom

namespace MVBlossoms

/-- **Even level(b;v) path.** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), Definitions 23 (p.2031) and 32
(p.2037): a minimum even-length alternating path in `G` from `b` to `v` that starts with an
unmatched edge. -/
def IsEvenLevelFromPath {V : Type} {G : SimpleGraph V} (M : G.Subgraph) {b v : V} (q : G.Walk b v) : Prop :=
  IsAltPathFromBase M q ∧ Even q.length ∧ (q.length : ℕ∞) = evenLevelFrom M b v

end MVBlossoms


