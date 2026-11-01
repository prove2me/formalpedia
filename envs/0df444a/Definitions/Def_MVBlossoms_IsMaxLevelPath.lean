-- Prove2me | Definitions.Def_MVBlossoms_IsMaxLevelPath
-- name    : MVBlossoms_IsMaxLevelPath
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:40:44.365632+00:00
-- url     : https://prove2.me/theorems/967e114c-8853-47aa-af2a-ce1727425622
-- title:
--   Max level($v$) path
-- statement:
--   A **max level($v$) path** is an even level($v$) or odd level($v$) path whose length is $\mathrm{max\ level}(v)$: the shortest alternating path to $v$ of the parity opposite to the min level.
--
--   Statement 1 of Theorem 3 asserts that every such path, for $v$ of eligible tenacity $t$, contains a bridge of tenacity $t$.
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Definitions 4-5, p.2016

import Mathlib
import Definitions.Def_MVBlossoms_IsEvenLevelPath
import Definitions.Def_MVBlossoms_IsOddLevelPath
import Definitions.Def_MVBlossoms_maxLevel

namespace MVBlossoms

/-- **Max level(v) path.** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), Definitions 4–5, p.2016, as used in
Definition 10 (p.2018) and Theorem 3 (p.2034): an even level(v) or odd level(v) path whose length
is max level(v). -/
def IsMaxLevelPath {V : Type} {G : SimpleGraph V} (M : G.Subgraph) {f v : V} (p : G.Walk f v) : Prop :=
  (IsEvenLevelPath M p ∨ IsOddLevelPath M p) ∧ (p.length : ℕ∞) = maxLevel M v

end MVBlossoms


