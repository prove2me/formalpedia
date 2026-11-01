-- Prove2me | Definitions.Def_MVBlossoms_IsMinLevelPath
-- name    : MVBlossoms_IsMinLevelPath
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:40:33.850921+00:00
-- url     : https://prove2.me/theorems/66d0dfa8-dc57-4d35-b911-5536985651c1
-- title:
--   Min level($v$) path
-- statement:
--   A **min level($v$) path** is an even level($v$) or odd level($v$) path whose length is $\mathrm{min\ level}(v)$: a shortest alternating path to $v$ from an unmatched vertex, of either parity.
--
--   Its last edge defines predecessors and props (Definition 10).
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Definitions 4-5, p.2016

import Mathlib
import Definitions.Def_MVBlossoms_IsEvenLevelPath
import Definitions.Def_MVBlossoms_IsOddLevelPath
import Definitions.Def_MVBlossoms_minLevel

namespace MVBlossoms

/-- **Min level(v) path.** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), Definitions 4–5, p.2016, as used in
Definition 10 (p.2018) and Theorem 3 (p.2034): an even level(v) or odd level(v) path whose length
is min level(v). -/
def IsMinLevelPath {V : Type} {G : SimpleGraph V} (M : G.Subgraph) {f v : V} (p : G.Walk f v) : Prop :=
  (IsEvenLevelPath M p ∨ IsOddLevelPath M p) ∧ (p.length : ℕ∞) = minLevel M v

end MVBlossoms


