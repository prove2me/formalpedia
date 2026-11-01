-- Prove2me | Definitions.Def_MVBlossoms_baseSet
-- name    : MVBlossoms_baseSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:41:09.04227+00:00
-- url     : https://prove2.me/theorems/eca3c3ee-9ce0-4494-a7b5-048dc9dff753
-- title:
--   The set $B(v)$
-- statement:
--   For a vertex $v$,
--
--   $$
--   B(v)=\{F(p,v) : p \text{ an even level}(v)\text{ or odd level}(v)\text{ path}\}.
--   $$
--
--   Statement 2 of Theorem 3 says that $B(v)$ is a singleton for every $v$ of eligible tenacity; its element is the base of $v$.
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Definition 19, p.2028

import Mathlib
import Definitions.Def_MVBlossoms_IsEvenLevelPath
import Definitions.Def_MVBlossoms_IsOddLevelPath
import Definitions.Def_MVBlossoms_IsBaseWrtPath

namespace MVBlossoms

/-- **The set `B(v)`.** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), Definition 19, p.2028: "B(v) = {F(p,v) | p is an even
level(v) or odd level(v) path}."

**Formalization Note.** Defined for every vertex `v` (the paper introduces it for `v` of eligible
tenacity); the paths range over all unmatched start vertices. -/
def baseSet {V : Type} [DecidableEq V] {G : SimpleGraph V} (M : G.Subgraph) (v : V) : Set V :=
  {b | ∃ (f : V) (p : G.Walk f v), (IsEvenLevelPath M p ∨ IsOddLevelPath M p) ∧
    IsBaseWrtPath M p b}

end MVBlossoms


