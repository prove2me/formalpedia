-- Prove2me | Definitions.Def_TightClock_tracked
-- name    : TightClock_tracked
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:25:25.177054+00:00
-- url     : https://prove2.me/theorems/113c1083-aeaf-41ca-b46d-fa7b3fbc6b5d
-- title:
--   Tracked set $R(J)$
-- statement:
--   Fix a good tree. At a state $J$, the **tracked set** is
--
--   $$R(J):=\{\mathrm{root}\}\cup\{S: S\text{ is exceptional at }J\}.$$
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §6.6, p.45 (PDF p.48)

import Mathlib
import Definitions.Def_TightClock_IsExceptional
import Definitions.Def_TightClock_rootNode

set_option autoImplicit false

namespace TightClock

open Classical in
/-- The tracked set `R(J) := {root} ∪ {S : S is exceptional at J}`. Afshinmehr et al., manuscript (STOC 2027
submission), §6.6, p.45 (PDF 48). -/
noncomputable def tracked {q L : ℕ} (T : Tree q L) (J : State q L) : Finset (TreeNode q L) :=
  insert (rootNode q L) ((Finset.univ.filter (IsExceptional T J)).image toNode)

end TightClock


