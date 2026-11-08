-- Prove2me | Definitions.Def_TightClock_account
-- name    : TightClock_account
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:12:47.67197+00:00
-- url     : https://prove2.me/theorems/15d5b775-fda8-4707-9a46-cfbd91dd0067
-- title:
--   Account $A_S(J)$ of a node, (6.11)
-- statement:
--   The account of a node $S$ of a realized tree, at a state $J$, is (6.11) with $r$ the depth of $S$ and with the bidder set of $S$.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §6.4, p.40 (PDF p.43), eq. (6.11)

import Mathlib
import Definitions.Def_TightClock_accountOf
import Definitions.Def_TightClock_nodeSet

set_option autoImplicit false

namespace TightClock

/-- The account (6.11) of a node `S` in a realized tree, at the state `J`. Afshinmehr et al., manuscript
(STOC 2027 submission), §6.4, p.40 (PDF 43). -/
noncomputable def account {q L : ℕ} (T : Tree q L) (S : TreeNode q L) (J : State q L) : ℝ :=
  accountOf q L S.1.val (nodeSet T S) J

end TightClock


