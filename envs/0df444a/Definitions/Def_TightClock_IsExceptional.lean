-- Prove2me | Definitions.Def_TightClock_IsExceptional
-- name    : TightClock_IsExceptional
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:19:36.210213+00:00
-- url     : https://prove2.me/theorems/9bbead34-6acf-45e4-8557-01b3309f07e9
-- title:
--   Exceptional node, Definition 6.8
-- statement:
--   Fix a state $J\in\{0,\dots,L,\bot\}^n$. A node $S$ at depth $r\ge1$ is **exceptional** at $J$ if
--
--   $$A_S(J)>\frac{A_{\mathrm{par}(S)}(J)}{n^2},$$
--
--   where $\mathrm{par}(S)$ denotes its parent. The root is never exceptional.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), Definition 6.8, §6.5, p.43 (PDF p.46)

import Mathlib
import Definitions.Def_TightClock_account
import Definitions.Def_TightClock_parent
import Definitions.Def_TightClock_toNode

set_option autoImplicit false

namespace TightClock

/-- Definition 6.8: a node at depth `r ≥ 1` is exceptional at `J` if `A_S(J) > A_{par(S)}(J) / n²`.
Afshinmehr et al., manuscript (STOC 2027 submission), §6.5, p.43 (PDF 46). -/
def IsExceptional {q L : ℕ} (T : Tree q L) (J : State q L) (D : NonrootNode q L) : Prop :=
  account T (parent D) J / ((bidderCount q L : ℝ) ^ 2) < account T (toNode D) J

end TightClock


