-- Prove2me | Definitions.Def_TightClock_State
-- name    : TightClock_State
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:47:02.335722+00:00
-- url     : https://prove2.me/theorems/2ff580a3-df21-4bcd-b73c-5555960000e1
-- title:
--   Auction state $J\in\{0,\dots,L,\bot\}^n$
-- statement:
--   A state assigns to each bidder either a cutoff $j\in\{0,\dots,L\}$ (she is active, and her first $L-j$ coins are known to be heads, so her value is known to be at least $y_j$) or $\bot$ (she is inactive).
--
--   **Formalization Note** The set $\{0,\dots,L,\bot\}$ is `Option (Fin (L + 1))`, with `none` for $\bot$.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §6.2, pp.35–36 (PDF pp.38–39)

import Mathlib
import Definitions.Def_TightClock_bidderCount

set_option autoImplicit false

namespace TightClock

/-- An auction state `J ∈ {0, …, L, ⊥}ⁿ`: `J i = some j` means that the bidder `i` is active with cutoff `j`,
and `J i = none` means that she is inactive. Afshinmehr et al., manuscript (STOC 2027 submission), §6.2, p.36
(PDF 39). -/
abbrev State (q L : ℕ) : Type := Fin (bidderCount q L) → Option (Fin (L + 1))

end TightClock


