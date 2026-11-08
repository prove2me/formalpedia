-- Prove2me | Definitions.Def_TightClock_accountOf
-- name    : TightClock_accountOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:00:29.284264+00:00
-- url     : https://prove2.me/theorems/eb96c2d5-cf31-4557-9228-4a0c892fbacc
-- title:
--   Account formula (6.11) on a set of bidders
-- statement:
--   For a set $S$ of bidders regarded at depth $r$, and an auction state $J$,
--
--   $$A_S(J):=\exp\Big(\sum_{i\in S}\ell_r(J_i)-rh\Big).$$
--
--   **Formalization Note** The formula depends on a node only through its depth and its set, so it is written for a set and a depth. This lets Lemma 6.7 speak of a random child of a fixed set.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §6.4, p.40 (PDF p.43), eq. (6.11)

import Mathlib
import Definitions.Def_TightClock_credit
import Definitions.Def_TightClock_fee
import Definitions.Def_TightClock_State

set_option autoImplicit false

namespace TightClock

/-- The account (6.11) at depth `r` of a set `S` of bidders at the state `J`:
`A_S(J) = exp(∑_{i ∈ S} ℓ_r(Jᵢ) − r h)`. Afshinmehr et al., manuscript (STOC 2027 submission), §6.4, p.40
(PDF 43).

**Formalization Note** The formula depends on the node only through its depth and its set, so it is stated on
sets. This lets Lemma 6.7 speak of a random child of a fixed set. -/
noncomputable def accountOf (q L r : ℕ) (S : Finset (Fin (bidderCount q L))) (J : State q L) : ℝ :=
  Real.exp (∑ i ∈ S, credit q L r (J i) - (r : ℝ) * fee q L)

end TightClock


