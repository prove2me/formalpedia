-- Prove2me | Definitions.Def_TightClock_Supplement_disjointProg
-- name    : TightClock_Supplement_disjointProg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:13:13.914606+00:00
-- url     : https://prove2.me/theorems/4d69abe0-e464-472e-b19a-2b03141ab7a0
-- title:
--   Auction 4 — $\mathrm{Disjoint}$
-- statement:
--   **Auction 4 (Disjoint)** on disjoint groups: flip a fair coin before any query; on heads run MaxSample (Auction 1), on tails run LearnedPricesAuction (Auction 2).
--
--   It is defined for arbitrary groups, because Auction 9 runs it on the routed groups $A_j(\sigma)$.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §4.3, Auction 4, p.19 (PDF p.22)

import Mathlib
import Definitions.Def_TightClock_Supplement_maxSample
import Definitions.Def_TightClock_Supplement_learnedPrices
import Definitions.Def_TightClock_Supplement_DisjointSeed

set_option autoImplicit false

namespace TightClock.Supplement

/-- Auction 4, `Disjoint`, on disjoint groups `Gs`: flip a fair coin before any query; on heads run
`MaxSample` (Auction 1), on tails `LearnedPricesAuction` (Auction 2). Afshinmehr et al., *Tight Approximation Bounds for Clock Auctions*, manuscript (STOC 2027 submission), §4.3, Auction 4, p.19
(PDF 22). It is defined for arbitrary groups because Auction 9 runs it on routed groups. -/
noncomputable def disjointProg {n : ℕ} (δ : ℝ) (Gs : Finset (Finset (Fin n))) (sel : Selector n)
    (ω : DisjointSeed n) : ClockProg n (Finset (Fin n)) :=
  if (ω.1 : ℝ) < 1 / 2 then maxSample δ Gs sel ω.2.1 else learnedPrices δ Gs sel ω.2.2.1 ω.2.2.2

end TightClock.Supplement


