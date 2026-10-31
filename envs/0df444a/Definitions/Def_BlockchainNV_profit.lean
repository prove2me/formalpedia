-- Prove2me | Definitions.Def_BlockchainNV_profit
-- name    : BlockchainNV_profit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:40:36.803994+00:00
-- url     : https://prove2.me/theorems/9fd2589a-9ee0-41b0-96cf-cc169b3df312
-- title:
--   Newsvendor profit with lost sales and salvage, $p\min\{q,d\}+s(q-d)^+-wq$
-- statement:
--   A retailer orders $q$ units at the unit wholesale price $w$ before demand is realized. If the demand is $d$, she sells $\min\{q,d\}$ units at the unit retail price $p$; unsatisfied demand is lost, and each of the $(q-d)^+ = \max\{q-d,0\}$ leftover units is disposed of at the unit salvage value $s$. Her profit is
--
--   $$
--   \pi(q,d) = p\,\min\{q,d\} + s\,(q-d)^+ - w\,q .
--   $$
--
--   Equivalently $\pi(q,d) = (p-s)\min\{d,q\} - (w-s)\,q$, the form used in the proof of Theorem 1 (p.ec11). This is the single-period newsvendor profit of the base model; every expected profit in the mission is its expectation.
--
--   **Formalization Note** The order quantity $q$ and the demand $d$ are arbitrary real numbers: the base model has normally distributed demand and restricts neither to be nonnegative.
-- source:
--   Keskin, Li, Song, The Blockchain Newsvendor: Value of Freshness Transparency and Smart Contracts, Management Science (2024), doi:10.1287/mnsc.2021.02949, §2, p.7 (PDF p.7)

import Mathlib

namespace BlockchainNV

/-- Keskin, Li, Song, *The Blockchain Newsvendor: Value of Freshness Transparency and Smart
Contracts*, Management Science (2024), doi:10.1287/mnsc.2021.02949, §2, p.7 (PDF p.7): the
retailer's single-period (newsvendor) profit. She orders `q` units at the unit wholesale price `w`,
sells `min{q, d}` units at the unit retail price `p` when demand is `d` (unsatisfied demand is
lost), and salvages each of the `(q − d)⁺` leftover units at the unit salvage value `s`:
`p · min{q, d} + s · (q − d)⁺ − w · q`.

**Formalization Note.** Order quantity and demand are arbitrary reals: the base model of §2 never
restricts either to be nonnegative (demand is normal). The form `(p − s) min{d, q} − (w − s) q`
used on p.ec11 is an algebraic identity of this definition. -/
def profit (p w s q d : ℝ) : ℝ :=
  p * min q d + s * max (q - d) 0 - w * q

end BlockchainNV


