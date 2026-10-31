-- Prove2me | Definitions.Def_MehtaOnlineAdAllocation_MSVV_Instance
-- name    : MehtaOnlineAdAllocation_MSVV_Instance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T15:36:38.196767+00:00
-- url     : https://prove2.me/theorems/d20b1097-4603-438c-bdfc-fe34ff77381d
-- title:
--   Finite budgeted allocation instances
-- statement:
--   A finite budgeted allocation instance has $N$ advertisers, $M$ ordered query occurrences, arbitrary positive real budgets $B_u$, and arbitrary nonnegative real bids $b_{ut}$. Query positions may have identical bid columns. No score, algorithm or performance assertion is part of the instance.
--
--   Advertisers and occurrences are enumerated by finite types. An absent edge is represented by bid zero. Removing a zero-budget advertiser and replacing any assignment to it by rejection changes no payment; hence positive budgets lose no revenue instance. Similarly, an assignment to a zero entry can be erased without changing any spend or future availability. Budgets need not be equal, and no bound on bids is included here.
-- source:
--   Aranyak Mehta, Online Matching and Ad Allocation, Foundations and Trends in Theoretical Computer Science 8(4), 265–368, 2013, DOI 10.1561/0400000057 (published), §§2.1–2.2, printed pp. 274–280 (PDF pp. 12–18); §5, printed pp. 306–308 (PDF pp. 44–46).

import Mathlib

namespace MehtaOnlineAdAllocation.MSVV

structure Instance (N M : ℕ) where
  budget : Fin N → ℝ
  budget_pos : ∀ u, 0 < budget u
  bid : Fin N → Fin M → ℝ
  bid_nonneg : ∀ u t, 0 ≤ bid u t

end MehtaOnlineAdAllocation.MSVV


