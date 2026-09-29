-- Prove2me | Definitions.Def_OnlinePrimalDual_AdAuctions_AdAuctionsInstance
-- name    : OnlinePrimalDual_AdAuctions_AdAuctionsInstance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:50:24.690609+00:00
-- url     : https://prove2.me/theorems/72921a15-76f3-4db2-aa77-627140296b2d
-- title:
--   The (single-slot) ad-auctions instance
-- statement:
--   A finite set `I` of buyers, each with a budget `B i > 0`; a finite set `M` of items, each
--   buyer `i` providing a non-negative bid `b i j` for item `j`. `Rmax = maxᵢⱼ b(i,j)/B(i)` is
--   carried as an explicit hypothesis-level bound (`hRmax_bound`), positive (excluding the
--   degenerate all-zero-bid case, for which the book's own formula `c=(1+Rmax)^(1/Rmax)` is
--   undefined).
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 210-212, Section 10.1

import Mathlib

namespace OnlinePrimalDual.AdAuctions

/-- Buchbinder & Naor, *The Design of Competitive Online Algorithms via a Primal-Dual Approach*,
FnT TCS 2009, Section 10.1, p. 210-212 (PDF p. 121-123). The (single-slot) ad-auctions instance:
a finite set `I` of buyers, each with a budget `B i > 0`; a finite set `M` of items, each buyer `i`
providing a bid `b i j ≥ 0` for item `j`. `Rmax = maxᵢⱼ b(i,j)/B(i)` (p. 211) is carried as an
explicit hypothesis-level bound (`hRmax_bound`) rather than derived, matching this series' own
convention (cf. `04-framework`'s `d`, `07-generalized-caching`'s `k`); `hRmax_pos` excludes the
degenerate all-zero-bid instance, for which the book's own formula `c = (1+Rmax)^(1/Rmax)`
(Theorem 10.1) is undefined — the book itself only discusses `Rmax → 0` as a limiting remark, not
as an instance of the main theorem. -/
structure AdAuctionsInstance (I M : Type*) [Fintype I] [Fintype M] where
  /-- Buyer `i`'s bid for item `j`. -/
  b : I → M → ℝ
  hb_nonneg : ∀ i j, 0 ≤ b i j
  /-- Buyer `i`'s daily budget. -/
  B : I → ℝ
  hB_pos : ∀ i, 0 < B i
  /-- `Rmax = maxᵢⱼ b(i,j)/B(i)`, the maximum bid-to-budget ratio (p. 211). -/
  Rmax : ℝ
  hRmax_pos : 0 < Rmax
  hRmax_bound : ∀ i j, b i j ≤ Rmax * B i

end OnlinePrimalDual.AdAuctions


