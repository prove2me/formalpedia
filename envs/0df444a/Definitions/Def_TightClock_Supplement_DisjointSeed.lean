-- Prove2me | Definitions.Def_TightClock_Supplement_DisjointSeed
-- name    : TightClock_Supplement_DisjointSeed
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:11:46.307266+00:00
-- url     : https://prove2.me/theorems/bc1538a5-3707-435e-8aa0-b2f624da5f71
-- title:
--   Random seed of Auction 4
-- statement:
--   The public random seed of Auction 4: one uniform on $[0,1]$ for the fair coin, and for every bidder one uniform for the $3/8$-sample of MaxSample, one for the $1/4$-sample of LearnedPricesAuction and one for its price-level draw. All are independent; the seed space carries the product of the uniform laws.
--
--   **Formalization Note** A coin of bias $p$ is "$u<p$"; the price level is drawn by the inverse distribution function.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §4, Auctions 1, 2, 4, pp.16–19 (PDF pp.19–22)

import Mathlib

set_option autoImplicit false

namespace TightClock.Supplement

/-- The public random seed of Auction 4: a uniform on `[0,1]` for the fair coin, and for each bidder
a uniform for the `3/8`-sample of `MaxSample`, a uniform for the `1/4`-sample of
`LearnedPricesAuction`, and a uniform for its price-level draw; all independent (product of uniform
laws, `volume`). Afshinmehr et al., *Tight Approximation Bounds for Clock Auctions*, manuscript (STOC 2027 submission), §4, Auctions 1, 2, 4, pp.16–19 (PDF 19–22).

**Formalization Note** Every draw of the auction is realized from these uniforms: a coin of bias
`p` by `u < p`, the level by the inverse distribution function. -/
abbrev DisjointSeed (n : ℕ) : Type :=
  unitInterval × (Fin n → unitInterval) × (Fin n → unitInterval) × (Fin n → unitInterval)

end TightClock.Supplement


