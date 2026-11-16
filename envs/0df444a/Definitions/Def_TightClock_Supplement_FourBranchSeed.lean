-- Prove2me | Definitions.Def_TightClock_Supplement_FourBranchSeed
-- name    : TightClock_Supplement_FourBranchSeed
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:21:14.142695+00:00
-- url     : https://prove2.me/theorems/f4c346f9-b02c-4445-942f-e0689f9b4723
-- title:
--   Random seed of Auction 10
-- statement:
--   The public random seed of Auction 10: a uniform for the branch index, and the independent uniforms of its branches — for every bidder, the $1/2$-sample of HeadSample, the screening coin and the score draw of its Window, and the $1/2$-sample of HalfSample; a key for every set of bidders (the random ordering of RoutedDisjoint); and the seed of the Disjoint auction run by RoutedDisjoint. The seed space carries the product of uniform laws.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §5, Auctions 5–10, pp.22–31 (PDF pp.25–34)

import Mathlib
import Definitions.Def_TightClock_Supplement_DisjointSeed

set_option autoImplicit false

namespace TightClock.Supplement

/-- The public random seed of Auction 10, `FourBranch`: a uniform for the branch index `κ`, and the
independent uniforms of its branches: per bidder, the `1/2`-sample of `HeadSample`, the
screening coin and the score draw of its `Window`, the `1/2`-sample of `HalfSample`; a key for each
set of bidders (the random ordering of `RoutedDisjoint`); and the seed of the `Disjoint` auction run
by `RoutedDisjoint`. Product of uniform laws (`volume`). Afshinmehr et al., *Tight Approximation Bounds for Clock Auctions*, manuscript (STOC 2027 submission), §5, Auctions 5–10, pp.22–31
(PDF 25–34). -/
abbrev FourBranchSeed (n : ℕ) : Type :=
  unitInterval × (Fin n → unitInterval) × (Fin n → unitInterval) × (Fin n → unitInterval) ×
    (Fin n → unitInterval) × (Finset (Fin n) → unitInterval) × DisjointSeed n

end TightClock.Supplement


