-- Prove2me | Definitions.Def_TightClock_Supplement_nextGrid
-- name    : TightClock_Supplement_nextGrid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:00:04.483375+00:00
-- url     : https://prove2.me/theorems/ab1e214b-4b33-463c-9cc6-7e7a4cd18ebb
-- title:
--   Next grid offer $\delta(\lfloor q/\delta\rfloor+1)$
-- statement:
--   From a current accepted price $q$ the **next grid offer** is
--
--   $$\delta\Big(\Big\lfloor \frac q\delta\Big\rfloor+1\Big),$$
--
--   the least grid point strictly above $q$ (for $\delta>0$). It is also the update $p_i\leftarrow\delta\lfloor p_i/\delta\rfloor+\delta$ of Auction 3.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §3, p.13 (PDF p.16); Auction 3, p.18 (PDF p.21)

import Mathlib

set_option autoImplicit false

namespace TightClock.Supplement

/-- The next grid offer from a current accepted price `q`: `δ(⌊q/δ⌋ + 1)`. Afshinmehr et al., *Tight Approximation Bounds for Clock Auctions*, manuscript (STOC 2027 submission), §3, p.13
(PDF 16): "From a current accepted price q, the next grid offer is δ(⌊q/δ⌋+ 1)." It is also the
update `pᵢ ← δ⌊pᵢ/δ⌋ + δ` of Auction 3 (p.18, PDF 21). -/
noncomputable def nextGrid (δ q : ℝ) : ℝ :=
  δ * ((⌊q / δ⌋ : ℝ) + 1)

end TightClock.Supplement


