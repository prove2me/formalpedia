-- Prove2me | Definitions.Def_TightClock_Supplement_sizeRestricted
-- name    : TightClock_Supplement_sizeRestricted
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:13:28.076633+00:00
-- url     : https://prove2.me/theorems/fb8efc56-5966-4ef5-8295-7cf268fadafc
-- title:
--   Size-restricted family $\mathcal F(m)$
-- statement:
--   For $m\ge1$ the **size-restricted family** is
--
--   $$\mathcal F(m)=\{S\in\mathcal F:|S|\le m\},$$
--
--   the feasible sets with at most $m$ bidders ("heads" for $m=\lceil\log(8d)\rceil$). It is downward closed when $\mathcal F$ is.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §5, p.21 (PDF p.24)

import Mathlib

set_option autoImplicit false

namespace TightClock.Supplement

/-- The size-restricted family `F(m) = {S ∈ F : |S| ≤ m}`. Afshinmehr et al., *Tight Approximation Bounds for Clock Auctions*, manuscript (STOC 2027 submission), §5, p.21 (PDF 24). -/
def sizeRestricted {n : ℕ} (F : Finset (Finset (Fin n))) (m : ℕ) : Finset (Finset (Fin n)) :=
  F.filter (fun S => S.card ≤ m)

end TightClock.Supplement


