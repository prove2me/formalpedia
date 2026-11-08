-- Prove2me | Definitions.Def_TightClock_FB
-- name    : TightClock_FB
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:52:04.736058+00:00
-- url     : https://prove2.me/theorems/73fa86d1-f403-40ec-98e1-b110ec809347
-- title:
--   Expected first-best welfare $\mathrm{FB}(\mathcal F,D)$
-- statement:
--   The **expected first-best welfare** of a family $\mathcal F$ under the i.i.d. prior $D$ is
--
--   $$\mathrm{FB}(\mathcal F,D)=\mathbb E_{X\sim D}[f(X)],$$
--
--   the upper benchmark in Theorem 6.1.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §3, p.14 (PDF p.17)

import Mathlib
import Definitions.Def_TightClock_firstBest
import Definitions.Def_TightClock_priorExpect

set_option autoImplicit false

namespace TightClock

/-- The expected first-best welfare `FB(F, D) = E_{X∼D}[f(X)]`. Afshinmehr et al., manuscript
(STOC 2027 submission), §3, p.14 (PDF 17). -/
noncomputable def FB {n : ℕ} (F : Finset (Finset (Fin n))) (D : FinitePrior) : ℝ :=
  priorExpect D (firstBest F)

end TightClock


