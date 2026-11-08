-- Prove2me | Definitions.Def_TightClock_epsL
-- name    : TightClock_epsL
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:47:48.822709+00:00
-- url     : https://prove2.me/theorems/d78e55e4-4ec4-41fb-ae6e-07328fe71232
-- title:
--   Error term $\varepsilon_L$ of Lemma 6.3
-- statement:
--   The failure probability of Lemma 6.3,
--
--   $$\varepsilon_L:=\frac{4}{\sqrt B}+L\exp(-q^{2B}).$$
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), Lemma 6.3, §6.3, p.37 (PDF p.40)

import Mathlib
import Definitions.Def_TightClock_B

set_option autoImplicit false

namespace TightClock

/-- The error `ε_L := 4/√B + L exp(−q^{2B})` of Lemma 6.3. Afshinmehr et al., manuscript (STOC 2027 submission),
§6.3, p.37 (PDF 40). -/
noncomputable def epsL (q L : ℕ) : ℝ :=
  4 / Real.sqrt (B L : ℝ) + (L : ℝ) * Real.exp (-((q : ℝ) ^ (2 * B L)))

end TightClock


