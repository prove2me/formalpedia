-- Prove2me | Definitions.Def_TightClock_Supplement_headSize
-- name    : TightClock_Supplement_headSize
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:13:57.866146+00:00
-- url     : https://prove2.me/theorems/6af6f385-0a7b-4197-8f69-cd9a0f040ed2
-- title:
--   Head size $m=\lceil\log(8d)\rceil$
-- statement:
--   The head size is
--
--   $$m=\lceil\log(8d)\rceil,$$
--
--   where $d$ is the maximum overlap of the maximal feasible sets and $\log$ is the natural logarithm. When $d\ge1$, $m\ge3$.
--
--   **Formalization Note** With no bidders $d=0$ and $\log 0=0$ in Lean, so $m=0$; this case has $f(v)=0$.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §5, (5.1), p.21 (PDF p.24); Auction 8, p.27 (PDF p.30)

import Mathlib
import Definitions.Def_TightClock_overlap

set_option autoImplicit false

namespace TightClock.Supplement

/-- The head size `m = ⌈log(8d)⌉`, with `d` the overlap of `F` and `log` the natural logarithm.
Afshinmehr et al., *Tight Approximation Bounds for Clock Auctions*, manuscript (STOC 2027 submission), §5, (5.1), p.21 (PDF 24); Auction 8 (p.27) and Auction 10 (p.31).

**Formalization Note** Natural logarithm, as the proof of Lemma 5.12 requires (`e^{−2m} ≤ 1/(64d²)`
from `m ≥ log(8d)`). At `d = 0` (no bidders) `Real.log 0 = 0` gives `m = 0`. -/
noncomputable def headSize {n : ℕ} (F : Finset (Finset (Fin n))) : ℕ :=
  ⌈Real.log (8 * (overlap F : ℝ))⌉₊

end TightClock.Supplement


