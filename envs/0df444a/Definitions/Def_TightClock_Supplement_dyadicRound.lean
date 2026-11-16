-- Prove2me | Definitions.Def_TightClock_Supplement_dyadicRound
-- name    : TightClock_Supplement_dyadicRound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:09:03.860205+00:00
-- url     : https://prove2.me/theorems/3a7da387-5b59-400d-a81a-c4f879602bf9
-- title:
--   Dyadic rounding $q(v)$, (4.2)
-- statement:
--   The **dyadic rounding** of a value $v\ge0$ is
--
--   $$q(v)=\begin{cases}2^{\lfloor\log_2 v\rfloor},&v>0,\\0,&v=0,\end{cases}$$
--
--   the largest power of two not exceeding $v$.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §4.2, (4.2), p.17 (PDF p.20)

import Mathlib

set_option autoImplicit false

namespace TightClock.Supplement

/-- The dyadic rounding `q(v) = 2^{⌊log₂ v⌋}` for `v > 0` and `q(0) = 0`, display (4.2). Afshinmehr et al., *Tight Approximation Bounds for Clock Auctions*, manuscript (STOC 2027 submission),
§4.2, p.17 (PDF 20).

**Formalization Note** `Int.log 2 v` is `⌊log₂ v⌋` for `v > 0`; the value is `0` for every
`v ≤ 0` (only `v = 0` occurs). -/
noncomputable def dyadicRound (v : ℝ) : ℝ :=
  if 0 < v then (2 : ℝ) ^ (Int.log 2 v) else 0

end TightClock.Supplement


