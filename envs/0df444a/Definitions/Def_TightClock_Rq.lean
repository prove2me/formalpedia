-- Prove2me | Definitions.Def_TightClock_Rq
-- name    : TightClock_Rq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:50:12.53192+00:00
-- url     : https://prove2.me/theorems/84e88bb9-c548-4041-9567-2f63484765e0
-- title:
--   Constant $R_q$
-- statement:
--   With $a=1/q$,
--
--   $$R_q:=\frac{e^a-1+a^2}{a(1-a)}.$$
--
--   It tends to $1$ as $q\to\infty$.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §6.7, p.48 (PDF p.51)

import Mathlib
import Definitions.Def_TightClock_a

set_option autoImplicit false

namespace TightClock

/-- The constant `R_q := (eᵃ − 1 + a²) / (a (1 − a))`. Afshinmehr et al., manuscript (STOC 2027 submission),
§6.7, p.48 (PDF 51). -/
noncomputable def Rq (q : ℕ) : ℝ := (Real.exp (a q) - 1 + (a q) ^ 2) / (a q * (1 - a q))

end TightClock


