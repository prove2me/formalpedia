-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_rw
-- name    : KawasakiSOS_Threshold_rw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:02:11.049523+00:00
-- url     : https://prove2.me/theorems/34fc4729-4cae-448a-96ee-7c1eb7ed4bf0
-- title:
--   The reservoir mass $r_w$
-- statement:
--   Conservation of mass forces the reservoir of $w_S$ to be
--
--   $$r_w=x(W)+x(U)-y(U).$$
--
--   **Formalization Note** The value is an integer, so that a negative reservoir is not hidden by natural subtraction.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), (5), p. 11 (PDF p. 12)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_Config
import Definitions.Def_KawasakiSOS_Threshold_Stage
import Definitions.Def_KawasakiSOS_Threshold_windows
import Definitions.Def_KawasakiSOS_Threshold_arcU

namespace KawasakiSOS.Threshold

/-- `r_w = x(W) + x(U) − y(U)` of (5), integer valued.

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), (5), p. 11 (PDF p. 12). -/
def rw {n k : ℕ} [NeZero k] (x y : Config n k) (S : Stage k) : ℤ :=
  ∑ i ∈ windows S, (x.1 i : ℤ) + ∑ i ∈ arcU S, (x.1 i : ℤ) - ∑ i ∈ arcU S, (y.1 i : ℤ)

end KawasakiSOS.Threshold


