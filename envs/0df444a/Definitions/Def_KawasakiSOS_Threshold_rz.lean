-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_rz
-- name    : KawasakiSOS_Threshold_rz
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:02:30.942379+00:00
-- url     : https://prove2.me/theorems/938cf506-29ca-4fda-8ed9-e60104c24713
-- title:
--   The reservoir mass $r_z$
-- statement:
--   Conservation of mass forces the reservoir of $z_{S,\xi}$ to be
--
--   $$r_z=y(W)+y(U)-x(U),$$
--
--   where $h(A)=\sum_{i\in A}h(i)$.
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

/-- `r_z = y(W) + y(U) − x(U)` of (5). Formalization Note: integer valued, so a negative reservoir is visible rather than truncated.

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), (5), p. 11 (PDF p. 12). -/
def rz {n k : ℕ} [NeZero k] (x y : Config n k) (S : Stage k) : ℤ :=
  ∑ i ∈ windows S, (y.1 i : ℤ) + ∑ i ∈ arcU S, (y.1 i : ℤ) - ∑ i ∈ arcU S, (x.1 i : ℤ)

end KawasakiSOS.Threshold


