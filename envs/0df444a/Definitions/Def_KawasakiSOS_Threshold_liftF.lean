-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_liftF
-- name    : KawasakiSOS_Threshold_liftF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:02:16.608833+00:00
-- url     : https://prove2.me/theorems/5131a3aa-1486-4f12-a223-4628f525cc5f
-- title:
--   The piecewise-linear profile $F$
-- statement:
--   Let $F:[0,k]\to\mathbb R$ be the piecewise-linear function with
--
--   $$F(j)=\sum_{i<j}d(p_0+i)$$
--
--   at integers $j$, linear between consecutive integers. With $p_0$ the base column, $F\ge0$ and $F(0)=F(k)=0$. The function records how much of the difference between $x$ and $y$ has been accumulated along the cycle.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 10 (PDF p. 11)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_Config
import Definitions.Def_KawasakiSOS_Threshold_diff
import Definitions.Def_KawasakiSOS_Threshold_partialSum

namespace KawasakiSOS.Threshold

/-- The piecewise-linear `F : [0, k] → ℝ` with `F(j) = ∑_{i<j} d(p0 + i)` at integers. Formalization Note: only its values on `[0, k]` are used; `⌊t⌋₊` selects the linear piece.

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 10 (PDF p. 11). -/
noncomputable def liftF {n k : ℕ} [NeZero k] (x y : Config n k) (p0 : ZMod k) (t : ℝ) : ℝ :=
  (partialSum x y p0 ⌊t⌋₊ : ℝ) + (t - (⌊t⌋₊ : ℝ)) * (diff x y (p0 + (⌊t⌋₊ : ZMod k)) : ℝ)

end KawasakiSOS.Threshold


