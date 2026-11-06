-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_partialSum
-- name    : KawasakiSOS_Threshold_partialSum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:00:56.702201+00:00
-- url     : https://prove2.me/theorems/66790f8b-ae42-4fea-be59-4bcb93b7a3c0
-- title:
--   The partial sums of $d$ from a base column
-- statement:
--   For a column $p_0$ and $j\ge0$, this is the partial sum
--
--   $$F(j)=\sum_{i<j}d(p_0+i).$$
--
--   In lifted coordinates, $j\in\{0,\dots,k-1\}$ stands for column $p_0+j$.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 10 (PDF p. 11)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_Config
import Definitions.Def_KawasakiSOS_Threshold_diff

namespace KawasakiSOS.Threshold

/-- `∑_{i<j} d(p0 + i)`, the value `F(j)` at integers.

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 10 (PDF p. 11). -/
def partialSum {n k : ℕ} [NeZero k] (x y : Config n k) (p0 : ZMod k) (j : ℕ) : ℤ :=
  ∑ i ∈ Finset.range j, diff x y (p0 + (i : ZMod k))

end KawasakiSOS.Threshold


