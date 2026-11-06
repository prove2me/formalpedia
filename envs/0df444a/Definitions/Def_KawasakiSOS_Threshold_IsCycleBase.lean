-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_IsCycleBase
-- name    : KawasakiSOS_Threshold_IsCycleBase
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:01:58.031926+00:00
-- url     : https://prove2.me/theorems/a2bd8cc9-6ef1-4902-a11a-093cb1b47c91
-- title:
--   Columns whose partial sums are nonnegative
-- statement:
--   A column $p_0$ is a base for $(x,y)$ if every partial sum $\sum_{i=p_0}^{p_0+t-1}d(i)$ with $0\le t\le k$ is nonnegative. Since $\sum_i d(i)=0$, such a column exists by the cycle lemma.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 10 (PDF p. 11)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_Config
import Definitions.Def_KawasakiSOS_Threshold_partialSum

namespace KawasakiSOS.Threshold

/-- `p0` is a base of the cycle lemma: every partial sum `∑_{i=p0}^{p0+t−1} d(i)`, `0 ≤ t ≤ k`, is nonnegative.

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 10 (PDF p. 11). -/
def IsCycleBase {n k : ℕ} [NeZero k] (x y : Config n k) (p0 : ZMod k) : Prop :=
  ∀ t, t ≤ k → 0 ≤ partialSum x y p0 t

end KawasakiSOS.Threshold


