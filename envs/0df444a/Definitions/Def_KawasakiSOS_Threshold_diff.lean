-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_diff
-- name    : KawasakiSOS_Threshold_diff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:59:48.527199+00:00
-- url     : https://prove2.me/theorems/60f8a503-e65f-4def-9db8-050f846eba5e
-- title:
--   The difference profile $d=x-y$
-- statement:
--   For $x,y\in\Omega_{n,k}$ put $d(i)=x(i)-y(i)$. Since both have total mass $n$, $\sum_i d(i)=0$.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 10 (PDF p. 11)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_Config

namespace KawasakiSOS.Threshold

/-- `d(i) = x(i) − y(i)`, integer valued, with `∑_i d(i) = 0`.

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 10 (PDF p. 11). -/
def diff {n k : ℕ} [NeZero k] (x y : Config n k) (i : ZMod k) : ℤ :=
  (x.1 i : ℤ) - (y.1 i : ℤ)

end KawasakiSOS.Threshold


