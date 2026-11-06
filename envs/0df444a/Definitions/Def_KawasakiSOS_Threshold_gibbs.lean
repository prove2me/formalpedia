-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_gibbs
-- name    : KawasakiSOS_Threshold_gibbs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:01:19.933037+00:00
-- url     : https://prove2.me/theorems/13ea6a7d-f6c4-414d-9f2e-30184480402d
-- title:
--   The stationary measure $\pi(h)=\lambda^{p(h)}/Z$
-- statement:
--   The stationary measure of the model on $\Omega_{n,k}$ is
--
--   $$\pi(h)=\frac{\lambda^{p(h)}}{Z}.$$
--
--   For $\lambda>1$ it favours large perimeter, for $\lambda<1$ it favours flat configurations, and for $\lambda=1$ it is uniform.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 1 (PDF p. 2)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_Config
import Definitions.Def_KawasakiSOS_Threshold_perimeter
import Definitions.Def_KawasakiSOS_Threshold_partitionFn

namespace KawasakiSOS.Threshold

/-- The stationary measure `π(h) = λ^{p(h)} / Z`.

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 1 (PDF p. 2). -/
noncomputable def gibbs (n k : ℕ) [NeZero k] (lam : ℝ) (h : Config n k) : ℝ :=
  lam ^ perimeter h.1 / partitionFn n k lam

end KawasakiSOS.Threshold


