-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_mu
-- name    : KawasakiSOS_Threshold_mu
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:59:02.704202+00:00
-- url     : https://prove2.me/theorems/a3504df4-7bcb-487e-8b37-1e5021295e40
-- title:
--   The parameter $\mu=\lambda^{-2}$
-- statement:
--   For $\lambda>1$ put $\mu=\lambda^{-2}\in(0,1)$. By the identity $p(h)=2n-2M(h)$, the stationary measure can be written $\pi(h)=\mu^{M(h)}/Z'$, with $Z'=\sum_h\mu^{M(h)}$.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 5 (PDF p. 6)

import Mathlib

namespace KawasakiSOS.Threshold

/-- The parameter `μ = λ⁻²` of §2.1, in `(0,1)` when `λ > 1`. Since `p = 2n − 2M`, `π(h) = μ^{M(h)}/Z′`.

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 5 (PDF p. 6). -/
noncomputable def mu (lam : ℝ) : ℝ := (lam ^ 2)⁻¹

end KawasakiSOS.Threshold


