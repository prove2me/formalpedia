-- Prove2me | Definitions.Def_CubeSampling_Edk
-- name    : CubeSampling_Edk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:15:29.028205+00:00
-- url     : https://prove2.me/theorems/55a338b6-e3cc-492e-a42e-938c5abe2935
-- title:
--   Exponent $E_{d,k}(R) = d\,I(\tau_R/d)$
-- statement:
--   $$
--   E_{d,k}(R) = d\, I(\tau_R / d), \qquad 0 \le R \le k,
--   $$
--   the binomial tail exponent of the common ball after reserving degree $R$ for the harmonic factors. At $R = 0$ it equals $\Lambda_{d,k}$.
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Section 5.1, p.20

import Mathlib
import Definitions.Def_CubeSampling_Irate
import Definitions.Def_CubeSampling_tauR

namespace CubeSampling

/-- The exponent `E_{d,k}(R) = d I(τ_R / d)` (Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), §5.1, p.20). -/
noncomputable def Edk (d k R : ℕ) : ℝ := d * Irate (tauR d k R / d)

end CubeSampling


