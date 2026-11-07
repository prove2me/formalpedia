-- Prove2me | Definitions.Def_HWMaskLeak_Lp
-- name    : HWMaskLeak_Lp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:29:51.105277+00:00
-- url     : https://prove2.me/theorems/e38d9a73-ca2a-4320-a5c8-b99592e68239
-- title:
--   The factor $L_p(u)=|(1-p)+p\,e^{\imath u}|$, eq. (37)
-- statement:
--   For real $p$ and $u$,
--   $$
--   L_p(u):=\bigl|(1-p)+p\exp(\imath u)\bigr|.
--   $$
--   With $p=w/n$, the integrand of the Cauchy coefficient bound for $\hat B_w(t)$ is a product of factors $L_p(\theta+2\pi\varphi_j)$.
-- source:
--   Biswas, Hwang, Maji, Shkredov, Ye, When Masks Leak Their Weight: From Additive Sharing to Learning with Physical Rounding, preprint (version of October 31, 2026, sha256 ab686360…), §4.4, p.24, and App. C.5, p.49, eq. (37)

import Mathlib

namespace HWMaskLeak

/-- **The factor `L_p`, eq. (37)** (Biswas, Hwang, Maji, Shkredov, Ye, *When Masks Leak Their Weight:
From Additive Sharing to Learning with Physical Rounding*, preprint (version of October 31, 2026,
sha256 ab686360…), §4.4, p.24, and App. C.5, p.49): `L_p(u) := |(1 − p) + p exp(ıu)|`, for real `p`
and `u`. -/
noncomputable def Lp (p u : ℝ) : ℝ :=
  ‖((1 - p : ℝ) : ℂ) + (p : ℂ) * Complex.exp ((u : ℂ) * Complex.I)‖

end HWMaskLeak


