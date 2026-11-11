-- Prove2me | Definitions.Def_GaussDiffSVP_coolWeight
-- name    : GaussDiffSVP_coolWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:58:07.812293+00:00
-- url     : https://prove2.me/theorems/cf500592-8ecd-41de-8c50-d2df2d6fd93d
-- title:
--   Cooling pair weight $\omega_r(z) = e^{-A_r(\|z\|^2-R_-^2)}$
-- statement:
--   For the cooling parameter $u$ ($a_0 = 1/(1+u)$, $a_1 = 4a_0-2$, $\gamma^2 = 2(1-u)$), a width $r$ and a shell width $w$,
--   $$A_r = \frac{\pi(\gamma^{-2}-1/2)}{r^2},\qquad R_-^2 = \frac{n r^2 a_1 (1-w)}{2\pi},\qquad \omega_r(z) = e^{-A_r(\|z\|^2-R_-^2)}.$$
--   The factor $e^{-A_r\|z\|^2}$ turns the Gaussian density of a difference into $\rho_{\gamma r}$; the normalization makes $\omega_r\le1$ on the output shell.
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), §5.1, pp.27–28

import Mathlib
import Definitions.Def_SuperlatSVP_lat

namespace GaussDiffSVP

/-- The cooling pair weight `ω_r(z) = e^{−A_r(‖z‖² − R_−²)}` (Gao–Han–Hu, *Gaussian Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), §5.1, pp.27–28), where, for the
cooling parameter `u` of (39) (`a₀ = 1/(1 + u)`, `a₁ = 4a₀ − 2`, `γ² = 2(1 − u)`),
`A_r = π(γ^{−2} − 1/2)/r²` and `R_−² = n r² a₁ (1 − w_n) / (2π)`.

**Formalization Note.** `γ^{−2}` is written `1/(2(1 − u))` and `a₁` as `4/(1 + u) − 2`; `w` is the
shell width `w_n` of the schedule in force. -/
noncomputable def coolWeight {n : ℕ} (w u r : ℝ) (z : SuperlatSVP.E n) : ℝ :=
  Real.exp (-(Real.pi * (1 / (2 * (1 - u)) - 1 / 2) / r ^ 2 *
    (‖z‖ ^ 2 - n * r ^ 2 * (4 / (1 + u) - 2) * (1 - w) / (2 * Real.pi))))

end GaussDiffSVP


