-- Prove2me | Definitions.Def_FTPLLinBandit_scalarDens
-- name    : FTPLLinBandit_scalarDens
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:01:25.802701+00:00
-- url     : https://prove2.me/theorems/8e550315-5972-446b-9128-38bf7eb5eb46
-- title:
--   Scalar weight densities $\varphi(\xi)=e^{-\xi^2/2}/\sqrt{2\pi}$ and $e^{-|\xi|}/2$
-- statement:
--   The normalized densities of the two scalar laws of Table 3 are
--   $$\varphi_{\mathrm{Gauss}}(\xi)=\frac{e^{-\xi^2/2}}{\sqrt{2\pi}},\qquad \varphi_{\mathrm{Lap}}(\xi)=\frac{e^{-|\xi|}}{2},\qquad \xi\in\mathbb R .$$
--   In round $t$ of the random-weighting construction each past estimate $\hat\theta_\tau$ is reweighted by a fresh $\xi_{t,\tau}\sim\varphi$.
-- source:
--   Wei, Follow the Perturbed Leader for Linear Bandits: √T Regret over General Action Sets, arXiv:2610.17818, Table 3, p.21; Figure 2, p.8

import Mathlib
import Definitions.Def_FTPLLinBandit_ScalarLaw

namespace FTPLLinBandit

/-- **The scalar weight density `φ` of Table 3.** Wei, arXiv:2610.17818, Table 3, p.21:
`φ(ξ) ∝ e^{−ξ²/2}` (Gaussian) and `φ(ξ) ∝ e^{−|ξ|}` (Laplace).

`scalarDens φ ξ` is the normalized density: `e^{−ξ²/2}/√(2π)` or `e^{−|ξ|}/2`. -/
noncomputable def scalarDens : ScalarLaw → ℝ → ℝ
  | .gaussian, ξ => Real.exp (-(ξ ^ 2) / 2) / Real.sqrt (2 * Real.pi)
  | .laplace, ξ => Real.exp (-|ξ|) / 2

end FTPLLinBandit


