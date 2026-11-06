-- Prove2me | Definitions.Def_FTPLLinBandit_radialFn
-- name    : FTPLLinBandit_radialFn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:01:21.081669+00:00
-- url     : https://prove2.me/theorems/a0a83274-597a-4828-bfff-af2437ecc5c2
-- title:
--   Radial profiles $f(s)=e^{-s^2/2}$, $e^{-\sqrt d\,s}$, $(1+s^2)^{-(d+2)/2}$
-- statement:
--   For a dimension $d$, the **radial profile** $f:[0,\infty)\to(0,\infty)$ of each law of Tables 2 and 4 is
--   $$f_{\mathrm{Gauss}}(s)=e^{-s^2/2},\qquad f_{\mathrm{Lap}}(s)=e^{-\sqrt d\,s},\qquad f_{t_2}(s)=(1+s^2)^{-(d+2)/2}.$$
--   The elliptical law with shape $\Sigma$ has density $P_\Sigma(z)\propto f(\|z\|_{\Sigma^{-1}})$ (Table 4); with $\Sigma=\lambda I$ these are the initializers of Table 2, $\rho_1(z)\propto e^{-\|z\|^2/(2\lambda)}$, $e^{-\sqrt d\|z\|/\sqrt\lambda}$, $(1+\|z\|^2/\lambda)^{-(d+2)/2}$.
--
--   **Formalization Note** The profile is a function on $\mathbb R$, evaluated only at $s=\|z\|_{\Sigma^{-1}}\ge0$.
-- source:
--   Wei, Follow the Perturbed Leader for Linear Bandits: √T Regret over General Action Sets, arXiv:2610.17818, §4, p.9; Tables 2 and 4, p.21

import Mathlib
import Definitions.Def_FTPLLinBandit_RadialProfile

namespace FTPLLinBandit

/-- **The radial profile `f` of each law of Tables 2 and 4.** Wei, arXiv:2610.17818, Table 4,
p.21: `P_Σ(z) ∝ e^{−‖z‖²_{Σ⁻¹}/2}` (Gaussian), `e^{−√d ‖z‖_{Σ⁻¹}}` (radial Laplace),
`(1 + ‖z‖²_{Σ⁻¹})^{−(d+2)/2}` (Student-t₂); §4, p.9: "density ρ_t(z) is proportional to
f(‖z‖_{Σ_t⁻¹}) … for some radial profile f : ℝ≥0 → ℝ≥0".

`radialFn d f s` is `e^{−s²/2}`, `e^{−√d s}` or `(1 + s²)^{−(d+2)/2}`.

**Formalization Note.** The profile is a function `ℝ → ℝ`; it is only evaluated at
`s = ‖z‖_{Σ⁻¹} ≥ 0`. With `Σ = λI` these are the initializers of Table 2:
`e^{−‖z‖²/(2λ)}`, `e^{−√d‖z‖/√λ}`, `(1 + ‖z‖²/λ)^{−(d+2)/2}`. -/
noncomputable def radialFn (d : ℕ) : RadialProfile → ℝ → ℝ
  | .gaussian, s => Real.exp (-(s ^ 2) / 2)
  | .radialLaplace, s => Real.exp (-(Real.sqrt d * s))
  | .studentT2, s => (1 + s ^ 2) ^ (-((d : ℝ) + 2) / 2)

end FTPLLinBandit


