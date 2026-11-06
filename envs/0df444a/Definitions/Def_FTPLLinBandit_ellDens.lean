-- Prove2me | Definitions.Def_FTPLLinBandit_ellDens
-- name    : FTPLLinBandit_ellDens
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:01:10.496182+00:00
-- url     : https://prove2.me/theorems/8172e85c-6497-4d1e-a574-711ca4b6c702
-- title:
--   Elliptical density $P_\Sigma(z)\propto f(\|z\|_{\Sigma^{-1}})$
-- statement:
--   For a radial profile $f$ and a positive definite $d\times d$ matrix $\Sigma$, the **elliptical density** is
--   $$P_\Sigma(z)=\frac{f\big(\|z\|_{\Sigma^{-1}}\big)}{\int_{\mathbb R^d}f\big(\|y\|_{\Sigma^{-1}}\big)\,dy},\qquad \|z\|_{\Sigma^{-1}}=\sqrt{z^\top\Sigma^{-1}z},$$
--   a probability density with respect to Lebesgue measure on $\mathbb R^d$. The elliptical perturbation of round $t$ is $\rho_t=P_{\Sigma_t}$ (Figure 2, Option 2), and the random-weighting initializer is $\rho_1=P_{\lambda I}$.
--
--   **Formalization Note** The normalizer is an integral, not a closed form. For a positive definite $\Sigma$ and each profile of `radialFn` with $d\ge1$ it is finite and positive. For a singular or indefinite $\Sigma$ Lean's conventions ($\Sigma^{-1}=0$, $\sqrt{\cdot}$ of a negative number is $0$, the integral of a non-integrable function is $0$, $x/0=0$) give a junk value; the mission uses $P_\Sigma$ only for positive definite $\Sigma$.
-- source:
--   Wei, Follow the Perturbed Leader for Linear Bandits: √T Regret over General Action Sets, arXiv:2610.17818, §4, p.9; Figure 2, p.8; Table 4, p.21

import Mathlib
import Definitions.Def_FTPLLinBandit_quadForm

namespace FTPLLinBandit

/-- **The elliptical density `P_Σ(z) ∝ f(‖z‖_{Σ⁻¹})`.** Wei, arXiv:2610.17818, §4, p.9 ("We
consider perturbation distributions whose density ρ_t(z) is proportional to f(‖z‖_{Σ_t⁻¹})");
Figure 2, Option 2, p.8 ("ρ_t = P_{Σ_t}"); Table 4, p.21.

`ellDens f Σ z = f(√(zᵀΣ⁻¹z)) / ∫ f(√(yᵀΣ⁻¹y)) dy`, the normalized density with respect to
Lebesgue measure on ℝ^d.

**Formalization Note.** The normalizer is written as an integral, not in closed form. For `Σ`
positive definite and each profile of `radialFn` (with `d ≥ 1`) it is finite and positive, so
`ellDens` is a probability density. For a singular or indefinite `Σ`, or a non-integrable profile,
Lean's conventions (`Σ⁻¹ = 0`, `√` of a negative number `= 0`, the integral of a non-integrable
function `= 0`, `x / 0 = 0`) give a junk value; every statement of the mission uses `ellDens` only
with `Σ` positive definite. -/
noncomputable def ellDens {d : ℕ} (f : ℝ → ℝ) (S : Matrix (Fin d) (Fin d) ℝ)
    (z : EuclideanSpace ℝ (Fin d)) : ℝ :=
  f (Real.sqrt (quadForm S⁻¹ z)) / ∫ y, f (Real.sqrt (quadForm S⁻¹ y))

end FTPLLinBandit


