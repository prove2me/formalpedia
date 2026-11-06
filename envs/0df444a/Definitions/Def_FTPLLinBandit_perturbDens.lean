-- Prove2me | Definitions.Def_FTPLLinBandit_perturbDens
-- name    : FTPLLinBandit_perturbDens
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:03:15.32421+00:00
-- url     : https://prove2.me/theorems/12c83148-d81c-4a58-b58e-dec1fceaa693
-- title:
--   Perturbation density $\rho_t$ of each scheme
-- statement:
--   For a perturbation scheme, a scale $\lambda>0$ and past estimates $\hat\theta_1,\dots,\hat\theta_{t-1}$, the **perturbation density** of round $t$ is
--
--   1. for random weighting with profile $f$ and scalar law $\varphi$: the random-weighting density $\rho_t$ built from the initializer $\rho_1=P_{\lambda I}$ of profile $f$ and the density $\varphi$;
--   2. for the elliptical scheme with profile $f$: $\rho_t=P_{\Sigma_t}$ with $\Sigma_t=\lambda I+\sum_{\tau<t}\hat\theta_\tau\hat\theta_\tau^\top$.
--
--   FTPL plays $x(\hat\Theta_t+Z)$ with $Z\sim\rho_t$; the potential $\Psi_t$, the action mean $\mu_t$ and the action covariance $M_t$ of the analysis are all taken under $\rho_t$.
--
--   **Formalization Note** The past is indexed from $0$, so a list of length $t$ gives the paper's $\rho_{t+1}$. The density is meaningful for $\lambda>0$ (Figure 2: "with parameter $\lambda>0$").
-- source:
--   Wei, Follow the Perturbed Leader for Linear Bandits: √T Regret over General Action Sets, arXiv:2610.17818, Figure 2, p.8; Table 2, p.21

import Mathlib
import Definitions.Def_FTPLLinBandit_Scheme
import Definitions.Def_FTPLLinBandit_radialFn
import Definitions.Def_FTPLLinBandit_scalarDens
import Definitions.Def_FTPLLinBandit_ellDens
import Definitions.Def_FTPLLinBandit_shapeMat
import Definitions.Def_FTPLLinBandit_rwDens

namespace FTPLLinBandit

/-- **The perturbation density `ρ_t` of each scheme.** Wei, arXiv:2610.17818, Figure 2, p.8, and
Table 2, p.21. For the scheme `s`, the scale `λ` and past estimates `θs : Fin t → ℝ^d`:

* random weighting with profile `f` and scalar law `φ`: `ρ_t = rwDens ρ₁ φ θs` with initializer
  `ρ₁ = P_{λI}` of profile `f` (Table 2: `ρ₁(z) ∝ f(‖z‖/√λ)`);
* elliptical with profile `f`: `ρ_t = P_{Σ_t}` with `Σ_t = λI + ∑ θs_i θs_iᵀ`.

**Formalization Note.** Past estimates are indexed from `0`, so a list of length `t` gives the
paper's `ρ_{t+1}`. The definition is meaningful for `λ > 0` (Figure 2: "with parameter λ > 0");
for `λ ≤ 0` the shape matrix may fail to be positive definite and `ellDens` takes a junk value. -/
noncomputable def perturbDens {d t : ℕ} (s : Scheme) (lam : ℝ)
    (θs : Fin t → EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) → ℝ :=
  match s with
  | .randomWeighting f φ =>
      rwDens (ellDens (radialFn d f) (lam • (1 : Matrix (Fin d) (Fin d) ℝ))) (scalarDens φ) θs
  | .elliptical f => ellDens (radialFn d f) (shapeMat lam θs)

end FTPLLinBandit


