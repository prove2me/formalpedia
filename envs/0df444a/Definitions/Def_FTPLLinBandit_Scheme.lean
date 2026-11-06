-- Prove2me | Definitions.Def_FTPLLinBandit_Scheme
-- name    : FTPLLinBandit_Scheme
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:01:29.306704+00:00
-- url     : https://prove2.me/theorems/b7f1ea95-643e-4646-a8c9-ed6c8be5031a
-- title:
--   The nine perturbation schemes of Theorem 13
-- statement:
--   A **perturbation scheme** is one of
--
--   1. **random weighting** with an initializer profile $f$ from Table 2 and a scalar law $\varphi$ from Table 3 ($3\times2=6$ schemes): $Z_t=Z'_t+\sum_{\tau<t}\xi_{t,\tau}\hat\theta_\tau$ with $Z'_t\sim\rho_1=P_{\lambda I}$ and $\xi_{t,\tau}\sim\varphi$ independent;
--   2. **elliptical** with a radial profile $f$ from Table 4 (3 schemes): $Z_t\sim P_{\Sigma_t}$, $\Sigma_t=\lambda I+\sum_{\tau<t}\hat\theta_\tau\hat\theta_\tau^\top$.
--
--   These are the two constructions of Figure 2 and exactly the perturbations covered by Theorem 13.
-- source:
--   Wei, Follow the Perturbed Leader for Linear Bandits: √T Regret over General Action Sets, arXiv:2610.17818, Figure 2, p.8; Theorem 13, p.14

import Mathlib
import Definitions.Def_FTPLLinBandit_RadialProfile
import Definitions.Def_FTPLLinBandit_ScalarLaw

namespace FTPLLinBandit

/-- **The nine perturbation schemes of Theorem 13.** Wei, arXiv:2610.17818, Figure 2, p.8 (Option
1: random-weighting perturbations, "Choose distribution ρ₁ from Table 2 … Choose distribution φ
from Table 3"; Option 2: elliptical perturbations, "Choose distribution family P_Σ from Table 4")
and Theorem 13, p.14.

`randomWeighting f φ` is random weighting with initializer `ρ₁ = P_{λI}` of profile `f` (Table 2)
and scalar law `φ` (Table 3): six schemes. `elliptical f` is the elliptical scheme `ρ_t = P_{Σ_t}`
with profile `f` (Table 4): three schemes. -/
inductive Scheme
  | randomWeighting (f : RadialProfile) (φ : ScalarLaw)
  | elliptical (f : RadialProfile)

end FTPLLinBandit


