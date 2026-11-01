-- Prove2me | Definitions.Def_EThetaPoula_Risk_semimetric
-- name    : EThetaPoula_Risk_semimetric
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:22:24.040593+00:00
-- url     : https://prove2.me/theorems/7a4b7620-5f87-4082-97de-c47fe607ce7b
-- title:
--   The semimetric $w_{1,\hat p}$, (44)
-- statement:
--   For probability measures $\mu,\nu$ on $\mathbb R^d$,
--   $$
--   w_{1,\hat p}(\mu,\nu):=\inf_{\zeta\in\mathcal C(\mu,\nu)}\int_{\mathbb R^d}\int_{\mathbb R^d}[1\wedge|\theta-\theta'|](1+V_{\hat p}(\theta)+V_{\hat p}(\theta'))\,\zeta(d\theta,d\theta'),
--   $$
--   where $V_{\hat p}(\theta)=(1+|\theta|^2)^{\hat p/2}$. This weighted distance dominates $W_1$ and controls $W_2^2$, and the Langevin SDE contracts in it.
--
--   **Formalization Note** The value lies in $[0,\infty]$ and the integrand is nonnegative, so no integrability is involved. The set of couplings is the published `WassersteinDRO_StrongDuality_couplings`. Only integer $\hat p$ is needed; the paper uses $\hat p=2$.
-- source:
--   Lim, Neufeld, Sabanis, Zhang, arXiv:2210.13193v3, §6.2, (44), p.24

import Mathlib
import Definitions.Def_WassersteinDRO_StrongDuality_couplings
import Definitions.Def_EThetaPoula_Risk_Model

open MeasureTheory

namespace EThetaPoula.Risk

/-- The semimetric `w_{1,p̂}(μ, ν) := inf_{ζ ∈ C(μ,ν)} ∫∫ [1 ∧ |θ − θ′|](1 + V_p̂(θ) + V_p̂(θ′)) ζ(dθ, dθ′)`
of (44), Lim, Neufeld, Sabanis, Zhang, arXiv:2210.13193v3, §6.2, p.24.

**Formalization Note.** The value is in `[0, ∞]` and the integrand is nonnegative, so no
integrability is involved; the paper restricts `μ`, `ν` to the measures with `∫ V_p̂ dμ < ∞`. The set
of couplings is nonempty for probability measures, so the infimum is not the empty-set value. -/
noncomputable def semimetric {d : ℕ} (p : ℕ) (μ ν : Measure (Eucl d)) : ENNReal :=
  ⨅ π ∈ WassersteinDRO.StrongDuality.couplings μ ν,
    ∫⁻ z, ENNReal.ofReal (min 1 ‖z.1 - z.2‖ * (1 + lyapunov p z.1 + lyapunov p z.2)) ∂π

end EThetaPoula.Risk


