-- Prove2me | Definitions.Def_MeanFieldOpt_ControlDuality_Parisi
-- name    : MeanFieldOpt_ControlDuality_Parisi
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T04:07:05.612986+00:00
-- url     : https://prove2.me/theorems/62dd9bd1-f5c6-4fe2-8ac1-404dae4f7d42
-- title:
--   $\nu(t)$, the Parisi functional $\mathsf P(\gamma)$, the Legendre transform $\Phi^*_\gamma$ and the HJB candidate $V$
-- statement:
--   Fix a mixture $\xi$ and $\gamma\in\mathsf{SF}_+$, with Cole–Hopf solution $\Phi_\gamma$.
--
--   1. $\nu(t)=\int_t^1\xi''(s)\gamma(s)\,ds$.
--   2. The **Parisi functional** (Eq. (1.6)) is
--   $$\mathsf P(\gamma)=\Phi_\gamma(0,0)-\frac12\int_0^1 t\,\xi''(t)\gamma(t)\,dt .$$
--   3. (The negative of) the **Legendre transform** of $\Phi_\gamma$ is
--   $$\Phi^*_\gamma(t,z)=\inf_{x\in\mathbb R}\big\{\Phi_\gamma(t,x)-xz\big\}.$$
--   4. The **candidate solution of the HJB equation** (Eq. (7.2)) is
--   $$V(t,z)=\Phi^*_\gamma(t,z)-\frac12\nu(t)z^2-\frac12\int_t^1\nu(s)\,ds .$$
--
--   These are the two sides of the duality of the mission: $V$ is the value function of the stochastic control problem, and $V(0,0)=\mathsf P(\gamma)$.
--
--   **Formalization Note** The infimum defining $\Phi^*_\gamma(t,z)$ is a real infimum; it is the true infimum for $|z|<1$, where the family is bounded below by $0$ (because $\Phi_\gamma(t,x)\ge|x|$), and no statement uses it for $|z|\ge1$.
-- source:
--   El Alaoui, Montanari, Sellke, Optimization of Mean-field Spin Glasses, arXiv:2001.00904v1, p. 3, Eq. (1.6) (Parisi functional); p. 11, below Eq. (4.5) (ν); p. 34, Section 7.1 (Φ*_γ and Eq. (7.2))

import Mathlib
import Definitions.Def_MeanFieldOpt_ControlDuality_ColeHopf

namespace MeanFieldOpt.ControlDuality

/-- `ν(t) = ∫_t^1 ξ''(s) γ(s) ds` (p. 11, below Eq. (4.5)). -/
noncomputable def nu (ξ : Mixture) (d : SFData) (t : ℝ) : ℝ :=
  ∫ s in t..1, ξ.xi'' s * d.toFun s

/-- The Parisi functional `P(γ) = Φ_γ(0, 0) − ½ ∫_0^1 t ξ''(t) γ(t) dt` (Eq. (1.6), p. 3), for
`γ ∈ SF₊` given by `d`. -/
noncomputable def Parisi (ξ : Mixture) (d : SFData) : ℝ :=
  PhiSF ξ d 0 0 - (1 / 2) * ∫ s in (0 : ℝ)..1, s * ξ.xi'' s * d.toFun s

/-- (The negative of) the Legendre transform `Φ*_γ(t, z) = inf_{x ∈ ℝ} {Φ_γ(t, x) − x z}`
(p. 34). For `|z| < 1` the family is bounded below (by `0`, since `Φ_γ(t, x) ≥ |x|`); it is only
used there. -/
noncomputable def PhiStar (ξ : Mixture) (d : SFData) (t z : ℝ) : ℝ :=
  ⨅ x : ℝ, (PhiSF ξ d t x - x * z)

/-- The candidate solution of the HJB equation (Eq. (7.2), p. 34):
`V(t, z) = Φ*_γ(t, z) − ½ ν(t) z² − ½ ∫_t^1 ν(s) ds`. -/
noncomputable def V (ξ : Mixture) (d : SFData) (t z : ℝ) : ℝ :=
  PhiStar ξ d t z - (1 / 2) * nu ξ d t * z ^ 2 - (1 / 2) * ∫ s in t..1, nu ξ d s

end MeanFieldOpt.ControlDuality


