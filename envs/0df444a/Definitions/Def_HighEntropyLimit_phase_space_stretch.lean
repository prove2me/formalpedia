-- Prove2me | Definitions.Def_HighEntropyLimit_phase_space_stretch
-- name    : HighEntropyLimit_phase_space_stretch
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-12T21:52:49.113025+00:00
-- url     : https://prove2.me/theorems/e5b5b8d8-5b25-49cb-97d0-cc347a01876a
-- title:
--   Gibbs entropy and pure stretching maps on phase space
-- statement:
--   Phase space for one degree of freedom is $\mathbb R^2 \ni z = (x,p)$ with Lebesgue measure.
--
--   1. The Gibbs entropy of a density $\rho$ is $S(\rho) = -\int_{\mathbb R^2}\rho\log\rho\,dx\,dp$ (Sec. 4.1).
--   2. The pure stretching map $T(x,p) = (\sqrt\lambda x, \sqrt\lambda p)$ (Eq. 16) transports densities: $$(T\rho)(z) = \frac1\lambda\,\rho\Big(\frac{z}{\sqrt\lambda}\Big).$$
--   3. The same stretch on a Husimi distribution $Q_1$ on $\mathbb C$ (Eq. 24) is $$Q_\lambda(\alpha) = \frac1\lambda\,Q_1\Big(\frac{\alpha}{\sqrt\lambda}\Big).$$
--
--   **Formalization Note** If $\int\rho\log\rho$ does not converge, the Lean integral returns $0$. Theorems about $S$ therefore assume integrability explicitly.
-- source:
--   Carcassi, Landini, Aidala, Classical mechanics as the high-entropy limit of quantum mechanics, arXiv:2411.00972v3 (1 Feb 2026), https://arxiv.org/abs/2411.00972, p. 7 Eqs. (15),(16); p. 9 Eq. (24)

import Mathlib

namespace HighEntropyLimit

/-- Gibbs/Shannon entropy of a density `ρ` on the phase space `ℝ²` of one degree of freedom,
`S(ρ) = - ∫ ρ log ρ dx dp` (Section 4.1). -/
noncomputable def gibbsEntropy (ρ : ℝ × ℝ → ℝ) : ℝ :=
  - ∫ z, ρ z * Real.log (ρ z)

/-- The pure stretching map `T(x, p) = (√λ x, √λ p)` of Eq. (16), acting on a phase-space
density by push-forward: `(Tρ)(z) = λ⁻¹ ρ(z / √λ)`. -/
noncomputable def pureStretch (lam : ℝ) (ρ : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun z => lam⁻¹ * ρ ((Real.sqrt lam)⁻¹ • z)

/-- The stretch of a Husimi distribution on `ℂ`, Eq. (24): `Q_λ(α) = λ⁻¹ Q₁(α / √λ)`. -/
noncomputable def husimiStretch (lam : ℝ) (Q : ℂ → ℝ) : ℂ → ℝ :=
  fun α => lam⁻¹ * Q ((Real.sqrt lam)⁻¹ • α)

end HighEntropyLimit


