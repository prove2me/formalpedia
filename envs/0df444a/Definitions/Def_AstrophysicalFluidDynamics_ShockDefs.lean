-- Prove2me | Definitions.Def_AstrophysicalFluidDynamics_ShockDefs
-- name    : AstrophysicalFluidDynamics_ShockDefs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-04T15:14:55.00199+00:00
-- url     : https://prove2.me/theorems/59248d93-56c4-4aa3-ad27-319c8d036fc0
-- title:
--   Perfect-gas normal shock: enthalpy, sound speed, Mach number, Rankine–Hugoniot relations, entropy jump and the shock-ratio functions
-- statement:
--   Definitions for a **normal, non-magnetic shock** in a **perfect gas** with constant adiabatic exponent $\gamma$ (Ogilvie 2016, §§2.8, 4.5, 6.3.1–6.3.2, Example A.13). Throughout, $\rho$ is density, $p$ pressure and $u$ the velocity component normal to the shock, in the rest frame of the shock; subscript $1$ denotes the upstream (pre-shock) state and $2$ the downstream (post-shock) state.
--
--   1. **Specific enthalpy** (eq. 6.28): $h(p,\rho) = \dfrac{\gamma}{\gamma-1}\,\dfrac{p}{\rho}$.
--   2. **Adiabatic sound speed** (eq. 4.36): $v_s^2 = \dfrac{\gamma p}{\rho}$ and $v_s = (\gamma p/\rho)^{1/2}$.
--   3. **Mach number** (eq. 6.29): $M = u / v_s$.
--   4. **Specific internal energy** (eq. 2.22): $e = \dfrac{p}{(\gamma-1)\rho}$.
--   5. **Rankine–Hugoniot relations** (eqs. 6.27a–c): the upstream state $(\rho_1,u_1,p_1)$ and downstream state $(\rho_2,u_2,p_2)$ satisfy
--   $$[\rho u]_1^2 = 0,\qquad [\rho u^2 + p]_1^2 = 0,\qquad \Big[\rho u\big(\tfrac12 u^2 + h\big)\Big]_1^2 = 0,$$
--   where $[Q]_1^2 = Q_2 - Q_1$.
--   6. **Entropy jump** (from $s = c_p(\gamma^{-1}\ln p - \ln\rho) + \text{const}$, §11.6.2, and $c_p = \gamma c_v$): $\dfrac{[s]_1^2}{c_v} = \ln\dfrac{p_2}{p_1} - \gamma\ln\dfrac{\rho_2}{\rho_1}$.
--   7. **Shock-ratio functions of the upstream Mach number** $M_1$ (eqs. 6.30a,b, 6.31):
--   $$D(M_1) = \frac{(\gamma+1)M_1^2}{(\gamma-1)M_1^2+2},\qquad P(M_1) = \frac{2\gamma M_1^2-(\gamma-1)}{\gamma+1},\qquad M_2^2(M_1) = \frac{2+(\gamma-1)M_1^2}{2\gamma M_1^2-(\gamma-1)}.$$
--
--   These are the objects in terms of which every statement of the mission is phrased.
--
--   **Formalization Note** All quantities are real numbers and all functions are total: division by zero returns $0$, the logarithm satisfies $\ln 0 = 0$ and $\ln x = \ln|x|$ for $x<0$, and the square root of a negative number is $0$. Every theorem of the mission assumes $\gamma>1$ and positive densities and pressures (and positive normal velocities where relevant), so these junk values never enter the statements. The entropy is represented only through its jump divided by $c_v$, which is all the source uses.
-- source:
--   G. I. Ogilvie, *Astrophysical fluid dynamics* (lecture notes), J. Plasma Phys. 82 (2016) 205820301, https://doi.org/10.1017/S0022377816000489, §2.8 eq. (2.22) p. 9; §4.5 eq. (4.36) p. 24; §6.3.1–6.3.2 eqs. (6.27)–(6.31) pp. 37–39; §11.6.2 (entropy of a perfect gas); Example A.13 eqs. (A 22)–(A 28) pp. 89–90

import Mathlib

namespace AstrophysicalFluidDynamics

/-- Specific enthalpy of a perfect gas with adiabatic exponent `γ`, pressure `p` and density `ρ`:
`h = (γ / (γ - 1)) * (p / ρ)` (Ogilvie 2016, eq. (6.28)). -/
noncomputable def perfectGasEnthalpy (γ p ρ : ℝ) : ℝ :=
  γ / (γ - 1) * (p / ρ)

/-- Square of the adiabatic sound speed, `v_s² = γ p / ρ` (Ogilvie 2016, eq. (4.36)). -/
noncomputable def soundSpeedSq (γ p ρ : ℝ) : ℝ :=
  γ * p / ρ

/-- Adiabatic sound speed `v_s = (γ p / ρ)^{1/2}` (Ogilvie 2016, eq. (4.36)). -/
noncomputable def soundSpeed (γ p ρ : ℝ) : ℝ :=
  Real.sqrt (soundSpeedSq γ p ρ)

/-- Mach number `M = u_x / v_s` of a gas with normal velocity `u`, pressure `p`, density `ρ`
(Ogilvie 2016, eq. (6.29) and Example A.13). -/
noncomputable def machNumber (γ ρ u p : ℝ) : ℝ :=
  u / soundSpeed γ p ρ

/-- Specific internal (thermal) energy of a perfect gas, `e = p / ((γ - 1) ρ)`
(Ogilvie 2016, eq. (2.22)). -/
noncomputable def perfectGasInternalEnergy (γ p ρ : ℝ) : ℝ :=
  p / ((γ - 1) * ρ)

/-- The Rankine–Hugoniot relations (Ogilvie 2016, eqs. (6.27a–c), (A 22)–(A 24)) for a normal,
non-magnetic shock at rest at `x = 0` in a perfect gas with adiabatic exponent `γ`.
The upstream (pre-shock) state is `(ρ₁, u₁, p₁)` and the downstream (post-shock) state is
`(ρ₂, u₂, p₂)`, where `u` is the velocity component normal to the shock. The three conditions
are continuity of the mass flux `ρ u`, of the momentum flux `ρ u² + p`, and of the energy flux
`ρ u (u²/2 + h)` with `h` the perfect-gas enthalpy. -/
def RankineHugoniot (γ ρ₁ u₁ p₁ ρ₂ u₂ p₂ : ℝ) : Prop :=
  ρ₂ * u₂ = ρ₁ * u₁ ∧
  ρ₂ * u₂ ^ 2 + p₂ = ρ₁ * u₁ ^ 2 + p₁ ∧
  ρ₂ * u₂ * (u₂ ^ 2 / 2 + perfectGasEnthalpy γ p₂ ρ₂) =
    ρ₁ * u₁ * (u₁ ^ 2 / 2 + perfectGasEnthalpy γ p₁ ρ₁)

/-- Entropy jump across the shock divided by `c_v`, `[s]₁² / c_v = ln(p₂/p₁) - γ ln(ρ₂/ρ₁)`,
computed from the specific entropy of a perfect gas `s = c_p (γ⁻¹ ln p - ln ρ) + const`
(Ogilvie 2016, §11.6.2) together with `c_p = γ c_v` (eq. (2.17)). -/
noncomputable def entropyJumpOverCv (γ ρ₁ p₁ ρ₂ p₂ : ℝ) : ℝ :=
  Real.log (p₂ / p₁) - γ * Real.log (ρ₂ / ρ₁)

/-- Shock density (compression) ratio as a function of the upstream Mach number `M₁`,
`(γ + 1) M₁² / ((γ - 1) M₁² + 2)` (Ogilvie 2016, eq. (6.30a)). -/
noncomputable def shockDensityRatio (γ M₁ : ℝ) : ℝ :=
  (γ + 1) * M₁ ^ 2 / ((γ - 1) * M₁ ^ 2 + 2)

/-- Shock pressure ratio as a function of the upstream Mach number `M₁`,
`(2 γ M₁² - (γ - 1)) / (γ + 1)` (Ogilvie 2016, eq. (6.30b)). -/
noncomputable def shockPressureRatio (γ M₁ : ℝ) : ℝ :=
  (2 * γ * M₁ ^ 2 - (γ - 1)) / (γ + 1)

/-- Square of the downstream Mach number as a function of the upstream Mach number `M₁`,
`(2 + (γ - 1) M₁²) / (2 γ M₁² - (γ - 1))` (Ogilvie 2016, eq. (6.31)). -/
noncomputable def shockDownstreamMachSq (γ M₁ : ℝ) : ℝ :=
  (2 + (γ - 1) * M₁ ^ 2) / (2 * γ * M₁ ^ 2 - (γ - 1))

end AstrophysicalFluidDynamics


