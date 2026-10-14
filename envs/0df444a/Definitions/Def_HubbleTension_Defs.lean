-- Prove2me | Definitions.Def_HubbleTension_Defs
-- name    : HubbleTension_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-12T21:21:12.132977+00:00
-- url     : https://prove2.me/theorems/809a2bc6-f27f-4402-b1be-5c309722f199
-- title:
--   Hubble-tension toolkit: quadrature, σ-tension, distance modulus, Hubble's law
-- statement:
--   Definitions shared by the mission:
--   - $\mathrm{quadSum}(s,t)=\sqrt{s^2+t^2}$, the combination in quadrature of two independent uncertainties (e.g. stat and sys);
--   - $\mathrm{tension}(a,\sigma_a,b,\sigma_b)=|a-b|/\mathrm{quadSum}(\sigma_a,\sigma_b)$, the discrepancy between independent measurements $a\pm\sigma_a$ and $b\pm\sigma_b$ in standard deviations;
--   - $\mathrm{distanceModulus}(d)=5\log_{10}(d/10)$ for a distance $d$ in parsecs;
--   - $\mathrm{distanceFromModulus}(\mu)=10^{\mu/5+1}$ parsecs;
--   - $\mathrm{hubbleConstant}(v,d)=v/(d/10^6)$, Hubble's law $H_0=v/d$ with $v$ in km/s and $d$ given in parsecs (converted to Mpc).
-- source:
--   W. L. Freedman and B. F. Madore, Progress in Direct Measurements of the Hubble Constant, JCAP (2023), arXiv:2309.05618v2, https://arxiv.org/abs/2309.05618, §§1, 4.1, 5, 10 (standard conventions of the field)

import Mathlib

/-!
# Definitions for the Hubble-tension mission
Source: W. L. Freedman and B. F. Madore, *Progress in Direct Measurements of the Hubble
Constant*, arXiv:2309.05618v2 (2023).
-/

namespace HubbleTension

/-- Combination in quadrature of two independent uncertainties (e.g. a statistical and a
systematic error quoted as `x ± s (stat) ± t (sys)`): `√(s² + t²)`. -/
noncomputable def quadSum (s t : ℝ) : ℝ := Real.sqrt (s ^ 2 + t ^ 2)

/-- The tension, in units of standard deviations ("σ"), between two independent measurements
`a ± σa` and `b ± σb`: `|a - b| / √(σa² + σb²)`. -/
noncomputable def tension (a σa b σb : ℝ) : ℝ := |a - b| / quadSum σa σb

/-- The distance modulus `μ = 5 log₁₀ (d / 10 pc)` of an object at distance `d` parsecs
(meaningful for `d > 0`). -/
noncomputable def distanceModulus (d : ℝ) : ℝ := 5 * Real.logb 10 (d / 10)

/-- The distance in parsecs corresponding to a distance modulus `μ`: `d = 10^(μ/5 + 1)`. -/
noncomputable def distanceFromModulus (μ : ℝ) : ℝ := (10 : ℝ) ^ (μ / 5 + 1)

/-- Hubble's law `v = H₀ d`: the Hubble constant (in km s⁻¹ Mpc⁻¹) inferred from a recession
velocity `v` (km s⁻¹) and a distance `d` in parsecs, i.e. `H₀ = v / (d / 10⁶)`. -/
noncomputable def hubbleConstant (v d : ℝ) : ℝ := v / (d / 1e6)

end HubbleTension


