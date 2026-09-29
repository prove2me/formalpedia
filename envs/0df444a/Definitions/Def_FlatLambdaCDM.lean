-- Prove2me | Definitions.Def_FlatLambdaCDM
-- name    : FlatLambdaCDM
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-21T02:24:11.852993+00:00
-- url     : https://prove2.me/theorems/c20aaf79-9009-4a62-be94-9f27046ff925
-- title:
--   Flat ΛCDM parameters, scale factor $a(t)$ and age $t_0$
-- statement:
--   The model bundle for the minimal spatially flat, radiation-free ΛCDM cosmology.
--
--   A parameter record carries a present-day Hubble constant $H_0>0$, a matter density parameter $\Omega_m>0$ and a dark-energy density parameter $\Omega_\Lambda>0$, constrained by the flatness relation $\Omega_m+\Omega_\Lambda=1$.
--
--   From these are built the dimensionless time variable
--   $$\theta(t)=\tfrac32\sqrt{\Omega_\Lambda}\,H_0\,t,$$
--   the closed-form scale factor
--   $$a(t)=\left(\frac{\Omega_m}{\Omega_\Lambda}\right)^{1/3}\sinh^{2/3}\theta(t),$$
--   with both exponents understood as real powers, and the age
--   $$t_0=\frac{2}{3H_0\sqrt{\Omega_\Lambda}}\operatorname{arsinh}\sqrt{\frac{\Omega_\Lambda}{\Omega_m}}.$$
--   Time is measured from the big bang at $t=0$; the formulas are intended for $t>0$, where $\sinh\theta(t)>0$.
-- source:
--   Wikipedia, Lambda-CDM model, https://en.wikipedia.org/wiki/Lambda-CDM_model, section 'Cosmic expansion history' (Friedmann equation in density parameters, closed-form solution a(t), age t0, deceleration-to-acceleration transition)

import Mathlib

namespace LambdaCDM

/-- Parameters of the minimal, spatially flat, radiation-free ΛCDM model:
a present-day Hubble constant `H0`, a present-day matter density parameter `Om`
and a dark-energy density parameter `OL` summing to one (zero spatial curvature). -/
structure FlatLCDM where
  /-- The present-day Hubble constant `H₀`. -/
  H0 : ℝ
  /-- The present-day matter density parameter `Ω_m`. -/
  Om : ℝ
  /-- The dark-energy density parameter `Ω_Λ`. -/
  OL : ℝ
  H0_pos : 0 < H0
  Om_pos : 0 < Om
  OL_pos : 0 < OL
  flat : Om + OL = 1

/-- The dimensionless time variable `θ(t) = (3/2) √Ω_Λ H₀ t`. -/
noncomputable def theta (P : FlatLCDM) (t : ℝ) : ℝ :=
  3 / 2 * Real.sqrt P.OL * P.H0 * t

/-- The closed-form ΛCDM scale factor
`a(t) = (Ω_m/Ω_Λ)^(1/3) * sinh (θ t) ^ (2/3)`, with real exponents. -/
noncomputable def scaleFactor (P : FlatLCDM) (t : ℝ) : ℝ :=
  (P.Om / P.OL) ^ ((1 : ℝ) / 3) * Real.sinh (theta P t) ^ ((2 : ℝ) / 3)

/-- The present age of the universe
`t₀ = 2/(3 H₀ √Ω_Λ) * arsinh √(Ω_Λ/Ω_m)`. -/
noncomputable def age (P : FlatLCDM) : ℝ :=
  2 / (3 * P.H0 * Real.sqrt P.OL) * Real.arsinh (Real.sqrt (P.OL / P.Om))

end LambdaCDM


