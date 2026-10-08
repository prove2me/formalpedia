-- Prove2me | Definitions.Def_FVRPricing_DecayBalancing_Kappa
-- name    : FVRPricing_DecayBalancing_Kappa
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:45:07.993215+00:00
-- url     : https://prove2.me/theorems/502eafb2-d4ea-4160-b6ab-7dc084038595
-- title:
--   Incomplete Gamma function $\Gamma(s,y)$ and $\kappa(a)$
-- statement:
--   The **upper incomplete Gamma function** (p. 20) is
--   $$\Gamma(s,y) = \int_y^\infty t^{s-1} e^{-t}\,dt ,$$
--   and for $a>0$ the constant of Theorem 1 is
--   $$\kappa(a) = \frac{a\,\Gamma(a)}{\Gamma(a+1) - \Gamma(a+1,a) + a\,\Gamma(a,a)} .$$
--   Writing $u\sim\mathrm{Gamma}(a,1)$, one has $1/\kappa(a) = E[\min(u/a, 1)]$; for example $\kappa(1) = 1/(1-e^{-1}) \approx 1.582$.
--
--   $\kappa(a)$ measures how much a Gamma prior with shape $a$ (coefficient of variation $1/\sqrt a$) can cost relative to knowing the arrival rate; it controls the bounds of Theorem 1, Corollary 1, Theorem 2 and, through $\kappa(1)$, the constant $1/3$ of Theorem 3.
--
--   **Formalization Note** $\Gamma(\cdot)$ is `Real.Gamma`; $\Gamma(s,y)$ is a set integral over $(y,\infty)$ with the real power `t ^ (s - 1)`.
-- source:
--   Farias, Van Roy, Dynamic Pricing with a Prior on Market Response, manuscript of January 20, 2009 (sha256 a64048ac…), p. 20, Theorem 1 and the definition of Γ(·,·) after its proof

import Mathlib

namespace FVRPricing.DecayBalancing

/-- Upper incomplete Gamma function `Γ(s, y) = ∫_y^∞ t^{s−1} e^{−t} dt` (p. 20). -/
noncomputable def upperGamma (s y : ℝ) : ℝ := ∫ t in Set.Ioi y, t ^ (s - 1) * Real.exp (-t)

/-- `κ(a) = a Γ(a) / (Γ(a+1) − Γ(a+1, a) + a Γ(a, a))` (Theorem 1, p. 20). -/
noncomputable def kappa (a : ℝ) : ℝ :=
  a * Real.Gamma a / (Real.Gamma (a + 1) - upperGamma (a + 1) a + a * upperGamma a a)

end FVRPricing.DecayBalancing


