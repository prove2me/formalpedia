-- Prove2me | Definitions.Def_StrategicObfuscation_equilibriumPayoff
-- name    : StrategicObfuscation_equilibriumPayoff
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:51:07.320365+00:00
-- url     : https://prove2.me/theorems/664e60fb-6b21-46d2-998e-1b3676d5f260
-- title:
--   Sponsor's equilibrium payoff as a function of $\sigma$
-- statement:
--   Given a family $\alpha^*(\sigma)$, this is the function $\sigma\mapsto u_S(\sigma,\alpha^*(\sigma),e^*(\sigma))$, the object of Proposition 2 and of Figure 4.
-- source:
--   Figueroa & Lemus, The Benefit of the Doubt: Decision Making under Strategic Obfuscation, SSRN 3840423 (version of April 4, 2022), §3.1, display before Proposition 2, p.13, and Figure 4, p.14

import Mathlib
import Definitions.Def_StrategicObfuscation_sponsorPayoff
import Definitions.Def_StrategicObfuscation_equilibriumEffort

namespace StrategicObfuscation

/-- **The sponsor's equilibrium payoff as a function of `σ`.**
Figueroa & Lemus, *The Benefit of the Doubt: Decision Making under Strategic Obfuscation*,
SSRN 3840423 (version of April 4, 2022), §3.1, display before Proposition 2, p.13 (PDF p.13), with
`α* = αS σ` and `e* = e(αS σ, σ)`. This is the function drawn in Figure 4, p.14 (PDF p.14). -/
def equilibriumPayoff (π : ℝ → ℝ → ℝ) (V c p : ℝ) (E : ℝ → ℝ → ℝ) (αS : ℝ → ℝ) (σ : ℝ) : ℝ :=
  sponsorPayoff π V c p σ (αS σ) (equilibriumEffort E αS σ)

end StrategicObfuscation


