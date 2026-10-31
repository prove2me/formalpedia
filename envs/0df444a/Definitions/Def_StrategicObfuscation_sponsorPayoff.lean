-- Prove2me | Definitions.Def_StrategicObfuscation_sponsorPayoff
-- name    : StrategicObfuscation_sponsorPayoff
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:50:01.973008+00:00
-- url     : https://prove2.me/theorems/8fac4eb2-3935-44d4-9af4-0a583d478eb0
-- title:
--   Sponsor's expected payoff $u_S$
-- statement:
--   The sponsor's expected payoff at resources $\sigma$, funding probability $\alpha$ and effort $e$ is
--
--   $$u_S=p\,\pi(\sigma,0)(V-c)+\alpha\bigl[p(1-\pi(\sigma,0))(V-c)-(1-p)(1-\pi(\sigma,e))c\bigr].$$
--
--   The first term is the surplus from good ideas that are certified; the bracket is the net gain from funding uncertified proposals.
-- source:
--   Figueroa & Lemus, The Benefit of the Doubt: Decision Making under Strategic Obfuscation, SSRN 3840423 (version of April 4, 2022), §3.1, display before Proposition 2, p.13

import Mathlib

namespace StrategicObfuscation

/-- **The sponsor's expected payoff `u_S`.**
Figueroa & Lemus, *The Benefit of the Doubt: Decision Making under Strategic Obfuscation*,
SSRN 3840423 (version of April 4, 2022), §3.1, display before Proposition 2, p.13 (PDF p.13):
`u_S = p π(σ, 0)(V - c) + α [p (1 - π(σ, 0))(V - c) - (1 - p)(1 - π(σ, e)) c]`. -/
def sponsorPayoff (π : ℝ → ℝ → ℝ) (V c p σ α e : ℝ) : ℝ :=
  p * π σ 0 * (V - c) + α * (p * (1 - π σ 0) * (V - c) - (1 - p) * (1 - π σ e) * c)

end StrategicObfuscation


