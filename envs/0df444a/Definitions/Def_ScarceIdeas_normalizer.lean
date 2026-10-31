-- Prove2me | Definitions.Def_ScarceIdeas_normalizer
-- name    : ScarceIdeas_normalizer
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:14:07.55977+00:00
-- url     : https://prove2.me/theorems/808ea9b2-6375-4fa9-926a-ef5ee6280cc3
-- title:
--   Posterior normalizer $Z(\phi)=\int_0^\infty h_0(\lambda)e^{-\lambda\phi}d\lambda$
-- statement:
--   For a state $\phi$ (the cumulative innovation incentive offered so far),
--
--   $$Z(\phi)=\int_0^\infty h_0(\lambda)\,e^{-\lambda\phi}\,d\lambda$$
--
--   is the denominator of the posterior $h_\phi(\lambda)=h_0(\lambda)e^{-\lambda\phi}/Z(\phi)$ of (12): the prior probability that no viable idea has arrived by the time the incentive reaches $\phi$.
-- source:
--   Basov, Erkal, Minehart, Scotchmer, Scarcity of Ideas and Optimal R&D Policy, SSRN 4628270, §4.1, (12), p.18

import Mathlib

namespace ScarceIdeas

/-- **Normalizing constant of the posterior `h_ϕ`.**
Basov, Erkal, Minehart, Scotchmer, *Scarcity of Ideas and Optimal R&D Policy*, SSRN 4628270,
§4.1, (12), p.18: the denominator of
`h_ϕ(λ) = h0(λ) e^{−λϕ} / ∫_0^∞ h0(λ′) e^{−λ′ϕ} dλ′`.

$$Z(\phi)=\int_0^\infty h_0(\lambda)\,e^{-\lambda\phi}\,d\lambda .$$

For a given `λ`, `e^{−λϕ}` is the probability that no viable idea has arrived when the cumulative
innovation incentive is `ϕ` ((1), p.12), so `Z(ϕ)` is the prior probability of that event.

**Formalization Note** Integral over `Ioi 0` (the arrival rate is `lam`). -/
noncomputable def normalizer (h0 : ℝ → ℝ) (ϕ : ℝ) : ℝ :=
  ∫ lam in Set.Ioi 0, h0 lam * Real.exp (-lam * ϕ)

end ScarceIdeas


