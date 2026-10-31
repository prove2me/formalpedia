-- Prove2me | Definitions.Def_StrategicObfuscation_SolvesFour
-- name    : StrategicObfuscation_SolvesFour
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:50:05.287249+00:00
-- url     : https://prove2.me/theorems/092ace0f-5682-4a89-83e4-4f8e6dad9544
-- title:
--   Equation (4): the indifference condition for $\alpha^*$
-- statement:
--   A funding probability $\alpha$ **solves (4)** at $\sigma$ when
--
--   $$c\,\bigl[(1-\pi(\sigma,0))p+(1-\pi(\sigma,e(\alpha,\sigma)))(1-p)\bigr]=V\,(1-\pi(\sigma,0))p,$$
--
--   that is, when the posterior induced by the effort $e(\alpha,\sigma)$ equals $c/V$.
--
--   **Formalization Note** Cross-multiplied, so that it keeps a meaning where the denominator of (4) vanishes.
-- source:
--   Figueroa & Lemus, The Benefit of the Doubt: Decision Making under Strategic Obfuscation, SSRN 3840423 (version of April 4, 2022), Proposition 1, part 3, eq. (4), p.11

import Mathlib

namespace StrategicObfuscation

/-- **Equation (4): the funding probability that makes the sponsor indifferent.**
Figueroa & Lemus, *The Benefit of the Doubt: Decision Making under Strategic Obfuscation*,
SSRN 3840423 (version of April 4, 2022), Proposition 1, part 3, eq. (4), p.11 (PDF p.11):
`(1 - π(σ, 0)) p / ((1 - π(σ, 0)) p + (1 - π(σ, e(α, σ))) (1 - p)) = c / V`.

**Formalization Note** Cross-multiplied, so that it keeps its meaning at `σ = 1` where the
denominator can vanish; whenever the denominator and `V` are nonzero this is (4). -/
def SolvesFour (π : ℝ → ℝ → ℝ) (V c p : ℝ) (E : ℝ → ℝ → ℝ) (σ α : ℝ) : Prop :=
  c * ((1 - π σ 0) * p + (1 - π σ (E α σ)) * (1 - p)) = V * ((1 - π σ 0) * p)

end StrategicObfuscation


