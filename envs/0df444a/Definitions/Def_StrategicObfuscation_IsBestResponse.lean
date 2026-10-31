-- Prove2me | Definitions.Def_StrategicObfuscation_IsBestResponse
-- name    : StrategicObfuscation_IsBestResponse
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:50:03.718991+00:00
-- url     : https://prove2.me/theorems/3cc6c63f-7b87-4371-9626-d3b9562f2b55
-- title:
--   The applicant's best response (1)
-- statement:
--   Given the funding probability $\alpha$ of an uncertified proposal, the private return $g$ and the reviewer's resources $\sigma$, an effort $e$ is a **best response** when $e\ge 0$ and
--
--   $$e\in\arg\max_{e'\ge 0}\ \alpha\, g\,(1-\pi(\sigma,e'))-e'.$$
--
--   The proposal is uncertified with probability $1-\pi(\sigma,e')$, and the effort cost is $C(e')=e'$. This is the incentive constraint of an applicant with a bad idea.
--
--   **Formalization Note** This is membership in the argmax; it does not assert that a maximizer exists.
-- source:
--   Figueroa & Lemus, The Benefit of the Doubt: Decision Making under Strategic Obfuscation, SSRN 3840423 (version of April 4, 2022), eq. (1), p.10

import Mathlib

namespace StrategicObfuscation

/-- **The applicant's best response (1).**
Figueroa & Lemus, *The Benefit of the Doubt: Decision Making under Strategic Obfuscation*,
SSRN 3840423 (version of April 4, 2022), eq. (1), p.10 (PDF p.10).

`e` is a best response of an applicant with a bad idea when `e ≥ 0` maximizes
`α · g · (1 - π(σ, e')) - e'` over `e' ≥ 0`, where `α` is the funding probability of an uncertified
proposal, `g` the applicant's private return and the effort cost is `C(e) = e`.

**Formalization Note** This is membership in the argmax of (1); it does not assert that a maximizer
exists. -/
def IsBestResponse (π : ℝ → ℝ → ℝ) (g α σ e : ℝ) : Prop :=
  0 ≤ e ∧ ∀ e', 0 ≤ e' → α * g * (1 - π σ e') - e' ≤ α * g * (1 - π σ e) - e

end StrategicObfuscation


