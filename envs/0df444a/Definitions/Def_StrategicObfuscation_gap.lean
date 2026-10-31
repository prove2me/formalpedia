-- Prove2me | Definitions.Def_StrategicObfuscation_gap
-- name    : StrategicObfuscation_gap
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:50:07.337546+00:00
-- url     : https://prove2.me/theorems/d5019a31-d158-4d64-bfb5-87deec5e7e4d
-- title:
--   The function $f(\sigma)$ of the Claim
-- statement:
--   The function
--
--   $$f(\sigma)=[1-\pi(\sigma,0)]\,p\,(V-c)-[1-\pi(\sigma,e(1,\sigma))]\,(1-p)\,c$$
--
--   is the benefit minus the cost of funding uncertified proposals when effort is at its maximal level $e(1,\sigma)$. Inequality (3) at $e^*=e(1,\sigma)$ is $f(\sigma)>0$.
-- source:
--   Figueroa & Lemus, The Benefit of the Doubt: Decision Making under Strategic Obfuscation, SSRN 3840423 (version of April 4, 2022), proof of Proposition 1, Claim, p.27

import Mathlib

namespace StrategicObfuscation

/-- **The function `f(σ)` of the Claim: benefit minus cost of funding at maximal obfuscation.**
Figueroa & Lemus, *The Benefit of the Doubt: Decision Making under Strategic Obfuscation*,
SSRN 3840423 (version of April 4, 2022), proof of Proposition 1, Claim, p.27 (PDF p.27):
`f(σ) = [1 - π(σ, 0)] p (V - c) - [1 - π(σ, e*)] (1 - p) c`, where `e* = e(1, σ)`.

Inequality (3) at `e* = e(1, σ)` is `0 < f(σ)`. -/
def gap (π : ℝ → ℝ → ℝ) (V c p : ℝ) (E : ℝ → ℝ → ℝ) (σ : ℝ) : ℝ :=
  (1 - π σ 0) * p * (V - c) - (1 - π σ (E 1 σ)) * (1 - p) * c

end StrategicObfuscation


