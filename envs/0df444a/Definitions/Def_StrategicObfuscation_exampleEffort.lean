-- Prove2me | Definitions.Def_StrategicObfuscation_exampleEffort
-- name    : StrategicObfuscation_exampleEffort
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:50:21.955238+00:00
-- url     : https://prove2.me/theorems/2ab5604d-4330-4fed-9659-04fb00bf8230
-- title:
--   The solution $e(\alpha,\sigma)=(\alpha\sigma)^2/2$ of (1) in the worked example
-- statement:
--   For $\pi(\sigma,e)=\sigma q(e)$ and $g=1$, the first-order condition of (1) gives $e(\alpha,\sigma)=(\alpha\sigma)^2/2$.
--
--   **Formalization Note** This closed form is not printed in the paper.
-- source:
--   Figueroa & Lemus, The Benefit of the Doubt: Decision Making under Strategic Obfuscation, SSRN 3840423 (version of April 4, 2022), eq. (1), p.10, for the π of §3.1, p.14

import Mathlib

namespace StrategicObfuscation

/-- **The solution of (1) in the worked example at `g = 1`, `e(α, σ) = (α σ)² / 2`.**
Figueroa & Lemus, *The Benefit of the Doubt: Decision Making under Strategic Obfuscation*,
SSRN 3840423 (version of April 4, 2022), eq. (1), p.10 (PDF p.10), for the `π` of §3.1, p.14
(PDF p.14).

**Formalization Note** This closed form is not printed. It is the first-order condition of (1) for
`π(σ, e) = σ q(e)` with `g = 1`. -/
noncomputable def exampleEffort (α σ : ℝ) : ℝ :=
  (α * σ) ^ 2 / 2

end StrategicObfuscation


