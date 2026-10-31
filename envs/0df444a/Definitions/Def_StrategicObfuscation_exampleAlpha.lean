-- Prove2me | Definitions.Def_StrategicObfuscation_exampleAlpha
-- name    : StrategicObfuscation_exampleAlpha
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:50:26.873981+00:00
-- url     : https://prove2.me/theorems/d65de7fe-9670-4090-8053-1de9b45dd99e
-- title:
--   The funding probability of the worked example
-- statement:
--   At $g=1$, $V=6$, $c=1$, $p=1/2$: $\alpha^*(\sigma)=1$ for $\sigma\le 2\sqrt 2-2$, and $\alpha^*(\sigma)=(4-4\sigma)/\sigma^2$ for larger $\sigma$, which solves (4).
--
--   **Formalization Note** This closed form is not printed, and the parameters $V=6$, $c=1$, $p=1/2$ are chosen here because the page fixes none.
-- source:
--   Figueroa & Lemus, The Benefit of the Doubt: Decision Making under Strategic Obfuscation, SSRN 3840423 (version of April 4, 2022), Figure 2, p.12, and eq. (4), p.11, for the π of §3.1, p.14

import Mathlib

namespace StrategicObfuscation

/-- **The funding probability in the worked example at `g = 1`, `V = 6`, `c = 1`, `p = 1/2`.**
Figueroa & Lemus, *The Benefit of the Doubt: Decision Making under Strategic Obfuscation*,
SSRN 3840423 (version of April 4, 2022), Figure 2, p.12 (PDF p.12) and eq. (4), p.11 (PDF p.11),
for the `π` of §3.1, p.14 (PDF p.14).

`α*(σ) = 1` for `σ ≤ σ̄2 = 2√2 - 2`, and above it `α*(σ) = (4 - 4σ) / σ²` solves (4).

**Formalization Note** This closed form is not printed, and the parameters `V = 6`, `c = 1`,
`p = 1/2` are chosen here because the page fixes none; `g = 1` is what gives the printed `0.5`. -/
noncomputable def exampleAlpha (σ : ℝ) : ℝ :=
  if σ ≤ 2 * Real.sqrt 2 - 2 then 1 else (4 - 4 * σ) / σ ^ 2

end StrategicObfuscation


