-- Prove2me | Definitions.Def_BeatingGV42_aGV
-- name    : BeatingGV42_aGV
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:32:22.455911+00:00
-- url     : https://prove2.me/theorems/7915a629-695f-4897-8406-d9764970cbed
-- title:
--   The degree fraction $a_{GV}(\delta)$
-- statement:
--   For $\delta\in I=[0.39,0.48]$,
--   $$
--   a_{GV}(\delta)=\frac76-\frac{h(\delta)+\delta\ln 41}{\ln 49},
--   $$
--   with $h(\delta)=-\delta\ln\delta-(1-\delta)\ln(1-\delta)$. It is chosen so that the rate $R(a_{GV}(\delta))$ of Proposition 4.9 at $Q=49$, $q=42$ equals the GV rate $1-H_{42}(\delta)$.
--
--   **Formalization Note** `aGV δ`, the same expression on all of $\mathbb R$; $h$ is Mathlib's `Real.binEntropy`.
-- source:
--   Cohen, Manket, Beating the Gilbert–Varshamov Bound at Alphabet Size 42, manuscript of October 24, 2026 (STOC 2027 submission; held version sha256 da05fc8e…eb595), §4.5, p.23 (PDF p.25)

import Mathlib

set_option autoImplicit false

namespace BeatingGV42

/-- **The GV-matching degree fraction** `a_GV(δ) := 7/6 − (h(δ) + δ ln 41)/ln 49`
(Cohen, Manket, *Beating the Gilbert–Varshamov Bound at Alphabet Size 42*, manuscript of October 24, 2026 (held version sha256 da05fc8e…), §4.5, p.23 (PDF p.25)), chosen so that `R(a_GV(δ)) = 1 − H_42(δ)`.

**Formalization Note** `h` is Mathlib's `Real.binEntropy` (natural logarithm). The paper defines
`a_GV` for `δ ∈ I = [0.39, 0.48]`; the Lean function is the same expression on all of `ℝ`. -/
noncomputable def aGV (δ : ℝ) : ℝ :=
  7 / 6 - (Real.binEntropy δ + δ * Real.log 41) / Real.log 49

end BeatingGV42


