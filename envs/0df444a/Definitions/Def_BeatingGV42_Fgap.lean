-- Prove2me | Definitions.Def_BeatingGV42_Fgap
-- name    : BeatingGV42_Fgap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:32:23.264132+00:00
-- url     : https://prove2.me/theorems/503c49c1-734e-4ae5-8b8d-0da876742cab
-- title:
--   The function $F(\delta)$ of §4.5
-- statement:
--   For real $\delta$,
--   $$
--   F(\delta)=h(\delta)+\delta\ln 41-\frac{49\delta+7}{48}\ln 49 .
--   $$
--   The $t$-derivative of $\Psi_{a_{GV}(\delta),42}(t,\delta)$ at $t=1/49$ is $(49/\ln 49)F(\delta)$, so positivity of $F$ on $I$ means that a slightly smaller $t$ makes the exponent negative.
--
--   **Formalization Note** Named `Fgap` because $F$ denotes the function field; $h$ is Mathlib's `Real.binEntropy`.
-- source:
--   Cohen, Manket, Beating the Gilbert–Varshamov Bound at Alphabet Size 42, manuscript of October 24, 2026 (STOC 2027 submission; held version sha256 da05fc8e…eb595), §4.5, p.24 (PDF p.26)

import Mathlib

set_option autoImplicit false

namespace BeatingGV42

/-- **The function `F(δ) := h(δ) + δ ln 41 − ((49δ + 7)/48) ln 49`** (Cohen, Manket, *Beating the Gilbert–Varshamov Bound at Alphabet Size 42*, manuscript of October 24, 2026 (held version sha256 da05fc8e…), §4.5, p.24 (PDF p.26));
`(49/ln 49) F(δ)` is the `t`-derivative of `Ψ_{a_GV(δ),42}(t, δ)` at `t = 1/49`.

**Formalization Note** Named `Fgap` because `F` denotes the function field. `h` is Mathlib's
`Real.binEntropy`. -/
noncomputable def Fgap (δ : ℝ) : ℝ :=
  Real.binEntropy δ + δ * Real.log 41 - (49 * δ + 7) / 48 * Real.log 49

end BeatingGV42


