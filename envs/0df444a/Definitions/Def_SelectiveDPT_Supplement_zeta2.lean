-- Prove2me | Definitions.Def_SelectiveDPT_Supplement_zeta2
-- name    : SelectiveDPT_Supplement_zeta2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:27:06.101823+00:00
-- url     : https://prove2.me/theorems/6470d3b0-552e-429d-9446-36e9ec4179d3
-- title:
--   Boolean conversion loss $\zeta_2(\varepsilon)$
-- statement:
--   For $\varepsilon \in [0, 1/2)$ the **Boolean conversion loss** is
--   $$\zeta_2(\varepsilon) = \frac{1 - 2\sqrt{\varepsilon(1-\varepsilon)}}{\ln\!\big(1 + \tfrac{9}{10}(\sqrt{1-\varepsilon} - 1/\sqrt2)^2\big)} .$$
--   It is the factor lost when a negative-weights adversary bound for a Boolean function is converted into a multiplicative adversary bound with $\lambda = 19/10$ and $\eta = 1/2$ (Theorem 3.6), and is plotted in Fig. 3 of the paper.
--
--   **Formalization Note** At $\varepsilon = 1/2$ the denominator vanishes and Lean's convention $x/0 = 0$ applies; Theorem 3.6 only uses $\varepsilon < 1/2$.
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, Theorem 3.6 part 3, p.24; Fig. 3

import Mathlib

namespace SelectiveDPT.Supplement

/-- The Boolean conversion loss
`ζ₂(ε) = (1 − 2√(ε(1 − ε))) / ln(1 + 9(√(1 − ε) − 1/√2)²/10)` of Theorem 3.6
(arXiv:2609.26678, Theorem 3.6 part 3, p.24; plotted in Fig. 3).

**Formalization Note.** `ln` is `Real.log`; at `ε = 1/2` the denominator is `ln 1 = 0` and Lean's
`x / 0 = 0` applies, a value Theorem 3.6 (`ε < 1/2`) never uses. -/
noncomputable def zeta2 (ε : ℝ) : ℝ :=
  (1 - 2 * Real.sqrt (ε * (1 - ε))) /
    Real.log (1 + 9 * (Real.sqrt (1 - ε) - 1 / Real.sqrt 2) ^ 2 / 10)

end SelectiveDPT.Supplement


