-- Prove2me | Definitions.Def_GevreyGibbsSep_F44
-- name    : GevreyGibbsSep_F44
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:34:52.853197+00:00
-- url     : https://prove2.me/theorems/6b54686e-08f2-4347-995d-7eb9d2e84a91
-- title:
--   Query-count expression of Eq. (44)
-- statement:
--   The expression inside $\widetilde O(\cdot)$ of Eq. (44):
--   $$F_{44}(d,s,\alpha,\varepsilon)=\alpha^{\frac12+\frac1d}\,d^{\frac52+s}\,(\log\alpha)^s\Big(d+\log\alpha+\log\frac1\varepsilon\Big)^s\log^2\frac1\varepsilon .$$
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Eq. (44), p.16

import Mathlib

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- The expression inside `Õ(·)` in Eq. (44), p.16 of arXiv:2608.24527 (sha256 d4fd40eb…):
`α^{1/2 + 1/d} d^{5/2 + s} (log α)^s (d + log α + log(1/ε))^s log²(1/ε)`. -/
noncomputable def F44 (d : ℕ) (s α ε : ℝ) : ℝ :=
  α ^ ((1 : ℝ) / 2 + 1 / d) * (d : ℝ) ^ ((5 : ℝ) / 2 + s) * Real.log α ^ s
    * (d + Real.log α + Real.log (1 / ε)) ^ s * Real.log (1 / ε) ^ 2

end GevreyGibbsSep


