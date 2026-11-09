-- Prove2me | Definitions.Def_GevreyGibbsSep_G14
-- name    : GevreyGibbsSep_G14
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:34:49.309606+00:00
-- url     : https://prove2.me/theorems/65ab2971-3adf-4116-a6ee-d10657525b9a
-- title:
--   Separation expression of Eq. (14)
-- statement:
--   The expression inside $\widetilde\Omega(\cdot)$ of the separation (14):
--   $$G_{14}(d,s,\alpha,\varepsilon)=\frac{\alpha^{c(d)}}{d^{\frac52+2s}\log^{s+2}\frac1\varepsilon},\qquad c(d)=\frac12-\frac1d .$$
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Eq. (14), p.7

import Mathlib

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- The expression inside `Ω̃(·)` in Eq. (14), p.7 of arXiv:2608.24527 (sha256 d4fd40eb…):
`α^{c(d)}/(d^{5/2 + 2s} log^{s+2}(1/ε))` with `c(d) = 1/2 − 1/d`. -/
noncomputable def G14 (d : ℕ) (s α ε : ℝ) : ℝ :=
  α ^ ((1 : ℝ) / 2 - 1 / d) / ((d : ℝ) ^ ((5 : ℝ) / 2 + 2 * s) * Real.log (1 / ε) ^ (s + 2))

end GevreyGibbsSep


