-- Prove2me | Definitions.Def_GevreyGibbsSep_F8
-- name    : GevreyGibbsSep_F8
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:34:45.575207+00:00
-- url     : https://prove2.me/theorems/d919a827-1b2d-4cca-b167-def9b904c505
-- title:
--   Query-count expression of Eq. (8)
-- statement:
--   The expression inside $\widetilde O(\cdot)$ of the quantum query count (8):
--   $$F_8(d,s,\alpha,\xi,\rho,\varepsilon)=\sqrt{\alpha d}\,\Big(1+\frac{d+\xi}{\rho}\Big[ds+\log\frac{\alpha(1+\xi/\rho)}{\varepsilon}\Big]^s\Big)\log^2\frac1\varepsilon ,$$
--   with natural logarithms; the radical covers $\alpha d$.
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Eq. (8), p.6; Eq. (24), p.11; Eq. (A89), p.33

import Mathlib

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- The expression inside `Õ(·)` in Eq. (8), p.6 (and (24), (A89)) of arXiv:2608.24527
(sha256 d4fd40eb…):
`√(αd) (1 + ((d + ξ)/ρ) [ds + log(α(1 + ξ/ρ)/ε)]^s) log²(1/ε)` (natural logarithms). -/
noncomputable def F8 (d : ℕ) (s α ξ ρ ε : ℝ) : ℝ :=
  Real.sqrt (α * d) * (1 + ((d + ξ) / ρ) * (d * s + Real.log (α * (1 + ξ / ρ) / ε)) ^ s)
    * Real.log (1 / ε) ^ 2

end GevreyGibbsSep


