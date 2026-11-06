-- Prove2me | Definitions.Def_MetricMinTest_Ddelta
-- name    : MetricMinTest_Ddelta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:05:16.167917+00:00
-- url     : https://prove2.me/theorems/04d8199d-918c-4ead-b7af-b7bf059d6b34
-- title:
--   $D_\delta=\mathrm{kl}(1-\delta,\delta)$
-- statement:
--   $D_\delta=\mathrm{kl}(1-\delta,\delta)=(1-2\delta)\ln\frac{1-\delta}{\delta}$, the binary relative entropy between Bernoulli laws of parameters $1-\delta$ and $\delta$. For $\delta\le1/4$ it is at least $\ln(1/\delta)/4$.
--
--   **Formalization Note** Uses the published binary relative entropy `LimitedPriceChanges.LowerBound.klBer` (natural logarithm).
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), §2, p.6

import Mathlib
import Definitions.Def_LimitedPriceChanges_LowerBound_KL

namespace MetricMinTest

/-- **`D_δ = kl(1 − δ, δ)`.** Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC
2027 submission (manuscript sha256 dcece193…ad32bb), §2, p.6:
`D_δ = kl(1 − δ, δ) = (1 − 2δ) ln((1 − δ)/δ)`.

**Formalization Note.** `kl` is the binary relative entropy (natural logarithm), the published
`LimitedPriceChanges.LowerBound.klBer`. -/
noncomputable def Ddelta (δ : ℝ) : ℝ :=
  LimitedPriceChanges.LowerBound.klBer (1 - δ) δ

end MetricMinTest


