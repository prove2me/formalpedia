-- Prove2me | Definitions.Def_MetricMinTest_corrPsi
-- name    : MetricMinTest_corrPsi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:06:38.710128+00:00
-- url     : https://prove2.me/theorems/828388b9-cb13-4f47-b1c0-dbb20bdfcb7a
-- title:
--   Correlation profile $\Psi$, display (4.2)
-- statement:
--   The correlation profile of a gap profile is
--   $$\Psi(u)=\frac1k\sum_{s=0}^m v_s\big(e^{uK_s}-1\big),\qquad u\ge0,$$
--   with $k=b^m$. It depends only on the gap profile and governs the lower bound for nonadaptive testers (Theorem 4.5).
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Eq. (4.2), p.9

import Mathlib
import Definitions.Def_MetricMinTest_levCount
import Definitions.Def_MetricMinTest_corrK

namespace MetricMinTest

/-- **Correlation profile `Ψ`**, display (4.2). Chen–Fang, *Minimum-Mean Testing under Metric
Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), (4.2), p.9:
`Ψ(u) = (1/k) ∑_{s=0}^m v_s (e^{u K_s} − 1)`, `u ≥ 0`, with `k = b^m`. -/
noncomputable def corrPsi (b m : ℕ) (g : ℕ → ℝ) (u : ℝ) : ℝ :=
  1 / (b : ℝ) ^ m * ∑ s ∈ Finset.range (m + 1), levCount b s * (Real.exp (u * corrK b m g s) - 1)

end MetricMinTest


