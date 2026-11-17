-- Prove2me | Definitions.Def_GraphNNSphere_Supplement_etaStarDense
-- name    : GraphNNSphere_Supplement_etaStarDense
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:45:48.026491+00:00
-- url     : https://prove2.me/theorems/0292c867-e17f-4475-b4f0-378e21565e47
-- title:
--   Fresh-start exponent $\eta^*(\gamma)$ and the dense near-threshold band
-- statement:
--   For the dense regime define
--
--   $$\eta^*(\gamma)=-\frac12\log\left(1-\frac{(2-e^{2\gamma})^2(3e^{2\gamma}-2)^2}{16e^{4\gamma}(e^{2\gamma}-1)}\right),$$
--
--   and the **near-threshold band** $\tfrac12\log(4/3)\le\gamma<\gamma_c$, $\gamma_c=\tfrac12\log2$. In the band, one greedy run from a uniform random entry succeeds with probability $e^{-(\eta^*(\gamma)+o(1))d}$, and $\eta^*$ governs the cost of fresh starts (Theorems 5.1, 5.3, 5.6, 5.9).
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), Eq. (50), p.54; §5.2, p.60

import Mathlib
import Definitions.Def_GraphNNSphere_gammaC

namespace GraphNNSphere

namespace Supplement

/-- The fresh-start exponent of the dense regime,
`η*(γ) = -½ log(1 - (2 - e^{2γ})²(3e^{2γ} - 2)²/(16 e^{4γ}(e^{2γ} - 1)))`
(Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), Eq. (50), p.54). -/
noncomputable def etaStarDense (γ : ℝ) : ℝ :=
  -(Real.log (1 - (2 - Real.exp (2 * γ)) ^ 2 * (3 * Real.exp (2 * γ) - 2) ^ 2 /
      (16 * Real.exp (4 * γ) * (Real.exp (2 * γ) - 1))) / 2)

/-- The near-threshold band of the dense regime, `½ log(4/3) ≤ γ < γ_c`
(Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §5.2, p.60). -/
def InBandDense (γ : ℝ) : Prop := Real.log (4 / 3) / 2 ≤ γ ∧ γ < gammaC

end Supplement

end GraphNNSphere


