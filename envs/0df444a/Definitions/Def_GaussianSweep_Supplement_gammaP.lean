-- Prove2me | Definitions.Def_GaussianSweep_Supplement_gammaP
-- name    : GaussianSweep_Supplement_gammaP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:35:04.316493+00:00
-- url     : https://prove2.me/theorems/e5ba7808-c956-4a24-9f94-26e477e380a4
-- title:
--   The cut-sweep constant $\gamma_p = \arccos(r_{pp})/\pi$
-- statement:
--   For an integer $p \ge 3$,
--   $$
--   \gamma_p = \frac{\arccos r_{pp}}{\pi}, \qquad r_{pp} = \frac{2\sqrt{p-1}}{p},
--   $$
--   so that $\gamma_3 = \tfrac23 c^* \approx 0.10817$, $\gamma_4 = 1/6$ and $\gamma_5 < 0.20484$. It is the per-edge coefficient of the cut sweep for maximum degree $p$.
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Section 3.5, p.20 (PDF p.22)

import Mathlib
import Definitions.Def_GaussianSweep_Supplement_rpp

namespace GaussianSweep.Supplement

/-- The cut-sweep constant `γ_p = arccos(r_pp)/π` for maximum degree `p`
(Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Section 3.5, p.20 (PDF p.22)); `γ₃ = (2/3)c*`, `γ₄ = 1/6`,
`γ₅ < 0.20484`. -/
noncomputable def gammaP (p : ℕ) : ℝ := Real.arccos (rpp p) / Real.pi

end GaussianSweep.Supplement


