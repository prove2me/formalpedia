-- Prove2me | Definitions.Def_MetricMinTest_Supplement_ballCoverCost
-- name    : MetricMinTest_Supplement_ballCoverCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:29:55.850985+00:00
-- url     : https://prove2.me/theorems/e4fa18cc-7ae6-4b62-bec5-84554eae5266
-- title:
--   Cost $C(y)=\sum_{j,\ell}y_{j\ell}a_{j\ell}^{-2}$ of a ball cover
-- statement:
--   The **cost** of a weighting $y$ of the indexed balls is
--   $$C(y)=\sum_{j,\ell}y_{j\ell}\,a_{j\ell}^{-2},\qquad a_{j\ell}=\gamma-r_{j\ell}.$$
--   The certificate workload $F_d(\gamma)$ is its minimum over fractional ball covers.
--
--   **Formalization Note** Same pair encoding of indexed balls as the published certificate workload.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), (2.1), p.6

import Mathlib

namespace MetricMinTest.Supplement

/-- **Cost `C(y) = ∑_{j,ℓ} y_{jℓ} a_{jℓ}⁻²` of a ball cover** (program (2.1)). Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), (2.1), p.6.

**Formalization Note.** Indexed-ball encoding of the published `certWorkload`: pairs `(j, i)` with
`d j i < γ`, gap `a = γ − d j i`. -/
noncomputable def ballCoverCost {ι : Type} [Fintype ι] (d : ι → ι → ℝ) (γ : ℝ) (y : ι × ι → ℝ) :
    ℝ :=
  ∑ p ∈ Finset.univ.filter (fun p : ι × ι => d p.1 p.2 < γ), y p * ((γ - d p.1 p.2) ^ 2)⁻¹

end MetricMinTest.Supplement


