-- Prove2me | Definitions.Def_MetricMinTest_Supplement_certCoverCost
-- name    : MetricMinTest_Supplement_certCoverCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:36:16.299359+00:00
-- url     : https://prove2.me/theorems/d4ac5b07-2d27-40df-a304-ba4aadd52a14
-- title:
--   Cost $C(y)=\sum_cy_c\eta_c^{-2}$ of a certificate cover
-- statement:
--   For gaps $\eta_c\in(0,2]$, the **cost** of a weighting $y$ of the certificates is $C(y)=\sum_cy_c\,\eta_c^{-2}$.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Definition K.1, p.32

import Mathlib

namespace MetricMinTest.Supplement

/-- **Cost `C(y) = ∑_c y_c η_c⁻²` of a certificate cover** (Definition K.1). Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb),
Definition K.1, p.32. -/
noncomputable def certCoverCost {C : Type} [Fintype C] (η y : C → ℝ) : ℝ :=
  ∑ c, y c * (η c ^ 2)⁻¹

end MetricMinTest.Supplement


