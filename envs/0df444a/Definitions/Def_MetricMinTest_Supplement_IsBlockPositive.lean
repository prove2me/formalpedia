-- Prove2me | Definitions.Def_MetricMinTest_Supplement_IsBlockPositive
-- name    : MetricMinTest_Supplement_IsBlockPositive
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:34:49.086494+00:00
-- url     : https://prove2.me/theorems/2e726692-dba3-45d7-85f5-1729c9317e74
-- title:
--   Positive instances with block margins $\gamma_C$
-- statement:
--   In the known-block model, an instance must be accepted when $\mu_i\ge\gamma_C$ for every $i\in C$ and every block $C$ ("validity is understood with block-dependent margins").
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Appendix H, p.29

import Mathlib
import Definitions.Def_MetricMinTest_Instance_mean

namespace MetricMinTest.Supplement

/-- **Positive instances with block-dependent margins** (Appendix H). Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Appendix H, p.29:
"acceptance [is required] when µᵢ ≥ γ_C for every i ∈ C and every block C". -/
def IsBlockPositive {ι β : Type} (blk : ι → β) (γC : β → ℝ) (P : Instance ι) : Prop :=
  ∀ i, γC (blk i) ≤ P.mean i

end MetricMinTest.Supplement


