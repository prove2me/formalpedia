-- Prove2me | Definitions.Def_KuhnWass2019_Reformulation_infinityWorstCaseRisk
-- name    : KuhnWass2019_Reformulation_infinityWorstCaseRisk
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T03:14:55.32454+00:00
-- url     : https://prove2.me/theorems/d6bfc02f-7b98-4f68-8326-da92ec4eed5e
-- title:
--   Worst-case risk over the type-infinity Wasserstein ball
-- statement:
--   The type-infinity risk is the supremum of the extended expectation of $\ell$ over all probability laws $Q$ supported on $\Xi$ whose infinity-Wasserstein distance from $P_N$ is at most $\varepsilon$. This distance uses the published maximum-cost primitive: the infimum, over probability couplings, of the essential supremum of $\|x-y\|$. Only that primitive is reused; its real-loss risk with a different expectation convention is not used.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen and Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning, arXiv:1908.08729v2 (4 Nov 2024), p. 11, Remark 1, with the risk convention of pp. 1–2 and 6

import Mathlib
import Definitions.Def_ShortWDRODual_MaxCost_Setting
import Definitions.Def_DupacovaWets_Consistency_expect

open MeasureTheory
open scoped ENNReal Classical

namespace KuhnWass2019.Reformulation

/-- Remark 1: worst-case risk for the type-infinity Wasserstein ball.
The distance is the infimum of the essential maximum displacement over all
probability couplings, using the published maximum-cost transport primitive. -/
noncomputable def infinityWorstCaseRisk {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    (ε : ℝ) (Ξ : Set E) (PN : Measure E) (ℓ : E → EReal) : EReal :=
  ⨆ (Q : Measure E) (_ : IsProbabilityMeasure Q ∧ Q Ξᶜ = 0 ∧
      ShortWDRODual.MaxCost.maxCost (fun x y : E => ‖x - y‖) PN Q ≤ ENNReal.ofReal ε),
    DupacovaWets.Consistency.expect Q ℓ

end KuhnWass2019.Reformulation


