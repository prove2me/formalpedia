-- Prove2me | Definitions.Def_BauerleRiederMDP_PDMDP_JumpModel_ContinuityCompactness
-- name    : BauerleRiederMDP_PDMDP_JumpModel_ContinuityCompactness
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:31:57.005366+00:00
-- url     : https://prove2.me/theorems/6cde6649-ba92-4a71-8914-b6a690778778
-- title:
--   The continuity and compactness assumptions of §8.2
-- statement:
--   The **continuity and compactness assumptions** are:
--
--   1. $U$ is compact;
--   2. $(t,x,\alpha)\mapsto\varphi^\alpha_t(x)$ is continuous on $\mathbb R_+\times E\times\mathcal R$;
--   3. $(x,\alpha)\mapsto\int_0^\infty e^{-(\lambda+\beta)t}b(\varphi^\alpha_t(x))\,dt$ is continuous on $E\times\mathcal R$;
--   4. $(x,u)\mapsto\int v(z)\,Q(dz|x,u)$ is upper semicontinuous for all upper semicontinuous $v\in\mathbb B_b^+$;
--   5. $(x,u)\mapsto r(x,u)$ is upper semicontinuous.
--
--   $\mathcal R$ carries the Young topology. These are the standing hypotheses of Theorems 8.2.6 and 8.2.7.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.251

import Mathlib
import Definitions.Def_BauerleRiederMDP_PDMDP_JumpModel
import Definitions.Def_MDPFinance_PDMDP_Core

open MeasureTheory ProbabilityTheory
open MDPFinance.PDMDP (erealIntegral IBbPlus)

namespace BauerleRiederMDP.PDMDP

/-- The **Continuity and Compactness Assumptions** (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.251, PDF 262):
(i) `U` is compact;
(ii) `(t,x,α) ↦ φ^α_t(x)` is continuous on `ℝ₊ × E × R`;
(iii) `(x,α) ↦ ∫_0^∞ e^{-(λ+β)t} b(φ^α_t(x)) dt` is continuous on `E × R`;
(iv) `(x,u) ↦ ∫ v(z) Q(dz|x,u)` is upper semicontinuous for all upper semicontinuous `v ∈ IB_b^+`;
(v) `(x,u) ↦ r(x,u)` is upper semicontinuous.

`R` carries the Young topology. -/
structure JumpModel.ContinuityCompactness {E U : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [TopologicalSpace U] [MeasurableSpace U] (M : JumpModel E U) (b : E → ℝ) : Prop where
  compact : CompactSpace U
  flow_continuous : ContinuousOn
    (fun p : ℝ × E × RelaxedControl U => M.flow p.2.2 p.2.1 p.1) {p | 0 ≤ p.1}
  bound_continuous : Continuous fun p : E × RelaxedControl U =>
    ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(M.lam + M.β) * t) * b (M.flow p.2 p.1 t)
  Q_usc : ∀ v ∈ IBbPlus b, UpperSemicontinuous v →
    UpperSemicontinuous fun p : E × U => erealIntegral (M.Q p) v
  r_usc : UpperSemicontinuous M.r

end BauerleRiederMDP.PDMDP


