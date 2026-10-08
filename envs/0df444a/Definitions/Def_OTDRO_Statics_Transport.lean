-- Prove2me | Definitions.Def_OTDRO_Statics_Transport
-- name    : OTDRO_Statics_Transport
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T23:10:51.96655+00:00
-- url     : https://prove2.me/theorems/4ea0c7d0-0089-4253-a08f-8ba00d9cd337
-- title:
--   Worst-case transport map and its graph coupling
-- statement:
--   For a scalar field $g(x)$, the transport map and associated coupling are
--
--   $$T_{\delta,\beta,g}(x)=x+\sqrt\delta\,g(x)A(x)^{-1}\beta,\qquad
--   \pi_{\delta,\beta,g}=(\operatorname{id},T_{\delta,\beta,g})_\#P_0.$$
--
--   The second marginal is the law of the displaced observation. The graph coupling records both its first marginal $P_0$ and its transport cost, so a worst-case law can be checked against the paper's primal problem.
--
--   **Formalization Note** Statements that take the pushforward as a probability law require almost-everywhere measurability of the transport map.
-- source:
--   arXiv:1810.02403v3, (10), p. 14; §2.1, p. 9

import Mathlib
import Definitions.Def_OTDRO_Dual_Setting
import Definitions.Def_ModelRiskOT_Duality_primalValue
import Definitions.Def_OTDRO_WorstCase_Transport

namespace OTDRO.Statics

open MeasureTheory Matrix

/-- The transport map x ↦ x + √δ g(x) A(x)⁻¹β of (10), p. 14. -/
noncomputable def shiftMap {d : ℕ}
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (δ : ℝ) (β : EuclideanSpace ℝ (Fin d))
    (g : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  x + (Real.sqrt δ * g x) • (WithLp.toLp 2 ((A x)⁻¹ *ᵥ β.ofLp))

end OTDRO.Statics


