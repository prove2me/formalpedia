-- Prove2me | Definitions.Def_CoupledLearning_payoffMeasure
-- name    : CoupledLearning_payoffMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:38:05.721926+00:00
-- url     : https://prove2.me/theorems/2fbc00f6-592b-4e6c-91e9-6d0180a4de6b
-- title:
--   Payoff distribution with density $\varphi^s(y|q)$
-- statement:
--   For a parameter $s$ and a profile $q$, the payoff distribution is the measure on payoff vectors $y=(y_i)_{i\in I}\in\mathbb R^I$ with density $\varphi^s(y|q)$ with respect to Lebesgue measure:
--
--   $$\mu^s_q(A)=\int_A\varphi^s(y|q)\,dy .$$
--
--   It is used to state absolute continuity, the KL divergence and the conditional law of the realized payoffs.
-- source:
--   Wu, Amin, Ozdaglar, Convergence and Stability of Coupled Belief–Strategy Learning Dynamics in Continuous Games, arXiv:2206.05637v2, §2, p.7

import Mathlib
import Definitions.Def_CoupledLearning_Prof

open MeasureTheory

namespace CoupledLearning

/-- The payoff distribution with density `φ^s(y|q)` (arXiv:2206.05637v2, §2, p.7): the measure on
payoff vectors `y = (y_i)_{i ∈ I} ∈ ℝ^I` with density `y ↦ φ s q y` with respect to Lebesgue
measure.

**Formalization Note.** Lebesgue measure on `ℝ^I` is `volume` on `I → ℝ`; the density enters as
`ENNReal.ofReal (φ s q y)`. -/
noncomputable def payoffMeasure {I S : Type*} [Fintype I] {d : I → ℕ}
    (φ : S → Prof d → (I → ℝ) → ℝ) (s : S) (q : Prof d) : Measure (I → ℝ) :=
  volume.withDensity (fun y => ENNReal.ofReal (φ s q y))

end CoupledLearning


