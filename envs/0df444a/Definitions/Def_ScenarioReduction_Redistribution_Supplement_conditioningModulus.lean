-- Prove2me | Definitions.Def_ScenarioReduction_Redistribution_Supplement_conditioningModulus
-- name    : ScenarioReduction_Redistribution_Supplement_conditioningModulus
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T08:30:47.81862+00:00
-- url     : https://prove2.me/theorems/27ea04a0-72e4-4ea4-aa39-384e663e073e
-- title:
--   Conditioning function and the exact stability modulus
-- statement:
--   Let $P$ be the reference law, $F_P(x)=E_P f(\omega,x)$ its expected objective, $v(P)$ its optimal value, and $S(P)$ its set of minimizers. For $\tau\ge0$ and $\eta\ge0$, define
--
--   $$
--   \psi(\tau)=\inf\{F_P(x)-v(P):x\in X,\ d(x,S(P))\ge\tau\},\qquad
--   \psi^{-1}(t)=\sup\{\tau\ge0:\psi(\tau)\le t\},\qquad
--   \Psi(\eta)=\eta+\psi^{-1}(2\eta).
--   $$
--
--   This is the conditioning modulus in Theorem 1. Its inverse is monotone and generalized, so no strict convexity or bijectivity is assumed.
--
--   **Formalization Note** The constraint $x\in X$ implements the objective of model (1), extended by positive infinity outside X. The source's minimum is represented by an extended infimum; under Theorem 1's assumptions, finite nonempty conditioning problems attain that infimum. The empty infimum is positive infinity. The inverse and modulus take values in the nonnegative extended reals, with empty supremum zero and unbounded supremum positive infinity. Distances use `Metric.infEDist`, positive infinity for an empty set. All uses of the inverse range over nonnegative tau, preserving the factor two inside the inverse.
-- source:
--   Dupačová, Gröwe-Kuska, Römisch, Scenario reduction in stochastic programming, Math. Program. Ser. A 95 (2003), DOI 10.1007/s10107-002-0331-0, p. 496, Theorem 1, definitions of psi and Psi, PDF 4

import Mathlib
import Definitions.Def_ProbMetricStab_General_Setting
set_option autoImplicit false
open scoped ENNReal

namespace ScenarioReduction.Redistribution.Supplement

/-- The conditioning function of model (1), p. 496. The constraint X is retained:
this equals use of the objective extended by +infinity outside X. Empty infimum = +infinity. -/
noncomputable def conditioning {n s : ℕ} (M : ProbMetricStab.General.Model n s 0)
    (P : MeasureTheory.Measure M.Ξ) (τ : ℝ) : EReal :=
  ⨅ x ∈ {x : EuclideanSpace ℝ (Fin n) | x ∈ M.X ∧
    ENNReal.ofReal τ ≤ Metric.infEDist x (M.S P)}, M.integral P 0 x - M.v P

/-- Monotone generalized inverse, not an inverse requiring bijectivity. -/
noncomputable def conditioningInverse {n s : ℕ} (M : ProbMetricStab.General.Model n s 0)
    (P : MeasureTheory.Measure M.Ξ) (t : EReal) : ℝ≥0∞ :=
  ⨆ τ ∈ {τ : ℝ | 0 ≤ τ ∧ conditioning M P τ ≤ t}, ENNReal.ofReal τ

/-- The EXACT modulus Psi(eta) = eta + psi^{-1}(2 eta), p. 496. -/
noncomputable def conditioningModulus {n s : ℕ} (M : ProbMetricStab.General.Model n s 0)
    (P : MeasureTheory.Measure M.Ξ) (η : ℝ≥0∞) : ℝ≥0∞ :=
  η + conditioningInverse M P ((2 * η : ℝ≥0∞) : EReal)

end ScenarioReduction.Redistribution.Supplement


