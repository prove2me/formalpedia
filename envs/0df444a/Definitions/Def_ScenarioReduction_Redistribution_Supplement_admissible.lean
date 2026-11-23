-- Prove2me | Definitions.Def_ScenarioReduction_Redistribution_Supplement_admissible
-- name    : ScenarioReduction_Redistribution_Supplement_admissible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T08:28:14.517727+00:00
-- url     : https://prove2.me/theorems/096fdf1b-7be4-479c-8625-45c56bf34e04
-- title:
--   The exact admissible probability class P_f
-- statement:
--   For the feasible set $X$, integrand $f$ and the closed unit ball $\mathbb B$, the admissible class consists of Borel probability measures $Q$ on $\Omega$ satisfying, for every $\rho>0$,
--
--   $$
--   -\infty<\int_\Omega\inf_{x\in X\cap\rho\mathbb B}f(\omega,x)\,Q(d\omega)
--   \le\sup_{x\in X\cap\rho\mathbb B}\int_\Omega f(\omega,x)\,Q(d\omega)<+\infty.
--   $$
--
--   The pointwise infimum is taken before integration. This is the class controlling the local lower bounds and finite expected objectives in Theorem 1.
--
--   **Formalization Note** Every displayed infimum and supremum is in the extended reals. The published extended expectation uses positive and negative Lebesgue integrals, with positive infinity when the positive integral is infinite. The two outer inequalities exclude undefined infinite cancellation in the admissible regime. The Lean definition imposes the two outer bounds, $-\infty<\int\inf f\,dQ$ and $\sup\int f\,dQ<+\infty$, for every $\rho>0$, and does not impose the printed middle inequality. When $X\cap\rho\mathbb B$ is nonempty, that inequality holds automatically because the expectation is monotone, so nothing changes on those radii. When the ball misses $X$ (which happens for small $\rho$ whenever $0\notin X$), the infimum over the empty set is $+\infty$ and the supremum is $-\infty$. Read literally, the middle inequality would then become $+\infty\le-\infty$, which would make the class empty for every $X$ with $0\notin X$. The source of Theorem 1 (Rachev–Römisch) states the class as these two separate bounds.
-- source:
--   Dupačová, Gröwe-Kuska, Römisch, Scenario reduction in stochastic programming, Math. Program. Ser. A 95 (2003), DOI 10.1007/s10107-002-0331-0, p. 496, Section 2, definition of P_f, PDF 4

import Mathlib
import Definitions.Def_ProbMetricStab_General_Setting
set_option autoImplicit false

namespace ScenarioReduction.Redistribution.Supplement

/-- The class P_f, p. 496: for EVERY positive radius, the integral of the pointwise
infimum over X ∩ ρ𝔹 is > -∞ and the supremum of the integrals over X ∩ ρ𝔹 is < +∞.
The printed middle inequality `lower ≤ upper` holds automatically whenever X ∩ ρ𝔹 is
nonempty (the expectation is monotone); it is not imposed, since on an empty ball it
would read `+∞ ≤ -∞` and empty the class for every X with 0 ∉ X. -/
def admissible {n s : ℕ} (M : ProbMetricStab.General.Model n s 0)
    (Q : MeasureTheory.Measure M.Ξ) : Prop :=
  MeasureTheory.IsProbabilityMeasure Q ∧ ∀ ρ : ℝ, 0 < ρ →
    let lower : EReal := DupacovaWets.Consistency.expect Q
      (fun ω => ⨅ x ∈ {x : EuclideanSpace ℝ (Fin n) | x ∈ M.X ∧ ‖x‖ ≤ ρ},
        M.f 0 ω x)
    let upper : EReal := ⨆ x ∈ {x : EuclideanSpace ℝ (Fin n) | x ∈ M.X ∧ ‖x‖ ≤ ρ},
      M.integral Q 0 x
    ⊥ < lower ∧ upper < ⊤

end ScenarioReduction.Redistribution.Supplement


