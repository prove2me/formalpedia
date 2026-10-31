-- Prove2me | Definitions.Def_ParamSDPTraj_IsIrregularAccumulationPoint
-- name    : ParamSDPTraj_IsIrregularAccumulationPoint
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:16:30.213007+00:00
-- url     : https://prove2.me/theorems/82074882-7ca6-45d2-b82d-451a5caf78d1
-- title:
--   Irregular accumulation point (corrected)
-- statement:
--   A pair $(X^*,t^*)$ is an **irregular accumulation point** of $F$ if $X^*\in F(t^*)$, there is $\varepsilon>0$ such that $F$ is single-valued and continuous at every $t\in(t^*-\varepsilon,t^*)$, and for every $\delta>0$ at least one of the following holds:
--
--   1. there is a sequence of times in $(t^*,t^*+\delta)$ converging to $t^*$ at each of which $F$ is not inner semicontinuous;
--   2. there is a sequence of times in $(t^*,t^*+\delta)$ converging to $t^*$ each of which is a right-sided continuous loss of uniqueness of $F$.
--
--   **Formalization Note** This corrects Definition 3.11 in two places, each forced by a counterexample to Theorem 3.15 as printed. In bullet 2 the printed "continuous bifurcation" is replaced by the right-sided notion. The printed sentence "At these times, either a discontinuous isolated multiple point or a discontinuous non-isolated multiple point appears" is commentary and not a condition. All intervals and times lie in $T$.
-- source:
--   Bellon, Henrion, Kungurtsev, Mareček, Parametric Semidefinite Programming: Geometry of the Trajectory of Solutions, arXiv:2104.05445v3, Definition 3.11, p.14 (corrected)

import Mathlib
import Definitions.Def_ParamSDPTraj_SingleValuedAt
import Definitions.Def_ParamSDPTraj_PKContinuousAt
import Definitions.Def_ParamSDPTraj_RightContLossOfUniqueness

namespace ParamSDPTraj

/-- **Irregular accumulation point (corrected).**
Bellon, Henrion, Kungurtsev, Mareček, *Parametric Semidefinite Programming: Geometry of the
Trajectory of Solutions*, arXiv:2104.05445v3, Definition 3.11, p.14: "At an irregular accumulation point (X∗, t∗), X∗ ∈ P∗(t∗) and there
exists ε > 0 such that • P∗(t) is single-valued and continuous for every t ∈ (t∗ − ε, t∗) and for
any δ > 0 at least one of the following is true: • there exists a sequence of times
{tk}∞k=1 ⊆ (t∗, t∗+δ) at which a loss of inner semi-continuity occurs and limk→∞ tk = t∗. At these
times, either a discontinuous isolated multiple point or a discontinuous non-isolated multiple
point appears. • there exists a sequence of times {tk}∞k=1 ⊆ (t∗, t∗ + δ) at which a continuous
bifurcation occurs and limk→∞ tk = t∗."

**Formalization Note** Two corrections, both forced by counterexamples to Theorem 3.15 as printed.
(1) In the second bullet "a continuous bifurcation occurs at tk" is
`RightContLossOfUniqueness T F (s k)`: Definition 3.10 without its left condition.
(2) The sentence "At these times, either … appears" is commentary, not a condition.
The left interval lies in `T`. Times `s k` lie in `T`, since T may end before t∗ + δ for a large
δ; the sequence converges to t∗ ∈ T, so this costs nothing. -/
def IsIrregularAccumulationPoint {n : ℕ} (T : Set ℝ) (F : ℝ → Set (Matrix (Fin n) (Fin n) ℝ)) (X : Matrix (Fin n) (Fin n) ℝ)
    (tstar : ℝ) : Prop :=
  X ∈ F tstar ∧
    (∃ ε > 0, Set.Ioo (tstar - ε) tstar ⊆ T ∧
      ∀ t ∈ Set.Ioo (tstar - ε) tstar, SingleValuedAt F t ∧ PKContinuousAt T F t) ∧
    ∀ δ > 0,
      (∃ s : ℕ → ℝ, (∀ k, s k ∈ Set.Ioo tstar (tstar + δ) ∧ s k ∈ T) ∧
        Filter.Tendsto s Filter.atTop (nhds tstar) ∧ ∀ k, ¬ InnerSemicontAt T F (s k)) ∨
      (∃ s : ℕ → ℝ, (∀ k, s k ∈ Set.Ioo tstar (tstar + δ) ∧ s k ∈ T) ∧
        Filter.Tendsto s Filter.atTop (nhds tstar) ∧ ∀ k, RightContLossOfUniqueness T F (s k))

end ParamSDPTraj


