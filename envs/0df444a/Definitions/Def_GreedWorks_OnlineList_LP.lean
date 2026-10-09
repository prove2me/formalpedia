-- Prove2me | Definitions.Def_GreedWorks_OnlineList_LP
-- name    : GreedWorks_OnlineList_LP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T22:13:44.196924+00:00
-- url     : https://prove2.me/theorems/16e0cac4-e003-46bd-a99e-dff4ae71a925
-- title:
--   §3, pp. 6–8 — stochastic and deterministic time-indexed relaxations and dual
-- statement:
--   The **time-indexed processing variable** $y_{ijs}$ represents the probability that job $j$ is processed on machine $i$ during integer slot $s\ge0$. Forbidden pairs have no variables. The common constraints are $y_{ijs}\ge0$, $\sum_j y_{ijs}\le1$ for each $(i,s)$, and
--
--   $$\sum_{i:\,(i,j)\in E}\frac{\sum_{s\ge0}y_{ijs}}{\mu_{ij}}=1\qquad(j\in J).$$
--
--   The stochastic relaxation $(S)$ uses the completion expression $C_j^S$ from equation (4) and requires $C_j^S\ge\sum_{i,s}y_{ijs}$. The simpler relaxation $(P)$ uses equation (6),
--
--   $$C_j^P=\sum_{i:\,(i,j)\in E}\sum_{s\ge0}\left[\frac{y_{ijs}}{\mu_{ij}}\left(s+\frac12\right)+\frac{y_{ijs}}2\right],$$
--
--   and drops that extra constraint. Their objectives are $z^S(y)=\sum_jw_jC_j^S$ and $z^P(y)=\sum_jw_jC_j^P$. The dual $(D)$ has free $\alpha_j$, nonnegative $\beta_{is}$, and the inequality $\alpha_j/\mu_{ij}\le\beta_{is}+w_j((s+1/2)/\mu_{ij}+1/2)$ for every eligible pair and slot.
--
--   These definitions are the comparison and dual-fitting interface used by the milestones. **Formalization Note** Each variable sequence and its first-moment-weighted sequence are required to be summable, so all real infinite sums have genuine series values.
-- source:
--   Gupta, Moseley, Uetz & Xie, Greed Works – Online Algorithms For Unrelated Machine Stochastic Scheduling, arXiv:1703.01634v4, pp. 6–8, §3, equations (2)–(6), (S), (P), (D)

import Mathlib
import Definitions.Def_GreedWorks_OnlineList_Model

namespace GreedWorks.OnlineList

open MeasureTheory ProbabilityTheory Classical

variable {M : Type*} [Fintype M] {n : ℕ}
  {Ω : Type*} [MeasurableSpace Ω]

/-- Time-indexed processing probabilities or their LP relaxation. -/
abbrev ProcessingPoint (M : Type*) (n : ℕ) := M → Fin n → ℕ → ℝ

/-- Squared coefficient of variation of an eligible processing time. -/
noncomputable def cvSquared (I : StochasticInstance M n Ω) (i : M) (j : Fin n) : ℝ :=
  variance (fun ω => (I.P i j ω : ℝ)) I.Pr / (mean I i j) ^ 2

/-- Formula (4): completion-time variable of the stochastic relaxation (S). -/
noncomputable def stochasticCompletion (I : StochasticInstance M n Ω)
    (y : ProcessingPoint M n) (j : Fin n) : ℝ := by
  classical
  exact ∑ i ∈ (Finset.univ.filter fun i : M => I.eligible i j),
    ∑' s : ℕ, (y i j s / mean I i j * ((s : ℝ) + 1 / 2) +
      (1 - cvSquared I i j) / 2 * y i j s)

/-- Formula (6): completion-time variable of the deterministic relaxation (P). -/
noncomputable def primalCompletion (I : StochasticInstance M n Ω)
    (y : ProcessingPoint M n) (j : Fin n) : ℝ := by
  classical
  exact ∑ i ∈ (Finset.univ.filter fun i : M => I.eligible i j),
    ∑' s : ℕ, (y i j s / mean I i j * ((s : ℝ) + 1 / 2) + y i j s / 2)

/-- Constraints (2), (3), and nonnegativity of (P), including summability so `tsum`
has its intended series value.  There are no variables for ineligible pairs. -/
def IsPrimalFeasible (I : StochasticInstance M n Ω)
    (y : ProcessingPoint M n) : Prop :=
  (∀ i j s, 0 ≤ y i j s) ∧
  (∀ i j s, ¬ I.eligible i j → y i j s = 0) ∧
  (∀ i j, Summable (y i j)) ∧
  (∀ i j, Summable (fun s : ℕ => ((s : ℝ) + 1 / 2) * y i j s)) ∧
  (∀ i s, (∑ j : Fin n, y i j s) ≤ 1) ∧
  (∀ j, (∑ i ∈ (Finset.univ.filter fun i : M => I.eligible i j),
    (∑' s : ℕ, y i j s) / mean I i j) = 1)

/-- The stochastic relaxation (S) adds constraint (5) to the common LP constraints. -/
def IsStochasticFeasible (I : StochasticInstance M n Ω)
    (y : ProcessingPoint M n) : Prop :=
  IsPrimalFeasible I y ∧
  ∀ j, (∑ i ∈ (Finset.univ.filter fun i : M => I.eligible i j),
    ∑' s : ℕ, y i j s) ≤ stochasticCompletion I y j

/-- Objective of (S). -/
noncomputable def stochasticValue (I : StochasticInstance M n Ω)
    (y : ProcessingPoint M n) : ℝ :=
  ∑ j : Fin n, I.weight j * stochasticCompletion I y j

/-- Objective of (P). -/
noncomputable def primalValue (I : StochasticInstance M n Ω)
    (y : ProcessingPoint M n) : ℝ :=
  ∑ j : Fin n, I.weight j * primalCompletion I y j

/-- Feasibility of dual (D), with α free and β nonnegative and summable. -/
def IsDualFeasible (I : StochasticInstance M n Ω)
    (a : Fin n → ℝ) (b : M → ℕ → ℝ) : Prop :=
  (∀ i s, 0 ≤ b i s) ∧ (∀ i, Summable (b i)) ∧
  ∀ i j s, I.eligible i j →
    a j / mean I i j ≤ b i s +
      I.weight j * (((s : ℝ) + 1 / 2) / mean I i j + 1 / 2)

end GreedWorks.OnlineList


