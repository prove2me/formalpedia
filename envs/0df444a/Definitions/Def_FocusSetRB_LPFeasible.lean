-- Prove2me | Definitions.Def_FocusSetRB_LPFeasible
-- name    : FocusSetRB_LPFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:16:12.456995+00:00
-- url     : https://prove2.me/theorems/1ccb5d04-44c8-4c16-8d2f-1e88a521879f
-- title:
--   The LP relaxation (LP), its feasible set and its optimal value $R^{\mathrm{rel}}$
-- statement:
--   The **LP relaxation** of the $N$-armed problem with budget $\alpha N$ is the linear program in the variables $y(s,a)$, $s\in\mathbb S$, $a\in\{0,1\}$:
--
--   $$
--   \begin{aligned}
--   \text{maximize}\quad & \sum_{s,a} r(s,a)\,y(s,a)\\
--   \text{subject to}\quad & \sum_{s} y(s,1)=\alpha, &&\text{(2a)}\\
--   & \sum_{s',a} y(s',a)\,P(s',a,s)=\sum_a y(s,a)\quad\forall s, &&\text{(2b)}\\
--   & \sum_{s',a'} y(s',a')=1,\qquad y(s,a)\ge 0. &&\text{(2c)}
--   \end{aligned}
--   $$
--
--   A feasible $y$ is a stationary state-action distribution of the single-armed MDP that pulls the arm with long-run frequency $\alpha$. An **optimal solution** is a feasible point with the largest objective, and $R^{\mathrm{rel}}$ is the optimal value. The LP value upper-bounds the optimal reward of the $N$-armed problem (Lemma 10), and the optimal solution $y^*$ defines the optimal single-armed policy $\bar\pi^*$ on which the focus-set policies are built.
--
--   **Formalization Note** $R^{\mathrm{rel}}$ is the supremum of the objective over the feasible set. For $0<\alpha<1$ the feasible set is nonempty and the objective is bounded by $r_{\max}$ on it, so the supremum is attained and equals the objective of every optimal solution.
-- source:
--   Hong, Xie, Chen, Wang, Unichain and Aperiodicity are Sufficient for Asymptotic Optimality of Average-Reward Restless Bandits, arXiv:2402.05689v4, §3.3, (LP) and (2a)–(2c), p.6

import Mathlib
import Definitions.Def_FocusSetRB_SingleArmMDP

namespace FocusSetRB

variable {S : Type*} [Fintype S]

/-- Feasibility for the **LP relaxation (LP)** of the restless bandit problem
(arXiv:2402.05689v4, §3.3, constraints (2a)–(2c), p.6): `y = (y(s, a))` satisfies
`∑_s y(s, 1) = α` (2a), `∑_{s', a} y(s', a) P(s', a, s) = ∑_a y(s, a)` for every `s` (2b),
`∑_{s', a'} y(s', a') = 1` and `y(s, a) ≥ 0` (2c).

**Formalization Note.** Actions are `Bool` (`true` = `1`). -/
def LPFeasible (M : SingleArmMDP S) (α : ℝ) (y : S → Bool → ℝ) : Prop :=
  (∑ s, y s true = α) ∧
  (∀ s, ∑ s', ∑ a, y s' a * M.P s' a s = ∑ a, y s a) ∧
  (∑ s, ∑ a, y s a = 1) ∧
  (∀ s a, 0 ≤ y s a)

/-- The objective `∑_{s, a} r(s, a) y(s, a)` of (LP) (arXiv:2402.05689v4, §3.3, p.6). -/
def lpObjective (M : SingleArmMDP S) (y : S → Bool → ℝ) : ℝ :=
  ∑ s, ∑ a, M.r s a * y s a

/-- `y` is an **optimal solution of (LP)** (arXiv:2402.05689v4, §3.3–3.4, p.6): it is feasible
and no feasible point has a larger objective. -/
def IsLPOptimal (M : SingleArmMDP S) (α : ℝ) (y : S → Bool → ℝ) : Prop :=
  LPFeasible M α y ∧ ∀ y', LPFeasible M α y' → lpObjective M y' ≤ lpObjective M y

/-- `R^rel`, the **optimal value of (LP)** (arXiv:2402.05689v4, §3.3, p.6).

**Formalization Note.** The supremum of the objective over the feasible set, as a real `sSup`.
For `0 < α < 1` the feasible set is nonempty (the stationary state-action law of the policy that
pulls with probability `α` in every state is feasible) and the objective is bounded by `r_max`
on it, so this is a genuine maximum, equal to the objective of any optimal solution. -/
noncomputable def Rrel (M : SingleArmMDP S) (α : ℝ) : ℝ :=
  sSup {v : ℝ | ∃ y, LPFeasible M α y ∧ lpObjective M y = v}

end FocusSetRB


