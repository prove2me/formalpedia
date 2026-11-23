-- Prove2me | Definitions.Def_StableFA_Discounted_Supplement_QBackup
-- name    : StableFA_Discounted_Supplement_QBackup
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T10:39:29.421885+00:00
-- url     : https://prove2.me/theorems/6597ee35-d7cf-4321-892d-6ef9effe2e73
-- title:
--   §5 and Appendix A — action values and the parallel Q-learning backup
-- statement:
--   For a finite MDP $M$ with expected costs $c_{xa}$, substochastic transition probabilities $p_{xay}$ and nonempty finite action sets $U(y)$, a continuation value $V$ determines action values
--   $$Q_V(x,a)=c_{xa}+\gamma\sum_y p_{xay}V(y).$$
--   At $V=V^*$ this is the report's $Q^*$. The full parallel Q-learning backup is
--   $$(T_MQ)(x,a)=c_{xa}+\gamma\sum_y p_{xay}\min_{b\in U(y)}Q(y,b).$$
--   These operators provide the Q-function interface for Theorem A.1. The implicit termination state has value zero. Costs are expected one-step costs, so only finite sums occur; no random cost distribution is needed. The real parameter $\gamma$ is unrestricted for this algebraic interface. The backup uses step size one, as in Appendix A, rather than the relaxed update of §5.
--
--   **Formalization Note** The finite MDP is the published `BertsekasSSPModel`: states `Fin n`, with state 1 (the cost-free absorbing goal, $V(1)\equiv 0$, p. 4) as its implicit termination state, so the goal contributes zero to every sum. The minimum over next actions is `Finset.inf'` over the nonempty admissible set $U(y)$; taking $U(y)$ equal to the whole action set gives the report's common action set $A$. The report's $\gamma\in[0,1]$ is generalized to every real $\gamma$.
-- source:
--   Gordon, Stable Function Approximation in Dynamic Programming, Tech. Rep. CMU-CS-95-103, Carnegie Mellon University (1995), p. 11, §5, Q* function and Q-learning operator; p. 19, Appendix A, first proof display

import Mathlib
import Definitions.Def_BertsekasSSPModel

namespace StableFA.Discounted.Supplement

/-- The one-step action value determined by a continuation value V (§5).
At V = V*, this is the report's Q* function. -/
def qFromValue {n : ℕ} {C : Type} [Fintype C]
    (M : BertsekasSSPModel n C) (γ : ℝ) (V : Fin n → ℝ) : Fin n → C → ℝ :=
  fun x a => M.g x a + γ * ∑ y, M.p x a y * V y

/-- The full parallel Q-learning backup (step size one), §5 and Appendix A.
The implicit termination state has Q-value zero. -/
noncomputable def qBackup {n : ℕ} {C : Type} [Fintype C]
    (M : BertsekasSSPModel n C) (γ : ℝ) (Q : Fin n → C → ℝ) : Fin n → C → ℝ :=
  fun x a => M.g x a + γ * ∑ y, M.p x a y * (M.U y).inf' (M.hU y) (Q y)

end StableFA.Discounted.Supplement


