-- Prove2me | Definitions.Def_SampleComplexityRL_Mismeasure_BellmanError
-- name    : SampleComplexityRL_Mismeasure_BellmanError
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T03:09:18.791671+00:00
-- url     : https://prove2.me/theorems/b5ec6241-59fc-4af4-91f1-773f3288ffdf
-- title:
--   Deterministic stationary policies, Q_J and the Bellman error B_J of a state vector J (Definition 5.1.2)
-- statement:
--   Work in the normalized $\gamma$-discounted model: finite state set $S$, finite nonempty action set $A$, transition kernel $P(s'\mid s,a)$, reward $r(s,a)$, discount factor $\gamma\in[0,1)$.
--
--   1. A **deterministic stationary policy** $f:S\to A$ is identified with the stochastic policy $\pi_f(a\mid s)=\mathbf 1[a=f(s)]$.
--   2. For a vector $J\in\mathbb R^S$ on the state space,
--   $$Q_J(s,a)=(1-\gamma)\,r(s,a)+\gamma\,\mathbb E_{s'\sim P(\cdot\mid s,a)}[J(s')].$$
--   3. The **Bellman error** of $J$ (Definition 5.1.2) is the number
--   $$B_J=\sup_{s,a}\big|Q_J(s,a)-J(s)\big|.$$
--
--   When $J=V_{\pi,\gamma}$ is the value of a policy, $B_J$ is the largest absolute advantage $\|A_{\pi,\gamma}\|_\infty$. The Bellman error is the error measure of the classical Williams–Baird bound for greedy policies (Theorem 5.1.3).
--
--   **Formalization Note** The thesis writes $B_J(s)$ although the supremum runs over both $s$ and $a$; it is formalized as printed, a single number, namely the sup norm of $(s,a)\mapsto Q_J(s,a)-J(s)$ on the finite set $S\times A$ (Mathlib's norm on `S → A → ℝ`). It is not replaced by the usual residual $\max_s|\max_aQ_J(s,a)-J(s)|$.
-- source:
--   Kakade, On the Sample Complexity of Reinforcement Learning, PhD thesis, University College London, 2003, p. 22 (Definition 2.1.2, deterministic stationary policies), p. 58 (Definition 5.1.2)

import Mathlib
import Definitions.Def_ApproxOptRL_Shared_Model
import Definitions.Def_SampleComplexityRL_ApproxDP_Greedy

namespace SampleComplexityRL.Mismeasure

/-- `Q_J(s,a) = (1-γ) r(s,a) + γ E_{s' ∼ P(·|s,a)}[J(s')]` for a vector `J` on the state space
(Definition 5.1.2, p. 58). -/
noncomputable def qJ {S A : Type} [Fintype S]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (J : S → ℝ) (s : S) (a : A) : ℝ :=
  (1 - γ) * r s a + γ * ∑ s', P s a s' * J s'

/-- The Bellman error of `J` (Definition 5.1.2, p. 58): `B_J = sup_{s,a} |Q_J(s,a) - J(s)|`,
a single number (the supremum runs over all state-action pairs). It is the sup norm of the
function `(s,a) ↦ Q_J(s,a) - J(s)` on the finite set `S × A`. -/
noncomputable def bellmanError {S A : Type} [Fintype S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (J : S → ℝ) : ℝ :=
  ‖fun s a => qJ P r γ J s a - J s‖

end SampleComplexityRL.Mismeasure


