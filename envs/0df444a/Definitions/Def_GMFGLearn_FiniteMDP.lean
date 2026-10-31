-- Prove2me | Definitions.Def_GMFGLearn_FiniteMDP
-- name    : GMFGLearn_FiniteMDP
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:52:37.514009+00:00
-- url     : https://prove2.me/theorems/4615ea59-dfd1-4c4e-a56f-8b624f2cdf52
-- title:
--   The Bellman optimality equation and the optimal Q-function $Q^\star_{\mathcal M}$ of a finite discounted MDP
-- statement:
--   Let $\mathcal M=(\mathcal S,\mathcal A,P,r,\gamma)$ be a discounted MDP with finite state and action sets ($\mathcal A$ nonempty), transition probabilities $P(s'\mid s,a)$, mean reward $r(s,a)=\mathbb E[r(s,a)]$ and discount $\gamma$. A function $Q:\mathcal S\times\mathcal A\to\mathbb R$ solves the **Bellman optimality equation** if
--
--   $$
--   Q(s,a)=r(s,a)+\gamma\sum_{s'\in\mathcal S}P(s'\mid s,a)\max_{a'\in\mathcal A}Q(s',a')\qquad\text{for all }s,a.
--   $$
--
--   The **optimal Q-function** $Q^\star_{\mathcal M}$ is its solution. When every $P(\cdot\mid s,a)$ is a probability vector and $0\le\gamma<1$ the equation has exactly one solution.
--
--   The optimal Q-function of the MDP $\mathcal M_{\mathcal L}$ defines the policy selection $\Gamma_1$ of the finite setting and the action gaps of the $\epsilon$-net.
--
--   **Formalization Note** $Q^\star$ is defined as a chosen solution; the mission's verification file proves existence and uniqueness for probability transitions and $0\le\gamma<1$. The page prints $\gamma\max_{a'}\sum_{s'}P(s'\mid s,a)Q^\star(s',a')$; the maximum is placed inside the sum, the standard equation of the optimal Q-function that the page names ($V^\star(s)=\max_aQ^\star(s,a)$).
-- source:
--   Guo, Hu, Xu, Zhang, A General Framework for Learning Mean-Field Games, arXiv:2003.06069v3, §4.1, p.10 (Bellman equation)

import Mathlib

namespace GMFGLearn

/-- **The Bellman optimality equation of a finite discounted MDP.** Guo–Hu–Xu–Zhang, *A General
Framework for Learning Mean-Field Games*, arXiv:2003.06069v3, §4.1, p.10: for an MDP
`M = (S, A, P, r, γ)` the optimal Q-function is "the unique solution of the Bellman equation",
`Q⋆_M(s,a) = E[r(s,a)] + γ Σ_{s′∈S} P(s′|s,a) max_{a′} Q⋆_M(s′,a′)` for all `s, a`, with optimal value
`V⋆_M(s) = max_a Q⋆_M(s,a)`.

**Formalization Note** Finite `S`, `A` (§4, p.10), `A` nonempty. `P s a s'` is `P(s′|s,a)` and
`r s a` is the mean reward `E[r(s,a)]`. The page prints `γ max_{a′} Σ_{s′} P(s′|s,a)Q⋆(s′,a′)`; the
maximum is placed inside the sum here, the standard Bellman optimality equation, whose solution is
the optimal Q-function the page names (`V⋆(s) = max_a Q⋆(s,a)`, and `argmax-e(Q⋆(s,·))` is an
optimal policy, p.10). -/
def IsBellmanFixed {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (Q : S → A → ℝ) : Prop :=
  ∀ s a, Q s a = r s a + γ * ∑ s', P s a s' * Finset.univ.sup' Finset.univ_nonempty (Q s')

/-- **The optimal Q-function `Q⋆_M`** of a finite discounted MDP (§4.1, p.10): the solution of the
Bellman equation `IsBellmanFixed`.

**Formalization Note** Defined as a chosen solution. When `P(·|s,a)` are probability vectors and
`0 ≤ γ < 1` (the case of every MDP `M_L` of the paper), the Bellman operator is a `γ`-contraction in
the sup norm, so the solution exists and is unique, and this is that solution (proved in the
mission's verification file). -/
noncomputable def optQ {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) : S → A → ℝ := by
  classical
  exact if h : ∃ Q, IsBellmanFixed P r γ Q then h.choose else 0

end GMFGLearn


