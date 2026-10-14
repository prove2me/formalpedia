-- Prove2me | Definitions.Def_LookaheadAPI_LeastSquares_MDP
-- name    : LookaheadAPI_LeastSquares_MDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T20:51:22.116717+00:00
-- url     : https://prove2.me/theorems/8c8b9091-9cbb-4f5a-80bc-efa1ad121563
-- title:
--   Finite discounted MDP $(\mathcal S,\mathcal A,P,r,\alpha)$, the operators $T_\mu$ and $T$, $J^\mu$ and $J^*$
-- statement:
--   This module fixes the model of Section 2 of Winnicki, Lubars, Livesay and Srikant.
--
--   A **Markov decision process** is a 5-tuple $(\mathcal S,\mathcal A,P,r,\alpha)$. The state set $\mathcal S$ and the action set $\mathcal A$ are finite (and nonempty). For each action $a\in\mathcal A$, $P_{ij}(a)$ is the probability of moving from state $i$ to state $j$ when action $a$ is taken, so every row $P_{i\cdot}(a)$ is a probability distribution on $\mathcal S$. Taking action $a$ in state $s$ earns a reward with mean $r(s,a)\in[0,1]$, and future rewards are discounted by $\alpha\in(0,1)$.
--
--   A **deterministic policy** is a map $\mu:\mathcal S\to\mathcal A$. The module defines:
--
--   1. the **policy operator** $T_\mu:\mathbb R^{|\mathcal S|}\to\mathbb R^{|\mathcal S|}$,
--   $$(T_\mu J)(s)=r(s,\mu(s))+\alpha\sum_{j\in\mathcal S}P_{sj}(\mu(s))\,J(j);$$
--   2. the **Bellman operator** $T$ of (1),
--   $$(TJ)(s)=\max_{a\in\mathcal A}\Big\{r(s,a)+\alpha\sum_{j\in\mathcal S}P_{sj}(a)\,J(j)\Big\};$$
--   3. the **value** of $\mu$, $J^\mu(s)=E\big[\sum_{k\ge0}\alpha^k r(s_k,\mu(s_k))\,\big|\,s_0=s\big]$, the expected discounted reward of the Markov chain on $\mathcal S$ that follows $\mu$;
--   4. the **optimal reward-to-go** $J^*(s)=\max_\mu J^\mu(s)$, the maximum over the finitely many deterministic policies.
--
--   Every statement of the mission is phrased in these objects: $T^H J$ is the $H$-step lookahead of an estimate $J$, $T^m_\mu J$ is the $m$-step rollout (return) of $\mu$, and the error of a policy is $\|J^\mu-J^*\|_\infty$.
--
--   **Formalization Note** The kernel condition is the published `IsTransitionKernel` (with `P s a j` $=P_{sj}(a)$), $T$ is the published `BellmanOperator` and $J^\mu$ is the published `PolicyValue` (a discounted series of expected rewards, not the fixed point of $T_\mu$) of the point-mass policy at $\mu(s)$. The paper's rewards are "non-deterministic"; $J^\mu$, $T_\mu$ and $T$ depend on them only through their means, so $r(s,a)$ is the mean reward. Vectors are functions $\mathcal S\to\mathbb R$, whose Lean norm is the sup norm $\|\cdot\|_\infty$.
-- source:
--   arXiv:2109.13419v7, pp. 5–7, Section 2 (the MDP, J^μ, J^*, T_μ, T of eq. (1))

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_PolicyValue
import Definitions.Def_FoundationsML_ReinforcementLearning_BellmanOperator

namespace LookaheadAPI.LeastSquares

open FoundationsML.ReinforcementLearning

/-- The finite discounted MDP `(𝒮, 𝒜, P, r, α)` of Section 2 (arXiv:2109.13419v7, pp. 5–6).
`P s a j` is the transition probability `P_{sj}(a)` from state `s` to state `j` under action `a`
(each row is a probability distribution, the published `IsTransitionKernel`), `r s a ∈ [0, 1]` is
the (mean) reward of action `a` at state `s`, and `α ∈ (0, 1)` is the discount factor. -/
structure MDP (S A : Type*) [Fintype S] where
  /-- `P s a j = P_{sj}(a)`. -/
  P : S → A → S → ℝ
  /-- Every `P s a ·` is a probability distribution on `𝒮`. -/
  kernel : IsTransitionKernel P
  /-- The mean reward `r(s, a)`. -/
  r : S → A → ℝ
  /-- `r(s, a) ∈ [0, 1]` for all `s, a`. -/
  r_mem : ∀ s a, r s a ∈ Set.Icc (0 : ℝ) 1
  /-- The discount factor `α`. -/
  α : ℝ
  α_pos : 0 < α
  α_lt_one : α < 1

variable {S A : Type*} [Fintype S] [Fintype A]

/-- A deterministic stationary policy `μ : 𝒮 → 𝒜`, viewed as the point-mass stochastic policy
`π(s)(a) = 1` if `a = μ(s)` and `0` otherwise. -/
def detPolicy [DecidableEq A] (μ : S → A) : S → A → ℝ :=
  fun s a => if a = μ s then 1 else 0

/-- The policy operator `T_μ` (p. 6): `(T_μ J)(s) = r(s, μ(s)) + α ∑_j P_{sj}(μ(s)) J(j)`. -/
noncomputable def policyOp (M : MDP S A) (μ : S → A) (J : S → ℝ) : S → ℝ :=
  fun s => M.r s (μ s) + M.α * ∑ j : S, M.P s (μ s) j * J j

/-- The Bellman operator `T` of (1) (p. 6): `(TJ)(s) = max_{a ∈ 𝒜} {r(s, a) + α ∑_j P_{sj}(a) J(j)}`,
the published `BellmanOperator` (a `Finset.sup'` over the finite nonempty action set). -/
noncomputable def bellmanOp [Nonempty A] (M : MDP S A) (J : S → ℝ) : S → ℝ :=
  BellmanOperator Finset.univ_nonempty M.P M.r M.α J

/-- The value `J^μ(s) = E[∑_{k ≥ 0} α^k r(s_k, μ(s_k)) | s_0 = s]` of a deterministic policy `μ`
(p. 6): the published `PolicyValue` (the discounted series of expected rewards of the Markov chain
driven by `μ`) of the point-mass policy `detPolicy μ`. -/
noncomputable def valueOf [DecidableEq S] [DecidableEq A] (M : MDP S A) (μ : S → A) : S → ℝ :=
  PolicyValue (detPolicy μ) M.P M.r M.α

/-- The optimal reward-to-go `J^*(s) = max_μ J^μ(s)` (p. 6), the maximum over the finite nonempty
set of deterministic policies `μ : 𝒮 → 𝒜`. -/
noncomputable def optValue [DecidableEq S] [DecidableEq A] [Nonempty A] (M : MDP S A) : S → ℝ :=
  fun s => Finset.univ.sup' Finset.univ_nonempty (fun μ : S → A => valueOf M μ s)

end LookaheadAPI.LeastSquares


