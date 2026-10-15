-- Prove2me | Definitions.Def_AccelVI_SafeAVI_Setting
-- name    : AccelVI_SafeAVI_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T09:02:29.836969+00:00
-- url     : https://prove2.me/theorems/0b7acc1e-e5ef-4995-a8e2-84dc314f5515
-- title:
--   §2, (2.1), Algorithm 1 — finite discounted MDP, the Bellman operator T, and Safe Accelerated Value Iteration (S-AVI)
-- statement:
--   **Finite discounted MDP.** Let $\mathbb S$ be a finite set of states and $\mathbb A$ a finite set of actions. The data of a Markov decision process are a transition kernel $P$, where $P_{iaj}$ is the probability of moving from state $i$ to state $j$ when action $a$ is chosen, a state-action reward $r \in \mathbb R^{\mathbb S\times\mathbb A}$ and a discount factor $\lambda$. The MDP is *valid* when each $P_{ia} = (P_{iaj})_{j\in\mathbb S}$ is a probability distribution ($P_{iaj}\ge 0$ and $\sum_j P_{iaj} = 1$) and $\lambda \in (0,1)$. Rewards are arbitrary real numbers.
--
--   **Bellman operator.** When $\mathbb A$ is nonempty, the Bellman operator $T:\mathbb R^{\mathbb S}\to\mathbb R^{\mathbb S}$ is
--
--   $$T(v)_i = \max_{a\in\mathbb A}\Big\{ r_{ia} + \lambda \sum_{j\in\mathbb S} P_{iaj}\, v_j \Big\}, \qquad i \in \mathbb S.$$
--
--   **Safe Accelerated Value Iteration (Algorithm 1).** Fix a scalar $\lambda'$, step sizes $\alpha,\gamma$ and a starting vector $v_0\in\mathbb R^{\mathbb S}$. Set $v_1 = T(v_0)$, and for every period $s \ge 1$ set
--
--   $$h_s = v_s + \gamma\,(v_s - v_{s-1}), \qquad v_{s+1/2} = h_s - \alpha\,\big(h_s - T(h_s)\big),$$
--
--   $$v_{s+1} = \begin{cases} v_{s+1/2} & \text{if } \|v_{s+1/2} - T(v_{s+1/2})\|_\infty \le \lambda'^{\,s+1}\,\|v_0 - T(v_0)\|_\infty,\\ T(v_s) & \text{otherwise.}\end{cases}$$
--
--   So each period tries an accelerated (A-VI) step and accepts it only if its Bellman residual is below the geometric threshold $\lambda'^{s+1}$ times the initial residual; otherwise it falls back to a plain value-iteration step from $v_s$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** The MDP is a structure carrying $P$, $r$ and $\lambda$ (written `lam`); validity is the separate predicate `MDP.Valid`, a hypothesis of each theorem, whose kernel condition is the published `IsTransitionKernel`. The operator $T$ is the published `BellmanOperator` applied to $(P, r, \lambda)$. The initial distribution $p_0$ of the paper's tuple is omitted, since no statement uses it. $\|\cdot\|_\infty$ is Mathlib's sup norm on functions `S → ℝ`. The sequence `savi M lam' α γ v0 : ℕ → (S → ℝ)` is indexed like the paper's $v_s$; its recursive case `s + 2` is the paper's period $s+1$, so the threshold there is `lam' ^ (s + 2)`. The definition places no constraint on $\lambda',\alpha,\gamma$; the theorems assume $\lambda'\in[\lambda,1)$ and $\alpha,\gamma>0$ as Algorithm 1 does.
-- source:
--   Goyal & Grand-Clément, A First-Order Approach to Accelerated Value Iteration, arXiv:1905.09963v7, p. 3, §2, (2.1); p. 14, Algorithm 1

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_BellmanOperator

namespace AccelVI.SafeAVI

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]

/-- §2, p. 3: the data (P, r, λ) of an MDP (S, A, P, r, p₀, λ); p₀ is omitted (no planned result uses it). -/
structure MDP (S A : Type*) where
  P : S → A → S → ℝ
  r : S → A → ℝ
  lam : ℝ

/-- §2: P_ia is a probability distribution over next states (the published
`IsTransitionKernel`), and λ ∈ (0, 1). -/
def MDP.Valid (M : MDP S A) : Prop :=
  FoundationsML.ReinforcementLearning.IsTransitionKernel M.P ∧ 0 < M.lam ∧ M.lam < 1

/-- (2.1): T(v)_i = max_{a ∈ A} {r_ia + λ P_iaᵀ v}, the published `BellmanOperator`
(a `Finset.sup'` over the nonempty finite action set). -/
noncomputable def bellman [Nonempty A] (M : MDP S A) (v : S → ℝ) : S → ℝ :=
  FoundationsML.ReinforcementLearning.BellmanOperator Finset.univ_nonempty M.P M.r M.lam v

/-- Algorithm 1 (Safe Accelerated Value Iteration), p. 14, with scalar λ' and step sizes α, γ:
v₀ is given and v₁ = T(v₀); at period s ≥ 1,
h_s = v_s + γ(v_s − v_{s−1}), v_{s+1/2} = h_s − α(h_s − T(h_s)), and
v_{s+1} = v_{s+1/2} if ‖v_{s+1/2} − T(v_{s+1/2})‖∞ ≤ λ'^{s+1}‖v₀ − T(v₀)‖∞, else v_{s+1} = T(v_s).
Lean's case `s + 2` is the paper's period s + 1, so its threshold is `lam' ^ (s + 2)`. -/
noncomputable def savi [Nonempty A] (M : MDP S A) (lam' α γ : ℝ) (v0 : S → ℝ) : ℕ → (S → ℝ)
  | 0 => v0
  | 1 => bellman M v0
  | s + 2 =>
      let vs := savi M lam' α γ v0 (s + 1)
      let h := vs + γ • (vs - savi M lam' α γ v0 s)
      let w := h - α • (h - bellman M h)
      if ‖w - bellman M w‖ ≤ lam' ^ (s + 2) * ‖v0 - bellman M v0‖ then w else bellman M vs

end AccelVI.SafeAVI


