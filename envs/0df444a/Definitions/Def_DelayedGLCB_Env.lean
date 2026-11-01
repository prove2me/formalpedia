-- Prove2me | Definitions.Def_DelayedGLCB_Env
-- name    : DelayedGLCB_Env
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T08:24:27.958864+00:00
-- url     : https://prove2.me/theorems/dc330618-3373-4c40-bbf1-6238dd3cd978
-- title:
--   The delayed GLM contextual bandit environment $(x_{t,a}, y_{t,a}, D_t, \alpha_t)$
-- statement:
--   On a probability space $(\Omega,\mathcal F,P)$, a **delayed generalized linear contextual bandit environment** with dimension $d$ and $K$ arms consists of, for every round $t=1,2,\dots$:
--
--   1. feature vectors $x_{t,a}\in\mathbb R^d$, one for each arm $a\in[K]$;
--   2. rewards $y_{t,a}$, one for each arm (the learner only sees the reward of the arm it plays);
--   3. a delay $D_t\in\mathbb R$: the reward of round $t$ becomes observable at the end of round $t+D_t$;
--   4. an exploration draw $\alpha_t\in[K]$, the arm played in an exploration round of DUCB-GLCB.
--
--   This is the common data on which the model assumptions, the algorithm DUCB-GLCB and its regret are defined.
--
--   **Formalization Note** Rounds start at $1$ (index $0$ is unused), vectors are `Fin d → ℝ`, and the reward is a full table over arms. All distributional assumptions are separate hypotheses.
-- source:
--   Blanchet, Xu, Zhou, Delay-Adaptive Learning in Generalized Linear Contextual Bandits, arXiv:2003.05174v1, §2.1–§2.2, pp.4–5, and Algorithm 1, p.7

import Mathlib

namespace DelayedGLCB

/-- **The delayed generalized linear contextual bandit environment.**
Blanchet, Xu, Zhou, *Delay-Adaptive Learning in Generalized Linear Contextual Bandits*,
arXiv:2003.05174v1, §2.1–§2.2, pp.4–5, and Algorithm 1, p.7.

On a probability space `Ω`, round `t` carries
* `x t ω a ∈ ℝ^d`, the feature vector `x_{t,a}` of arm `a ∈ [K]` (p.4);
* `y t ω a`, the reward `y_{t,a}` associated with `x_{t,a}` (p.4: "Each feature vector `x_{t,a}` is
  associated with an unknown stochastic reward `y_{t,a} ∈ [0,1]`");
* `D t ω`, the delay `D_t` of the reward of round `t` (p.5);
* `α t ω ∈ [K]`, the random arm drawn in an exploration round of Algorithm 1 (p.7, line 2:
  "randomly choose `α_t ∈ [K]`").

**Formalization Note.** Rounds are indexed `1, 2, …`; index `0` is unused by every definition of
this mission. Vectors of `ℝ^d` are `Fin d → ℝ`. The reward is a full table `y_{t,a}` over arms, as
on p.4; the learner only sees `y_{t,a_t}`. Delays are real valued. The distributional assumptions
are not part of this structure; they are the separate hypotheses `RoundModel`, `RewardModel`,
`Assumption1`, `TailEnvelope` and `DelayIndependent`. -/
structure Env (Ω : Type*) (d K : ℕ) where
  /-- Feature vector `x_{t,a}` of arm `a` at round `t`. -/
  x : ℕ → Ω → Fin K → Fin d → ℝ
  /-- Reward `y_{t,a}` of arm `a` at round `t`. -/
  y : ℕ → Ω → Fin K → ℝ
  /-- Delay `D_t` of the reward of round `t`. -/
  D : ℕ → Ω → ℝ
  /-- Exploration draw `α_t ∈ [K]`. -/
  α : ℕ → Ω → Fin K

end DelayedGLCB


