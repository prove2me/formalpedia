-- Prove2me | Definitions.Def_InfoRelaxTS_Monotone_Supplement_Duality
-- name    : InfoRelaxTS_Monotone_Supplement_Duality
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:54:10.250354+00:00
-- url     : https://prove2.me/theorems/31304de6-5cbd-4eda-b638-1c629d491a03
-- title:
--   §2.1, §2.3, §3, pp. 5–11 — policies Π_F, V(π, T, y) (7), V* (15)–(16), penalties, dual feasibility (18), W^z (19), z^ideal (22)
-- statement:
--   This file adds to the published Bayesian bandit model of §2.1 (arms $a\in\mathcal A=\{1,\dots,K\}$, reward laws $\mathcal R_a(\theta_a)$, conjugate priors $\mathcal P_a(y_a)$, Bayesian update $\mathcal U_a$, outcome $\omega=(\theta,(R_{a,n}))\sim\mathcal I(y)$, beliefs $y_t$ and posterior predictive means $\hat\mu_{a,n}$) the objects of the information relaxation duality of §3.
--
--   1. **Rewards (5).** Along an action sequence $a_{1:T}$ the reward at time $t$ is $r_t(a_{1:t},\omega)=R_{a_t,\,n_t(a_{1:t},a_t)}$, the next unobserved reward of the arm pulled.
--   2. **Non-anticipating policies $\Pi_{\mathbb F}$ (p. 5).** A policy $\pi$ consists of a private random seed $\xi$ with a probability law $\rho$, drawn independently of $\omega$, and measurable decision rules: the action $A^\pi_t$ is a measurable function of $\xi$ and of the rewards observed before time $t$ (the earlier actions are themselves functions of these). This covers all history-dependent and randomized policies.
--   3. **Performance (7).** $V(\pi,T,y)=\mathbb E_y\big[\sum_{t=1}^T r_t(A^\pi_{1:t},\omega)\big]$, the expectation over $\xi\sim\rho$ and $\omega\sim\mathcal I(y)$ independently.
--   4. **Bellman value (15)–(16).** $V^*(0,y)=0$ and
--   $$V^*(T+1,y)=\max_{a\in\mathcal A}\ \mathbb E_{y_a}\big[R_{a,1}+V^*(T,\mathcal U(y,a,R_{a,1}))\big],$$
--   the expectation over the predictive law of the next reward of arm $a$ under the belief $y_a$; the inner expectation is the page's $Q^*(T+1,y,a)$.
--   5. **Penalties, dual feasibility (18), the bound (19).** For a fixed horizon $T$ and prior $y$, a penalty assigns to each time $t$, action prefix $a_{1:t}$ and outcome $\omega$ a real number $z_t(a_{1:t},\omega)$. It is *dual feasible* if for every $\pi\in\Pi_{\mathbb F}$ the total penalty $\sum_{t=1}^T z_t(A^\pi_{1:t},\omega)$ has a finite expectation equal to $0$. The bound is
--   $$W^z(T,y)=\mathbb E_y\Big[\max_{a_{1:T}\in\mathcal A^T}\sum_{t=1}^T\big(r_t(a_{1:t},\omega)-z_t(a_{1:t},\omega)\big)\Big].$$
--   6. **The ideal penalty (22).**
--   $$z^{\rm ideal}_t(a_{1:t},\omega;T,y)=r_t-\mathbb E_y[r_t\mid H_{t-1}]+V^*(T-t,y_t)-\mathbb E_y\big[V^*(T-t,y_t)\mid H_{t-1}\big],$$
--   where $H_{t-1}=H_{t-1}(a_{1:t-1},\omega)$ is the history along the prefix and $y_t=y_t(a_{1:t},\omega;y)$. Given $H_{t-1}$, the next reward of $a_t$ has the predictive law under the current belief $y_{t-1}$, so $\mathbb E_y[r_t\mid H_{t-1}]=\bar\mu_{a_t}([y_{t-1}]_{a_t})$ and $\mathbb E_y[V^*(T-t,y_t)\mid H_{t-1}]=\mathbb E_{[y_{t-1}]_{a_t}}\big[V^*(T-t,\mathcal U(y_{t-1},a_t,R))\big]$; these versions define $z^{\rm ideal}$.
--
--   These are the objects of Theorem 1 and Proposition 3: weak duality bounds $V^*$ by $W^z$ for every dual feasible $z$, and the ideal penalty closes the gap.
--
--   **Formalization Note** Arms and times are 0-based (`Fin K`, `Fin T`); the paper's time $t$ is Lean's $t-1$, so $V^*(T-t,\cdot)$ is `Vstar (T - t - 1)` at Lean time `t`. A policy's seed lives in an arbitrary measurable type with a probability law, and the joint law is the product $\rho\otimes\mathcal I(y)$, which is the independence of the private randomization from $\omega$. The recursion for $V^*$ uses the consistent indexing $V^*(T,y)=\max_a Q^*(T,y,a)$ of (15), (89)–(90), (100) and Algorithm 1; the printed (16) reads $\max_a Q^*(T-1,y,a)$, a slip. The conditional expectations in (22) are the conjugate predictive versions, which agree almost surely with any version under the conjugacy assumption and make the pathwise inner problem well defined. Dual feasibility requires the expectation in (18) to exist (integrability of the total penalty along every policy), not each summand.
--
--   The penalty type allows arbitrary individual summands, including nonmeasurable ones, provided every policy's total penalty is integrable with mean zero. This generalizes the source's stochastic penalties: no separate measurability or integrability of individual summands is imposed. All definitions include the empty horizon, whose totals and values are zero.
-- source:
--   Min, Maglaras, Moallemi, Thompson Sampling with Information Relaxation Penalties, arXiv:1902.04251v2, pp. 5–11, (5)–(8), (15)–(16), (*), Definition 1 (18), (19), (22)

import Mathlib
import Definitions.Def_InfoRelaxTS_Monotone_Setting

namespace InfoRelaxTS.Monotone.Supplement

open MeasureTheory ProbabilityTheory InfoRelaxTS.Monotone

variable {K : ℕ} {Θ Y : Type*} [MeasurableSpace Θ] [MeasurableSpace Y]

/-- The reward (5) earned at time `t` (0-based; the paper's time `t + 1`) along the action
sequence `s`: the arm `s t` is pulled for the `(count s t (s t) + 1)`-th time, so the reward is
`R_{s t, count s t (s t) + 1}`, i.e. `(ω (s t)).2 (count s t (s t))`. -/
def rew {T : ℕ} (s : Fin T → Fin K) (t : Fin T) (ω : Outcome K Θ) : ℝ :=
  (ω (s t)).2 (count s (t : ℕ) (s t))

/-- A non-anticipating policy of `Π_𝔽` (§2.1, p. 5), randomized and history dependent: a private
seed `ξ ∈ Ξ` with law `ρ`, drawn independently of the outcome `ω`, and, for every time `t`
(0-based), a jointly measurable rule `act t ξ (r_0, …, r_{t-1})` choosing the next arm from the
seed and the rewards observed so far. The past actions are themselves functions of the seed and
the past rewards, so the rule sees the whole history `H_{t-1}` (6) together with the policy's
own randomization. -/
structure Policy (K : ℕ) : Type 1 where
  /-- The space of private random seeds. -/
  Ξ : Type
  /-- Its σ-algebra. -/
  [mΞ : MeasurableSpace Ξ]
  /-- The law of the seed. -/
  ρ : Measure Ξ
  [isProb : IsProbabilityMeasure ρ]
  /-- The decision rule at time `t`, given the seed and the `t` rewards observed so far. -/
  act : (t : ℕ) → Ξ → (Fin t → ℝ) → Fin K
  /-- Each decision rule is jointly measurable in the seed and the observed rewards. -/
  meas : ∀ t, Measurable fun p : Ξ × (Fin t → ℝ) => act t p.1 p.2

attribute [instance] Policy.mΞ Policy.isProb

/-- The first `n` actions `A^π_{1:n}` of the policy `π` for the seed `ξ` and the outcome `ω`,
built recursively: the action at time `n` is `π.act n ξ` applied to the rewards observed along
the first `n` actions. -/
def Policy.path (π : Policy K) (ξ : π.Ξ) (ω : Outcome K Θ) : (n : ℕ) → Fin n → Fin K
  | 0 => Fin.elim0
  | n + 1 => Fin.snoc (α := fun _ => Fin K) (π.path ξ ω n)
      (π.act n ξ fun i => rew (π.path ξ ω n) i ω)

/-- The joint law of the seed and the outcome, `ρ ⊗ ℐ(y)`: the seed is independent of `ω`. -/
noncomputable def Policy.law (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin K → Kernel Y Θ) (π : Policy K) (y : Fin K → Y) : Measure (π.Ξ × Outcome K Θ) :=
  π.ρ.prod (I R P y)

/-- The total reward `Σ_{t=1}^T r_t(A^π_{1:t}, ω)` earned by `π` over the horizon `T`. -/
def Policy.totalReward (π : Policy K) (T : ℕ) (ξ : π.Ξ) (ω : Outcome K Θ) : ℝ :=
  ∑ t : Fin T, rew (π.path ξ ω T) t ω

/-- The Bayesian performance (7) of the policy `π`:
`V(π, T, y) = 𝔼_y[Σ_{t=1}^T r_t(A^π_{1:t}, ω)]`. -/
noncomputable def V (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin K → Kernel Y Θ) (π : Policy K) (T : ℕ) (y : Fin K → Y) : ℝ :=
  ∫ p, π.totalReward T p.1 p.2 ∂(π.law R P y)

/-- The Bayesian optimal value by the Bellman equations (15)–(16): `V*(0, y) = 0` and
`V*(T + 1, y) = max_a 𝔼_{y_a}[R_{a,1} + V*(T, 𝒰(y, a, R_{a,1}))]`, the expectation over the
predictive law of the next reward of arm `a` (the page's `Q*(T + 1, y, a)`). -/
noncomputable def Vstar [NeZero K] (R : Fin K → Kernel Θ ℝ) (P : Fin K → Kernel Y Θ)
    (U : Fin K → Y → ℝ → Y) : ℕ → (Fin K → Y) → ℝ
  | 0, _ => 0
  | T + 1, y => Finset.univ.sup' Finset.univ_nonempty fun a =>
      ∫ r, (r + Vstar R P U T (Function.update y a (U a (y a) r))) ∂(pred R P a (y a))

/-- A penalty function (p. 10): `z t a ω` is the penalty `z_{t+1}(a_{1:t+1}, ω; T, y)` incurred at
time `t` (0-based) for the action prefix `a = (a_1, …, a_{t+1})` and the outcome `ω`, for a fixed
horizon `T` and prior `y`. -/
abbrev Penalty (K : ℕ) (Θ : Type*) : Type _ := (t : ℕ) → (Fin (t + 1) → Fin K) → Outcome K Θ → ℝ

/-- The prefix `(s_0, …, s_t)` of the action sequence `s`. -/
def pre {T : ℕ} (s : Fin T → Fin K) (t : Fin T) : Fin ((t : ℕ) + 1) → Fin K :=
  fun i => s ⟨i, by omega⟩

/-- The total penalty `Σ_{t=1}^T z_t(a_{1:t}, ω)` along the action sequence `s`. -/
def totalPen {T : ℕ} (z : Penalty K Θ) (s : Fin T → Fin K) (ω : Outcome K Θ) : ℝ :=
  ∑ t : Fin T, z t (pre s t) ω

/-- Definition 1 (dual feasibility), (18): for every non-anticipating policy `π ∈ Π_𝔽`, the total
penalty along the policy's actions has a well-defined (finite) expectation and it is zero,
`𝔼_y[Σ_{t=1}^T z_t(A^π_{1:t}, ω; T, y)] = 0`. -/
def DualFeasible (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)] (P : Fin K → Kernel Y Θ)
    (z : Penalty K Θ) (T : ℕ) (y : Fin K → Y) : Prop :=
  ∀ π : Policy K,
    Integrable (fun p => totalPen z (π.path p.1 p.2 T) p.2) (π.law R P y) ∧
      ∫ p, totalPen z (π.path p.1 p.2 T) p.2 ∂(π.law R P y) = 0

/-- The maximal value of the inner problem (∗) for the outcome `ω`:
`max_{a_{1:T} ∈ 𝒜^T} Σ_{t=1}^T (r_t(a_{1:t}, ω) - z_t(a_{1:t}, ω; T, y))`. -/
noncomputable def innerVal [NeZero K] (z : Penalty K Θ) (T : ℕ) (ω : Outcome K Θ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun s : Fin T → Fin K =>
    ∑ t : Fin T, (rew s t ω - z t (pre s t) ω)

/-- The performance bound (19): `W^z(T, y) = 𝔼_y[max_{a_{1:T}} Σ_t (r_t - z_t)]`, `ω ∼ ℐ(y)`. -/
noncomputable def W [NeZero K] (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin K → Kernel Y Θ) (z : Penalty K Θ) (T : ℕ) (y : Fin K → Y) : ℝ :=
  ∫ ω, innerVal z T ω ∂(I R P y)

/-- The ideal penalty (22) for horizon `T` and prior `y`, at time `t` (0-based) for the action
prefix `a = (a_0, …, a_t)` with last action `b = a_t`:
`z^ideal = r_t - 𝔼_y[r_t | H_{t-1}] + V*(T-t-1, y_{t+1}) - 𝔼_y[V*(T-t-1, y_{t+1}) | H_{t-1}]`
(the paper's `T - t` at its 1-based time `t`). Both conditional expectations given the history
along the prefix `(a_0, …, a_{t-1})` are taken in their conjugate predictive version: under the
current belief `y_t` the next reward of `b` has the predictive law `pred R P b (y_t b)`, so
`𝔼[r_t | H_{t-1}] = μ̄_b(y_t b) = μ̂_{b, n}` with `n` the earlier pulls of `b`, and
`𝔼[V*(T-t-1, y_{t+1}) | H_{t-1}] = ∫ V*(T-t-1, 𝒰(y_t, b, r)) d pred(b, y_t b)(r)`. -/
noncomputable def zIdeal [NeZero K] (R : Fin K → Kernel Θ ℝ) (P : Fin K → Kernel Y Θ)
    (U : Fin K → Y → ℝ → Y) (T : ℕ) (y : Fin K → Y) : Penalty K Θ :=
  fun t a ω =>
    rew a (Fin.last t) ω
      - muHat R P U y (a (Fin.last t)) (count a t (a (Fin.last t))) ω
      + Vstar R P U (T - t - 1) (ybel U y a (t + 1) ω)
      - ∫ r, Vstar R P U (T - t - 1)
          (Function.update (ybel U y a t ω) (a (Fin.last t))
            (U (a (Fin.last t)) (ybel U y a t ω (a (Fin.last t))) r))
          ∂(pred R P (a (Fin.last t)) (ybel U y a t ω (a (Fin.last t))))

end InfoRelaxTS.Monotone.Supplement


