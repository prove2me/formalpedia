-- Prove2me | Definitions.Def_TPG_Model
-- name    : TPG_Model
-- status  : Definition
-- author  : @Wenqian Xing
-- created : 2026-10-12T03:01:43.414494+00:00
-- url     : https://prove2.me/theorems/bb6a0119-8254-42a7-b97f-ecc7455b8319
-- title:
--   §2 — nonstationary Markovian treatment model: Assumption 1 (mixing), kernel deviation $\delta$, trajectory law, value function $J$, GATE $\tau$
-- statement:
--   This definition file fixes the dynamic model of treatment of the source (§2.2–2.3) and the objects built from it.
--
--   **Convention.** Time is indexed by $t=0,1,\dots,T-1$; the source writes $t=1,\dots,T$, so time $t$ here is the source's time $t+1$.
--
--   1. **Total variation.** For real vectors $f,g$ on a finite set $S$, $\|f-g\|_{\mathrm{TV}}=\tfrac12\sum_{x\in S}|f(x)-g(x)|$ (`tvDist`). A probability vector is a nonnegative vector summing to one (`IsProbVec`).
--
--   2. **Environment** (`Env S`). A finite state space $S$ with, for every time $t\in\mathbb N$ and action $z\in\{0,1\}$ (`false` is control, `true` is treatment), a transition matrix $P_z^t$ with nonnegative entries and rows summing to one, so that $\mathbb P(X_{t+1}=x'\mid X_t=x,Z_t=z)=P_z^t(x,x')$; a distribution $\rho$ of the initial state $X_0$; and for every state $x$ and action $z$ a probability distribution $R(\cdot\mid x,z)$ on $\mathbb R$ of the reward.
--
--   3. **Bounded rewards** (`Env.RewardBound M`): $R([-M,M]\mid x,z)=1$ for all $x,z$. The mean rewards are $r(x,z)=\int y\,R(dy\mid x,z)$ (`Env.r`) and $r_\theta(x)=\theta\,r(x,1)+(1-\theta)\,r(x,0)$ (`Env.rMix`).
--
--   4. **Kernels under $\pi_\theta$:** $P_\theta^t=\theta P_1^t+(1-\theta)P_0^t$ (`Env.PMix`), and the multi-step kernel $P_\theta^{a\to b}=P_\theta^{a}P_\theta^{a+1}\cdots P_\theta^{b-1}$, equal to the identity when $b\le a$ (`Env.PProd`).
--
--   5. **Assumption 1, mixing time** (`Env.Mixing T γ`): for every $t<T$, every action $z$ and every pair of probability vectors $f,f'$ on $S$,
--
--   $$\|f'P_z^t-fP_z^t\|_{\mathrm{TV}}\le\gamma\,\|f'-f\|_{\mathrm{TV}},\qquad (fP)(x')=\sum_{x}f(x)P(x,x').$$
--
--   The condition $0<\gamma<1$ is a separate hypothesis of each theorem.
--
--   6. **Kernel deviation** (`Env.delta T`): $\delta=\sup_{t<T}\sup_{x\in S}\|P_1^t(x,\cdot)-P_0^t(x,\cdot)\|_{\mathrm{TV}}$.
--
--   7. **Trajectories.** A trajectory of horizon $T$ is $\omega=(X_t,Z_t,Y_t)_{t<T}$ (`Traj S T`, with coordinate maps `X`, `Z`, `Y`). For a sequence $q=(q_t)_{t\ge0}$ of treatment probabilities, `Env.pathWeight` is the probability of a state path $x$ and an action path $z$,
--
--   $$\rho(x_0)\prod_{s+1<T}P_{z_s}^{s}(x_s,x_{s+1})\prod_{t<T}q_t^{\,z_t}(1-q_t)^{1-z_t},$$
--
--   and `Env.trajLaw T q` is the law of the trajectory when $X_0\sim\rho$, the actions are independent with $\mathbb P(Z_t=1)=q_t$, the state follows $P^t_{Z_t}$, and, given the states and actions, the rewards are independent with $Y_t\sim R(\cdot\mid X_t,Z_t)$. `Env.expLaw T θ` is the case $q_t\equiv\theta$: the law under the Bernoulli randomization policy $\pi_\theta$.
--
--   8. **Value function and estimand** (`Env.J`, `Env.gate`):
--
--   $$J(\theta)=\frac1T\sum_{t<T}\mathbb E_\theta[Y_t],\qquad \tau=\frac1T\sum_{t<T}\bigl(\mathbb E_1[Y_t]-\mathbb E_0[Y_t]\bigr).$$
--
--   $\tau$ is the global average treatment effect (GATE).
--
--   Every statement of the mission is expressed through these objects.
--
--   **Formalization Note** Kernels are stored for all $t\in\mathbb N$; a statement with horizon $T$ involves $P^t$ only for $t<T$, which are the source's $P^1,\dots,P^T$. The trajectory law is constructed as a finite mixture, over the pairs of a state path and an action path, of products of point masses and reward laws. For $q_t\notin[0,1]$ negative path weights are replaced by $0$ and the result is not a probability law; no statement uses such $q$ except through values of $J$ away from the point of interest. For $T=0$ the averages $J$ and $\tau$ equal $0$.
-- source:
--   Johari, Peng, Xing, Estimation of Treatment Effects Under Nonstationarity via the Truncated Policy Gradient Estimator, revised manuscript of October 2026 (revision of arXiv:2506.05308v3, https://arxiv.org/abs/2506.05308); numbering follows the revised manuscript. §2.2–2.3, pp. 8–10: transition kernels, Assumption 1, rewards, policies π_θ, eq. (1), definition of the GATE; Theorem 1, p. 11 (kernel deviation δ); eq. (6), p. 13 (value function J); Appendix A.1–A.2, p. 27 (multi-step kernels).

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace TPG

/-- Total variation distance between two real vectors on a finite set,
with the convention `‖f - g‖_TV = (1/2) ‖f - g‖₁`. -/
noncomputable def tvDist {S : Type} [Fintype S] (f g : S → ℝ) : ℝ :=
  (1 / 2) * ∑ x, |f x - g x|

/-- `f` is a probability distribution on the finite set `S`. -/
def IsProbVec {S : Type} [Fintype S] (f : S → ℝ) : Prop :=
  (∀ x, 0 ≤ f x) ∧ ∑ x, f x = 1

/-- A nonstationary Markovian environment with finite state space `S` and binary action
(`true` = treatment, `false` = control). Time is indexed by `t = 0, 1, 2, …`
(the source's time `t + 1`).

* `P t z` is the transition matrix used between times `t` and `t + 1` under action `z`;
* `ρ` is the distribution of the initial state;
* `R x z` is the distribution of the real-valued reward when action `z` is taken in state `x`. -/
structure Env (S : Type) [Fintype S] where
  P : ℕ → Bool → Matrix S S ℝ
  P_nonneg : ∀ (t : ℕ) (z : Bool) (x x' : S), 0 ≤ P t z x x'
  P_row_sum : ∀ (t : ℕ) (z : Bool) (x : S), ∑ x', P t z x x' = 1
  ρ : S → ℝ
  ρ_nonneg : ∀ x : S, 0 ≤ ρ x
  ρ_sum : ∑ x, ρ x = 1
  R : S → Bool → Measure ℝ
  R_prob : ∀ (x : S) (z : Bool), IsProbabilityMeasure (R x z)

instance {S : Type} [Fintype S] (E : Env S) (x : S) (z : Bool) :
    IsProbabilityMeasure (E.R x z) := E.R_prob x z

section Kernels

variable {S : Type} [Fintype S]

/-- Rewards are almost surely bounded by `M`: `R([-M, M] | x, z) = 1` for all `x, z`. -/
def Env.RewardBound (E : Env S) (M : ℝ) : Prop :=
  ∀ (x : S) (z : Bool), E.R x z (Set.Icc (-M) M) = 1

/-- Expected reward `r(x, z) = ∫ y R(dy | x, z)`. -/
noncomputable def Env.r (E : Env S) (z : Bool) (x : S) : ℝ :=
  ∫ y, y ∂(E.R x z)

/-- Expected reward `r_θ(x) = θ r(x, 1) + (1 - θ) r(x, 0)` under the policy `π_θ`. -/
noncomputable def Env.rMix (E : Env S) (θ : ℝ) (x : S) : ℝ :=
  θ * E.r true x + (1 - θ) * E.r false x

/-- Transition matrix `P_θ^t = θ P_1^t + (1 - θ) P_0^t` under the policy `π_θ`. -/
noncomputable def Env.PMix (E : Env S) (θ : ℝ) (t : ℕ) : Matrix S S ℝ :=
  θ • E.P t true + (1 - θ) • E.P t false

/-- Multi-step kernel `P_θ^{a → b} = P_θ^a P_θ^{a+1} ⋯ P_θ^{b-1}`
(the identity matrix when `b ≤ a`). -/
noncomputable def Env.PProd [DecidableEq S] (E : Env S) (θ : ℝ) (a b : ℕ) : Matrix S S ℝ :=
  ((List.Ico a b).map (fun u => E.PMix θ u)).prod

/-- Assumption 1 (mixing time) over the horizon `T` with contraction constant `γ`:
for every time `t < T`, every action `z` and every pair of probability distributions
`f, f'` on `S`, `‖f' P_z^t - f P_z^t‖_TV ≤ γ ‖f' - f‖_TV`. -/
def Env.Mixing (E : Env S) (T : ℕ) (γ : ℝ) : Prop :=
  ∀ t : ℕ, t < T → ∀ (z : Bool) (f f' : S → ℝ), IsProbVec f → IsProbVec f' →
    tvDist (Matrix.vecMul f' (E.P t z)) (Matrix.vecMul f (E.P t z)) ≤ γ * tvDist f' f

/-- Kernel deviation
`δ = sup_{t < T} sup_x ‖P_1^t(x, ·) - P_0^t(x, ·)‖_TV` over the horizon `T`. -/
noncomputable def Env.delta (E : Env S) (T : ℕ) : ℝ :=
  ⨆ t : Fin T, ⨆ x : S, tvDist (E.P (t : ℕ) true x) (E.P (t : ℕ) false x)

end Kernels

section Trajectory

variable {S : Type} [Fintype S]

/-- A trajectory `(X_t, Z_t, Y_t)_{t < T}` of states, actions and rewards. -/
abbrev Traj (S : Type) (T : ℕ) : Type := Fin T → S × Bool × ℝ

/-- State at time `t`. -/
def X {T : ℕ} (t : Fin T) (ω : Traj S T) : S := (ω t).1

/-- Action (treatment indicator) at time `t`. -/
def Z {T : ℕ} (t : Fin T) (ω : Traj S T) : Bool := (ω t).2.1

/-- Reward at time `t`. -/
def Y {T : ℕ} (t : Fin T) (ω : Traj S T) : ℝ := (ω t).2.2

/-- Probability of the state path `x` and action path `z` over the horizon `T` when the
initial state has distribution `ρ`, the action at time `t` is treatment with probability
`q t` independently of everything else, and the state moves from time `s` to time `s + 1`
according to `P s (z s)`:
`ρ(x_0) · ∏_{s + 1 < T} P_{z_s}^s(x_s, x_{s+1}) · ∏_{t < T} (q_t if z_t else 1 - q_t)`. -/
noncomputable def Env.pathWeight (E : Env S) (T : ℕ) (q : ℕ → ℝ)
    (x : Fin T → S) (z : Fin T → Bool) : ℝ :=
  (∏ t : Fin T, if (t : ℕ) = 0 then E.ρ (x t) else 1)
    * (∏ s : Fin T, ∏ t : Fin T,
        if (s : ℕ) + 1 = (t : ℕ) then E.P (s : ℕ) (z s) (x s) (x t) else 1)
    * (∏ t : Fin T, if z t then q (t : ℕ) else 1 - q (t : ℕ))

/-- Law of the trajectory `(X_t, Z_t, Y_t)_{t < T}` when the action at time `t` is treatment
with probability `q t`: a mixture over state/action paths, weighted by `pathWeight`, of the
laws under which the path is fixed and the rewards are independent with
`Y_t ∼ R(· | x_t, z_t)`. -/
noncomputable def Env.trajLaw [MeasurableSpace S] (E : Env S) (T : ℕ) (q : ℕ → ℝ) :
    Measure (Traj S T) :=
  ∑ p : (Fin T → S) × (Fin T → Bool),
    ENNReal.ofReal (E.pathWeight T q p.1 p.2) •
      Measure.pi (fun t : Fin T =>
        (Measure.dirac (p.1 t)).prod ((Measure.dirac (p.2 t)).prod (E.R (p.1 t) (p.2 t))))

/-- Law of the trajectory under the Bernoulli randomization policy `π_θ`
(every action is treatment with probability `θ`). -/
noncomputable def Env.expLaw [MeasurableSpace S] (E : Env S) (T : ℕ) (θ : ℝ) :
    Measure (Traj S T) :=
  E.trajLaw T (fun _ => θ)

/-- Value function `J(θ) = (1/T) ∑_t E_{π_θ}[Y_t]`. -/
noncomputable def Env.J [MeasurableSpace S] (E : Env S) (T : ℕ) (θ : ℝ) : ℝ :=
  (1 / (T : ℝ)) * ∑ t : Fin T, ∫ ω, Y t ω ∂(E.expLaw T θ)

/-- Global average treatment effect
`τ = (1/T) ∑_t (E_{π_1}[Y_t] - E_{π_0}[Y_t])`. -/
noncomputable def Env.gate [MeasurableSpace S] (E : Env S) (T : ℕ) : ℝ :=
  (1 / (T : ℝ)) * ∑ t : Fin T,
    ((∫ ω, Y t ω ∂(E.expLaw T 1)) - ∫ ω, Y t ω ∂(E.expLaw T 0))

end Trajectory

end TPG


