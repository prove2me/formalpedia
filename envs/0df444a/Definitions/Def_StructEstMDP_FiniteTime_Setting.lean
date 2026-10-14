-- Prove2me | Definitions.Def_StructEstMDP_FiniteTime_Setting
-- name    : StructEstMDP_FiniteTime_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T03:11:36.940683+00:00
-- url     : https://prove2.me/theorems/d6f58cc8-2e24-4113-b9a9-f42e544c8e50
-- title:
--   pp. 3–11, 23 — soft values and soft-optimal Q-function, L̂(θ; D), visitation, Assumptions 1–3, and the ML-IRL run (Algorithm 1)
-- statement:
--   This module fixes the setting of Zeng, Hong and Garcia: an entropy-regularized Markov decision process with a parameterized reward, the surrogate likelihood the paper maximizes, the paper's three standing assumptions, and a run of its single-loop algorithm ML-IRL.
--
--   **The MDP.** Let $\mathcal S$ and $\mathcal A$ be finite nonempty sets of states and actions, $P(s'\mid s,a)$ a transition kernel, $\rho$ a probability distribution on $\mathcal S$ (the initial distribution), $\gamma\in[0,1)$ a discount factor, and $r(s,a;\theta)$ a reward depending on a parameter $\theta\in\mathbb R^p$. A policy $\pi(a\mid s)$ gives a distribution over actions at each state. The entropy of $\pi(\cdot\mid s)$ is $\mathcal H(\pi(\cdot\mid s))=-\sum_a\pi(a\mid s)\log\pi(a\mid s)$, with $0\log 0=0$.
--
--   1. **Soft values of a pair $(\theta,\pi)$** (14a)–(14b):
--   $$V(s)=\mathbb E_{\tau\sim\pi}\Big[\sum_{t=0}^\infty\gamma^t\big(r(s_t,a_t;\theta)+\mathcal H(\pi(\cdot\mid s_t))\big)\,\Big|\,s_0=s\Big],\qquad Q(s,a)=r(s,a;\theta)+\gamma\,\mathbb E_{s'\sim P(\cdot\mid s,a)}[V(s')].$$
--   2. **The soft-optimal Q-function** $Q_\theta$ is the fixed point of the soft-Bellman operator $\Lambda_\theta Q(s,a)=r(s,a;\theta)+\gamma\sum_{s'}P(s'\mid s,a)\log\sum_b e^{Q(s',b)}$, which is (1) with the Gumbel expectation in closed form; $V_\theta(s)=\log\sum_a e^{Q_\theta(s,a)}$ (5b) and $\pi_\theta(a\mid s)=e^{Q_\theta(s,a)}/\sum_b e^{Q_\theta(s,b)}$ (5c). More generally $\mathrm{softmax}(Q)$ denotes the policy $e^{Q(s,a)}/\sum_b e^{Q(s,b)}$.
--   3. **Norms.** $\|f\|_\infty=\max_{s,a}|f(s,a)|$; $\|f\|_F=(\sum_{s,a}f(s,a)^2)^{1/2}$ is the Euclidean norm on $\mathbb R^{|\mathcal S|\times|\mathcal A|}$; $\|d-d'\|_{TV}=\tfrac12\sum_{s,a}|d(s,a)-d'(s,a)|$.
--   4. **Discounted means.** For a dataset $\mathcal D=(\tau_1,\dots,\tau_m)$ of state-action trajectories, $\mathbb E_{\tau\sim\mathcal D}[\sum_t\gamma^tf(s_t,a_t)]=\frac1m\sum_j\sum_t\gamma^tf(\tau_j(t))$; for a policy $\pi$, $\mathbb E_{\tau\sim\pi}[\sum_t\gamma^tf(s_t,a_t)]$ is the same discounted mean along the Markov chain with $s_0\sim\rho$, $a_t\sim\pi(\cdot\mid s_t)$, $s_{t+1}\sim P(\cdot\mid s_t,a_t)$. The state-action visitation measure is $d(s,a;\pi)=(1-\gamma)\pi(a\mid s)\sum_t\gamma^tP^\pi(s_t=s\mid s_0\sim\rho)$ (p. 23). The gradient estimator is $h(\theta;\tau)=\sum_t\gamma^t\nabla_\theta r(s_t,a_t;\theta)$ (17).
--   5. **Likelihoods.** The surrogate likelihood (9) is
--   $$\widehat L(\theta;\mathcal D)=\mathbb E_{\tau\sim\mathcal D}\Big[\sum_{t=0}^\infty\gamma^tr(s_t,a_t;\theta)\Big]-\mathbb E_{s_0\sim\rho}[V_\theta(s_0)],$$
--   and the expert log-likelihood (4a) is $L(\theta)=\mathbb E_{\tau\sim\pi^E}[\sum_t\gamma^t\log\pi_\theta(a_t\mid s_t)]$ with $s_0\sim\rho$.
--   6. **Assumptions.** Assumption 1: $0\le r(s,a;\theta)\le C_r$ with $C_r>0$. Assumption 2: for every policy $\pi$ there are a stationary distribution $\mu_\pi$, $\kappa>0$ and $\varrho\in(0,1)$ with $\sup_s\|P(s_t\in\cdot\mid s_0=s,\pi)-\mu_\pi\|_{TV}\le\kappa\varrho^t$ for all $t$. Assumption 3: each $r(s,a;\cdot)$ is differentiable with $\|\nabla_\theta r\|\le L_r$ and $\|\nabla_\theta r(s,a;\theta_1)-\nabla_\theta r(s,a;\theta_2)\|\le L_g\|\theta_1-\theta_2\|$, $L_r,L_g>0$.
--   7. **A run of Algorithm 1** with step size $\alpha$ and evaluation error $\varepsilon$ on a probability space with filtration $(\mathcal F_k)$: $\theta_0$ and the policy $\pi_0$ are given; at every iteration $\|\widehat Q_k-Q_k\|_\infty\le\varepsilon$ where $Q_k$ is the soft Q-function of $(\theta_k,\pi_k)$; $\pi_{k+1}=\mathrm{softmax}(\widehat Q_k)$ (15); the expert trajectory $\tau^E_k$ belongs to $\mathcal D$; $\theta_{k+1}=\theta_k+\alpha\big(h(\theta_k;\tau^E_k)-h(\theta_k;\tau^A_k)\big)$ (17)–(18); $\theta_k$ and $\widehat Q_k$ are $\mathcal F_k$-measurable, the sampled gradients are $\mathcal F_{k+1}$-measurable, and
--   $$\mathbb E[h(\theta_k;\tau^E_k)\mid\mathcal F_k]=\mathbb E_{\tau\sim\mathcal D}\Big[\sum_t\gamma^t\nabla_\theta r(s_t,a_t;\theta_k)\Big],\qquad \mathbb E[h(\theta_k;\tau^A_k)\mid\mathcal F_k]=\mathbb E_{\tau\sim\pi_{k+1}}\Big[\sum_t\gamma^t\nabla_\theta r(s_t,a_t;\theta_k)\Big].$$
--
--   These objects are the vocabulary of Theorem 1 and of every lemma on its proof path.
--
--   **Formalization Note** The finite-MDP primitives (kernel, policy, occupation distribution $P^\pi(s_t=\cdot\mid s_0)$, discounted value) are the published `FoundationsML.ReinforcementLearning` definitions; the soft value of $(\theta,\pi)$ is the published `PolicyValue` with reward $r+\mathcal H(\pi(\cdot\mid s))$. $Q_\theta$ is selected by `Classical.epsilon` among fixed points of $\Lambda_\theta$; for a transition kernel and $0\le\gamma<1$, $\Lambda_\theta$ is a $\gamma$-contraction in $\|\cdot\|_\infty$, so the fixed point exists and is unique. Discounted sums are `tsum`s of bounded terms times $\gamma^t$, hence summable. Assumption 2's "irreducible and aperiodic" is the reason the mixing bound holds; the bound is what the paper uses, and it is what is stated; the paper's mixing rate $\rho$ is renamed $\varrho$ because $\rho$ is also the initial distribution. Differentiability in Assumption 3 is implicit on the page (it writes $\nabla_\theta r$). The two sampling steps of Algorithm 1 enter only through the conditional means of the sampled gradients, which is the only way the proof uses them; they hold when $\tau^E_k$ is uniform on $\mathcal D$ and $\tau^A_k$ is a $\pi_{k+1}$-trajectory from $\rho$, drawn given the past. The parameter space $\mathbb R^p$ is `EuclideanSpace ℝ (Fin p)`, so $\|\theta\|$ and $\|\nabla_\theta r\|$ are Euclidean norms.
-- source:
--   Zeng, Hong and Garcia, Structural Estimation of Markov Decision Processes in High-Dimensional State Space with Finite-Time Guarantees, arXiv:2210.01282v3, pp. 3–11, §2–§5: (1), (4a), (5a)–(5c), (9), (14a)–(14b), (15), (17), (18), Algorithm 1, Assumptions 1–3; p. 23 (visitation measure d(s,a;π))

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedTransition
import Definitions.Def_FoundationsML_ReinforcementLearning_OccupationDist
import Definitions.Def_FoundationsML_ReinforcementLearning_PolicyValue

namespace StructEstMDP.FiniteTime

open FoundationsML.ReinforcementLearning MeasureTheory

/-! # The entropy-regularized MDP, the surrogate likelihood and the ML-IRL run

Zeng, Hong and Garcia, *Structural Estimation of Markov Decision Processes in High-Dimensional
State Space with Finite-Time Guarantees*, arXiv:2210.01282v3, §2–§5 (pp. 3–12) and p. 23.

The MDP is finite: `S` and `A` are finite types, `P s a s'` is `P(s'|s,a)`, a policy is
`π : S → A → ℝ` with `π s a = π(a|s)`, and the reward parameter lives in
`ℝᵖ = EuclideanSpace ℝ (Fin p)`. -/

/-- A probability distribution on a finite type (the initial distribution `ρ`, p. 5). -/
def IsDist {X : Type*} [Fintype X] (μ : X → ℝ) : Prop :=
  (∀ x, 0 ≤ μ x) ∧ ∑ x, μ x = 1

/-- Shannon entropy `H(q) = −∑ₐ q(a) log q(a)` (p. 5), with `0 log 0 = 0`. -/
noncomputable def entropy {A : Type*} [Fintype A] (q : A → ℝ) : ℝ :=
  ∑ a, Real.negMulLog (q a)

/-- The entropy-regularized reward `r(s,a;θ) + H(π(·|s))` of (14a), p. 9. -/
noncomputable def softReward {S A : Type*} [Fintype A] {p : ℕ}
    (r : S → A → EuclideanSpace ℝ (Fin p) → ℝ) (θ : EuclideanSpace ℝ (Fin p))
    (π : S → A → ℝ) : S → A → ℝ :=
  fun s a => r s a θ + entropy (π s)

/-- Soft value of the pair `(θ, π)`, (14a), p. 9:
`V(s) = E_{τ∼π}[∑_{t≥0} γᵗ (r(s_t,a_t;θ) + H(π(·|s_t))) | s₀ = s]`. -/
noncomputable def softV {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] {p : ℕ}
    (P : S → A → S → ℝ) (γ : ℝ) (r : S → A → EuclideanSpace ℝ (Fin p) → ℝ)
    (θ : EuclideanSpace ℝ (Fin p)) (π : S → A → ℝ) (s : S) : ℝ :=
  PolicyValue π P (softReward r θ π) γ s

/-- Soft Q-function of the pair `(θ, π)`, (14b), p. 9:
`Q(s,a) = r(s,a;θ) + γ E_{s'∼P(·|s,a)}[V(s')]` (no entropy bonus at `t = 0`). -/
noncomputable def softQ {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] {p : ℕ}
    (P : S → A → S → ℝ) (γ : ℝ) (r : S → A → EuclideanSpace ℝ (Fin p) → ℝ)
    (θ : EuclideanSpace ℝ (Fin p)) (π : S → A → ℝ) (s : S) (a : A) : ℝ :=
  r s a θ + γ * ∑ s', P s a s' * softV P γ r θ π s'

/-- `log ∑ₐ exp Q(s,a)`, (5b), p. 5. -/
noncomputable def logSumExp {S A : Type*} [Fintype A] (Q : S → A → ℝ) (s : S) : ℝ :=
  Real.log (∑ a, Real.exp (Q s a))

/-- The softmax policy `π(a|s) = exp Q(s,a) / ∑_b exp Q(s,b)`, (5c) and (15). -/
noncomputable def softmax {S A : Type*} [Fintype A] (Q : S → A → ℝ) : S → A → ℝ :=
  fun s a => Real.exp (Q s a) / ∑ b, Real.exp (Q s b)

/-- The soft-Bellman operator `Λ_θ` of (1), with the Gumbel expectation in the closed form
(5a)–(5b): `Λ_θ Q(s,a) = r(s,a;θ) + γ ∑_{s'} P(s'|s,a) log ∑_b exp Q(s',b)`. -/
noncomputable def softBellman {S A : Type*} [Fintype S] [Fintype A] {p : ℕ}
    (P : S → A → S → ℝ) (γ : ℝ) (r : S → A → EuclideanSpace ℝ (Fin p) → ℝ)
    (θ : EuclideanSpace ℝ (Fin p)) (Q : S → A → ℝ) : S → A → ℝ :=
  fun s a => r s a θ + γ * ∑ s', P s a s' * logSumExp Q s'

/-- The soft-optimal Q-function `Q_θ`: the fixed point of `Λ_θ` (p. 4, (5a)). For a transition
kernel and `0 ≤ γ < 1`, `Λ_θ` is a `γ`-contraction in the sup norm, so the fixed point exists
and is unique, and `Classical.epsilon` selects it. -/
noncomputable def optQ {S A : Type*} [Fintype S] [Fintype A] {p : ℕ}
    (P : S → A → S → ℝ) (γ : ℝ) (r : S → A → EuclideanSpace ℝ (Fin p) → ℝ)
    (θ : EuclideanSpace ℝ (Fin p)) : S → A → ℝ :=
  Classical.epsilon (fun Q : S → A → ℝ => softBellman P γ r θ Q = Q)

/-- The soft-optimal value `V_θ(s) = log ∑ₐ exp Q_θ(s,a)`, (5b), p. 5. -/
noncomputable def optV {S A : Type*} [Fintype S] [Fintype A] {p : ℕ}
    (P : S → A → S → ℝ) (γ : ℝ) (r : S → A → EuclideanSpace ℝ (Fin p) → ℝ)
    (θ : EuclideanSpace ℝ (Fin p)) (s : S) : ℝ :=
  logSumExp (optQ P γ r θ) s

/-- The soft-optimal policy `π_θ = softmax(Q_θ)`, (5c), p. 5. -/
noncomputable def optPolicy {S A : Type*} [Fintype S] [Fintype A] {p : ℕ}
    (P : S → A → S → ℝ) (γ : ℝ) (r : S → A → EuclideanSpace ℝ (Fin p) → ℝ)
    (θ : EuclideanSpace ℝ (Fin p)) : S → A → ℝ :=
  softmax (optQ P γ r θ)

/-- `‖f‖_∞ = max_{s,a} |f(s,a)|` (pp. 12, 20). -/
noncomputable def supNorm {S A : Type*} [Fintype S] [Nonempty S] [Fintype A] [Nonempty A]
    (f : S → A → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun x : S × A => |f x.1 x.2|)

/-- The Euclidean (Frobenius) norm `(∑_{s,a} f(s,a)²)^{1/2}` on `ℝ^{|S|×|A|}` (Lemma 5, p. 19;
"the conversion between Frobenius norm and infinity norm", p. 24). -/
noncomputable def frobNorm {S A : Type*} [Fintype S] [Fintype A] (f : S → A → ℝ) : ℝ :=
  Real.sqrt (∑ s, ∑ a, f s a ^ 2)

/-- A state-action trajectory `τ = {(s_t, a_t)}_{t ≥ 0}` (p. 21). -/
abbrev Traj (S A : Type*) := ℕ → S × A

/-- `h(θ; τ) = ∑_{t ≥ 0} γᵗ ∇_θ r(s_t, a_t; θ)`, (17), p. 10. -/
noncomputable def hGrad {S A : Type*} {p : ℕ} (γ : ℝ)
    (r : S → A → EuclideanSpace ℝ (Fin p) → ℝ) (θ : EuclideanSpace ℝ (Fin p))
    (τ : Traj S A) : EuclideanSpace ℝ (Fin p) :=
  ∑' t : ℕ, γ ^ t • gradient (r (τ t).1 (τ t).2) θ

/-- `E_{τ∼D}[∑_{t≥0} γᵗ f(s_t,a_t)]` for a dataset `D = (τ_1, …, τ_m)` of trajectories, with
`τ ∼ D` uniform on `D` (p. 6). -/
noncomputable def dataMean {S A E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (γ : ℝ) {m : ℕ} (D : Fin m → Traj S A) (f : S × A → E) : E :=
  (m : ℝ)⁻¹ • ∑ j, ∑' t : ℕ, γ ^ t • f (D j t)

/-- `P^π(s_t = s | s₀ ∼ ρ)`. -/
noncomputable def stateDist {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (ρ : S → ℝ) (π : S → A → ℝ) (t : ℕ) (s : S) : ℝ :=
  ∑ s₀, ρ s₀ * OccupationDist π P s₀ t s

/-- `E_{τ∼π}[∑_{t≥0} γᵗ f(s_t,a_t)]` with `s₀ ∼ ρ`, `a_t ∼ π(·|s_t)`, `s_{t+1} ∼ P(·|s_t,a_t)`. -/
noncomputable def polMean {S A E : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : S → A → S → ℝ) (γ : ℝ) (ρ : S → ℝ) (π : S → A → ℝ) (f : S × A → E) : E :=
  ∑' t : ℕ, γ ^ t • ∑ s, ∑ a, (stateDist P ρ π t s * π s a) • f (s, a)

/-- The state-action visitation measure `d(s,a;π) = (1−γ) π(a|s) ∑_{t≥0} γᵗ P^π(s_t = s | s₀ ∼ ρ)`
(p. 23, below (48)). -/
noncomputable def visitation {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (γ : ℝ) (ρ : S → ℝ) (π : S → A → ℝ) (s : S) (a : A) : ℝ :=
  (1 - γ) * π s a * ∑' t : ℕ, γ ^ t * stateDist P ρ π t s

/-- Total variation distance `‖d − d'‖_TV = ½ ∑_{s,a} |d(s,a) − d'(s,a)|` (as used in (48)(ii)). -/
noncomputable def tvDist {S A : Type*} [Fintype S] [Fintype A] (d d' : S → A → ℝ) : ℝ :=
  (1 / 2) * ∑ s, ∑ a, |d s a - d' s a|

/-- The surrogate likelihood (9), p. 7:
`L̂(θ; D) = E_{τ∼D}[∑_{t≥0} γᵗ r(s_t,a_t;θ)] − E_{s₀∼ρ}[V_θ(s₀)]`. -/
noncomputable def Lhat {S A : Type*} [Fintype S] [Fintype A] {p m : ℕ}
    (P : S → A → S → ℝ) (γ : ℝ) (ρ : S → ℝ) (r : S → A → EuclideanSpace ℝ (Fin p) → ℝ)
    (D : Fin m → Traj S A) (θ : EuclideanSpace ℝ (Fin p)) : ℝ :=
  dataMean γ D (fun x => r x.1 x.2 θ) - ∑ s, ρ s * optV P γ r θ s

/-- The expert log-likelihood (4a), p. 5: `L(θ) = E_{τ∼π^E}[∑_{t≥0} γᵗ log π_θ(a_t|s_t)]`,
expert trajectories started from `ρ`. -/
noncomputable def Lexp {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] {p : ℕ}
    (P : S → A → S → ℝ) (γ : ℝ) (ρ : S → ℝ) (r : S → A → EuclideanSpace ℝ (Fin p) → ℝ)
    (πE : S → A → ℝ) (θ : EuclideanSpace ℝ (Fin p)) : ℝ :=
  polMean P γ ρ πE (fun x => Real.log (optPolicy P γ r θ x.1 x.2))

/-- Assumption 1, p. 8: `0 ≤ r(s,a;θ) ≤ C_r` for all `s, a, θ`, with `C_r > 0`. -/
def Assumption1 {S A : Type*} {p : ℕ} (r : S → A → EuclideanSpace ℝ (Fin p) → ℝ) (Cr : ℝ) :
    Prop :=
  0 < Cr ∧ ∀ s a θ, 0 ≤ r s a θ ∧ r s a θ ≤ Cr

/-- Assumption 2 (ergodic dynamics), p. 11, in the form the paper uses: for every policy `π`
there are a stationary distribution `μ_π`, `κ > 0` and `ϱ ∈ (0,1)` with
`sup_s ‖P(s_t ∈ · | s₀ = s, π) − μ_π‖_TV ≤ κ ϱᵗ` for all `t ≥ 0`. -/
def Assumption2 {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) : Prop :=
  ∀ π : S → A → ℝ, IsPolicy π →
    ∃ μ : S → ℝ, IsDist μ ∧ (∀ s', ∑ s, μ s * InducedTransition π P s s' = μ s') ∧
      ∃ κ : ℝ, 0 < κ ∧ ∃ ϱ ∈ Set.Ioo (0 : ℝ) 1, ∀ (s₀ : S) (t : ℕ),
        (1 / 2) * ∑ s, |OccupationDist π P s₀ t s - μ s| ≤ κ * ϱ ^ t

/-- Assumption 3 (Lipschitz reward), (19), p. 11: `r(s,a;·)` is differentiable,
`‖∇_θ r(s,a;θ)‖ ≤ L_r` and `‖∇_θ r(s,a;θ₁) − ∇_θ r(s,a;θ₂)‖ ≤ L_g ‖θ₁ − θ₂‖`, `L_r, L_g > 0`. -/
def Assumption3 {S A : Type*} {p : ℕ} (r : S → A → EuclideanSpace ℝ (Fin p) → ℝ)
    (Lr Lg : ℝ) : Prop :=
  0 < Lr ∧ 0 < Lg ∧ ∀ s a, Differentiable ℝ (r s a) ∧
    (∀ θ, ‖gradient (r s a) θ‖ ≤ Lr) ∧
    ∀ θ₁ θ₂, ‖gradient (r s a) θ₁ - gradient (r s a) θ₂‖ ≤ Lg * ‖θ₁ - θ₂‖

/-- A run of Algorithm 1 (ML-IRL), p. 10, with step size `α` and policy-evaluation error `ε`,
on a probability space `(Ω, Pr)` with filtration `ℱ` (`ℱ k` = the information before the
samples of iteration `k`). The two sampling steps enter through the conditional means of the
sampled gradients given `ℱ k`. -/
structure IsMLIRLRun {S A : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype A] [DecidableEq A] [Nonempty A] {p m : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : S → A → S → ℝ) (γ : ℝ) (ρ : S → ℝ) (r : S → A → EuclideanSpace ℝ (Fin p) → ℝ)
    (D : Fin m → Traj S A) (Pr : MeasureTheory.Measure Ω)
    (ℱ : MeasureTheory.Filtration ℕ mΩ) (α ε : ℝ)
    (θ₀ : EuclideanSpace ℝ (Fin p)) (π₀ : S → A → ℝ)
    (θ : ℕ → Ω → EuclideanSpace ℝ (Fin p)) (π Qhat : ℕ → Ω → S → A → ℝ)
    (τE τA : ℕ → Ω → Traj S A) : Prop where
  /-- Input: the reward parameter `θ₀`. -/
  init_theta : ∀ ω, θ 0 ω = θ₀
  /-- Input: the policy `π₀`. -/
  init_policy : ∀ ω, π 0 ω = π₀
  /-- `π₀` is a policy. -/
  init_isPolicy : IsPolicy π₀
  /-- Policy evaluation: `‖Q̂_k − Q_k‖_∞ ≤ ε`, with `Q_k` the soft Q-function of `(θ_k, π_k)`. -/
  policy_eval : ∀ k ω, supNorm (Qhat k ω - softQ P γ r (θ k ω) (π k ω)) ≤ ε
  /-- Policy improvement (15): `π_{k+1}(a|s) ∝ exp Q̂_k(s,a)`. -/
  policy_improve : ∀ k ω, π (k + 1) ω = softmax (Qhat k ω)
  /-- Data sampling I: `τ^E_k` is a trajectory of the dataset. -/
  sample_expert : ∀ k ω, ∃ j, τE k ω = D j
  /-- Reward update (17)–(18): `θ_{k+1} = θ_k + α (h(θ_k; τ^E_k) − h(θ_k; τ^A_k))`. -/
  reward_update : ∀ k ω,
    θ (k + 1) ω = θ k ω + α • (hGrad γ r (θ k ω) (τE k ω) - hGrad γ r (θ k ω) (τA k ω))
  /-- `θ_k` is `ℱ k`-measurable. -/
  theta_adapted : ∀ k, Measurable[ℱ k] (θ k)
  /-- `Q̂_k` is `ℱ k`-measurable. -/
  qhat_adapted : ∀ k s a, Measurable[ℱ k] (fun ω => Qhat k ω s a)
  /-- The sampled expert gradient is `ℱ (k+1)`-measurable. -/
  gradE_measurable : ∀ k,
    StronglyMeasurable[ℱ (k + 1)] (fun ω => hGrad γ r (θ k ω) (τE k ω))
  /-- The sampled agent gradient is `ℱ (k+1)`-measurable. -/
  gradA_measurable : ∀ k,
    StronglyMeasurable[ℱ (k + 1)] (fun ω => hGrad γ r (θ k ω) (τA k ω))
  /-- Data sampling I, in mean: `E[h(θ_k; τ^E_k) | ℱ k] = E_{τ∼D}[∑ γᵗ ∇_θ r(s_t,a_t;θ_k)]`. -/
  condMean_expert : ∀ k,
    MeasureTheory.condExp (ℱ k) Pr (fun ω => hGrad γ r (θ k ω) (τE k ω)) =ᵐ[Pr]
      fun ω => dataMean γ D (fun x => gradient (r x.1 x.2) (θ k ω))
  /-- Data sampling II, in mean: `E[h(θ_k; τ^A_k) | ℱ k] = E_{τ∼π_{k+1}}[∑ γᵗ ∇_θ r(s_t,a_t;θ_k)]`,
  with `s₀ ∼ ρ`. -/
  condMean_agent : ∀ k,
    MeasureTheory.condExp (ℱ k) Pr (fun ω => hGrad γ r (θ k ω) (τA k ω)) =ᵐ[Pr]
      fun ω => polMean P γ ρ (π (k + 1) ω) (fun x => gradient (r x.1 x.2) (θ k ω))

end StructEstMDP.FiniteTime


