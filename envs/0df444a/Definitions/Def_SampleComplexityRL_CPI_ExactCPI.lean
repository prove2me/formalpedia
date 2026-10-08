-- Prove2me | Definitions.Def_SampleComplexityRL_CPI_ExactCPI
-- name    : SampleComplexityRL_CPI_ExactCPI
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T02:12:01.646909+00:00
-- url     : https://prove2.me/theorems/8215fe7d-b575-4832-8d0d-5b0a7e51327b
-- title:
--   Horizon H, distributional and future values and advantages, the Exact CPI run, and the MDP of Example 7.4.1 (Ch. 7)
-- statement:
--   This module fixes the vocabulary of Chapter 7 of Kakade's thesis on top of the normalized $\gamma$-discounted model: finite state set $S$, finite action set $A$, transition kernel $P(s'\mid s,a)$, reward $r(s,a)$, discount $0\le\gamma<1$, normalized values $V_\pi(s)=(1-\gamma)\,\mathbb E[\sum_{t\ge0}\gamma^t r(s_t,a_t)\mid\pi,s_0=s]$, state-action values $Q_\pi$, advantages $A_\pi=Q_\pi-V_\pi$, and the discounted future state distribution $d_{\pi,\mu}(s)=(1-\gamma)\sum_{t\ge0}\gamma^t\Pr(s_t=s\mid\pi,s_0\sim\mu)$. Policies are stationary and stochastic, $\pi(a\mid s)$.
--
--   1. **Horizon time** (p. 88): $H=\dfrac{1}{1-\gamma}$.
--   2. **Point mass.** $\delta_{s_0}(s)=1$ if $s=s_0$ and $0$ otherwise; $d_{\pi,s_0}=d_{\pi,\delta_{s_0}}$.
--   3. **Advantage under a distribution** (Definition 7.1.1): for a state distribution $\nu$ and a stationary policy $h$,
--   $$A_\pi(\nu,h)=\mathbb E_{s\sim\nu}\,\mathbb E_{a\sim h(\cdot\mid s)}\big[A_\pi(s,a)\big].$$
--   4. **Future value and future state-action value** (Definition 7.2.1):
--   $$\mathbb V_\pi(\mu)=\mathbb E_{s\sim d_{\pi,\mu}}[V_\pi(s)],\qquad \mathbb Q_\pi(\mu,h)=\mathbb E_{s\sim d_{\pi,\mu}}\,\mathbb E_{a\sim h(\cdot\mid s)}[Q_\pi(s,a)].$$
--   The future advantage $\mathbb A_\pi(\mu,h)=\mathbb E_{s\sim d_{\pi,\mu}}\mathbb E_{a\sim h(\cdot\mid s)}[A_\pi(s,a)]$ is the published policy advantage of Kakade–Langford.
--   5. **ℓ1 distance** (p. 89): $\|p-q\|_1=\sum_x|p(x)-q(x)|$.
--   6. **Exact CPI run** (Algorithm 11, p. 90). For a class $\Pi$ of stationary policies, a reset distribution $\mu$ and an accuracy $\varepsilon$, sequences $\pi_0,\pi_1,\dots$ (current policies) and $\pi'_0,\pi'_1,\dots$ (chooser outputs) form a run if $\pi_0$ is a policy and, at every round $k$ that the algorithm reaches (all earlier tests $\mathbb A_{\pi_j}(\mu,\pi'_j)>\varepsilon/H$, $j<k$, passed):
--      - $\pi'_k\in\Pi$ and $\mathbb Q_{\pi_k}(\mu,h)\le\mathbb Q_{\pi_k}(\mu,\pi'_k)$ for all $h\in\Pi$ (the ExactPolicyChooser, line 2);
--      - if $\mathbb A_{\pi_k}(\mu,\pi'_k)>\varepsilon/H$, then
--      $$\pi_{k+1}=(1-\alpha_k)\pi_k+\alpha_k\pi'_k,\qquad \alpha_k=\frac{\mathbb A_{\pi_k}(\mu,\pi'_k)}{4H}$$
--      (lines 3(a)–(b)). The first round at which the test fails is where the algorithm halts and returns $\pi_k$.
--   7. **The MDP of Example 7.4.1** (p. 94): states $i,j$; actions $1,2$; at $i$ action $1$ is a self transition with reward $\tfrac12$ and action $2$ moves to $j$ with reward $1$; at $j$ both actions are self transitions, with rewards $\tfrac12$ and $0$; $\pi$ always plays action $1$ and $\pi'$ always plays action $2$.
--
--   These objects state the guarantees of conservative policy iteration: the improvement of a mixture update, the μ-optimality of policies with small advantages, and the halting and output guarantee of Exact CPI.
--
--   **Formalization Note** Values are normalized by $1-\gamma$ (Definition 2.2.4), so with rewards in $[0,1]$ they lie in $[0,1]$. Deterministic policies enter as indicator policies $\pi(a\mid s)=\mathbf 1[a=f(s)]$. In Lean the policy class is named `Pi` because `Π` is a reserved token. The run constrains the sequences only up to the halting round; nothing is required afterwards. The ExactPolicyChooser's argmax is a hypothesis on $\pi'_k$, so the run assumes, as the thesis does, that the maximum over $\Pi$ is attained. The actions $1,2$ of the example are the constructors `one`, `two`.
-- source:
--   Kakade, On the Sample Complexity of Reinforcement Learning, PhD thesis, University College London, 2003, p. 84 (Definitions 7.1.1, 7.1.2), p. 85 (Definition 7.2.1), p. 88 (horizon time H), p. 89 (ℓ1 distance), p. 90 (Algorithm 11, Exact CPI), p. 94 (Example 7.4.1)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_ApproxOptRL_Shared_Model
import Definitions.Def_ApproxOptRL_CPI_PolicyAdvantage
open ApproxOptRL.Shared ApproxOptRL.CPI FoundationsML.ReinforcementLearning

namespace SampleComplexityRL.CPI

/-- The horizon time `H = 1/(1 - γ)` (Kakade 2003, §7.3, p. 88). -/
noncomputable def horizon (γ : ℝ) : ℝ := 1 / (1 - γ)

/-- The point mass `δ_{s₀}` on the state `s₀`; `futureStateDist P γ π (pointMass s₀)` is the
thesis's `d_{π,s₀}` (Definition 7.1.2, p. 84, with `μ = δ_{s₀}`). -/
def pointMass {S : Type} [DecidableEq S] (s₀ : S) : S → ℝ :=
  fun s => if s = s₀ then 1 else 0

/-- The advantage of a stationary policy `h` with respect to `π` under the state distribution
`ν` (Definition 7.1.1, p. 84): `A_π(ν, h) = E_{s∼ν} E_{a∼h(·|s)}[A_π(s, a)]`. -/
noncomputable def distAdvantage {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (π : S → A → ℝ) (ν : S → ℝ)
    (h : S → A → ℝ) : ℝ :=
  ∑ s, ν s * ∑ a, h s a * advantage P r γ π s a

/-- The future value (Definition 7.2.1, p. 85): `𝕍_π(μ) = E_{s∼d_{π,μ}}[V_π(s)]`. -/
noncomputable def futureValue {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (π : S → A → ℝ) (μ : S → ℝ) : ℝ :=
  ∑ s, futureStateDist P γ π μ s * value P r γ π s

/-- The future state-action value (Definition 7.2.1, p. 85):
`ℚ_π(μ, h) = E_{s∼d_{π,μ}} E_{a∼h(·|s)}[Q_π(s, a)]`. -/
noncomputable def futureQValue {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (π : S → A → ℝ) (μ : S → ℝ)
    (h : S → A → ℝ) : ℝ :=
  ∑ s, futureStateDist P γ π μ s * ∑ a, h s a * qValue P r γ π s a

/-- The ℓ1 distance `‖p − q‖₁ = Σ_x |p(x) − q(x)|` of two functions on a finite set
(Kakade 2003, p. 89). -/
def l1Dist {S : Type} [Fintype S] (p q : S → ℝ) : ℝ :=
  ∑ s, |p s - q s|

/-- A run of Exact CPI (Algorithm 11, p. 90) for the policy class `Pi` (the thesis's `Π`), the
reset distribution `μ` and the accuracy `ε`. `π k` is the current policy when the ExactPolicyChooser is called for the
`(k+1)`-st time and `π' k` is the policy it returns. As long as the algorithm has not halted
before round `k` (every earlier test `𝔸_{π j}(μ, π' j) > ε/H` passed):
* `π' k ∈ Pi` maximizes the future state-action value `ℚ_{π k}(μ, ·)` over `Pi` (line 2);
* if `𝔸_{π k}(μ, π' k) > ε/H`, then `π (k+1) = (1 − α) π k + α π' k` with
  `α = 𝔸_{π k}(μ, π' k)/(4H)` (line 3).
The initial policy `π 0` is an arbitrary stationary policy (line 1). Nothing is required of the
sequences after the algorithm halts. Here `𝔸` is the future advantage (Definition 7.2.1),
`ApproxOptRL.CPI.policyAdvantage`. -/
structure IsExactCPIRun {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (μ : S → ℝ) (ε : ℝ)
    (Pi : Set (S → A → ℝ)) (π π' : ℕ → S → A → ℝ) : Prop where
  init : IsPolicy (π 0)
  chooser_mem : ∀ k : ℕ,
    (∀ j < k, ε / horizon γ < policyAdvantage P r γ (π j) μ (π' j)) → π' k ∈ Pi
  chooser_max : ∀ k : ℕ,
    (∀ j < k, ε / horizon γ < policyAdvantage P r γ (π j) μ (π' j)) →
      ∀ h ∈ Pi, futureQValue P r γ (π k) μ h ≤ futureQValue P r γ (π k) μ (π' k)
  update : ∀ k : ℕ,
    (∀ j < k, ε / horizon γ < policyAdvantage P r γ (π j) μ (π' j)) →
      ε / horizon γ < policyAdvantage P r γ (π k) μ (π' k) →
        π (k + 1) = mixPolicy (policyAdvantage P r γ (π k) μ (π' k) / (4 * horizon γ))
          (π k) (π' k)

/-- The two states `i`, `j` of Example 7.4.1 (p. 94). -/
inductive ExState
  | i
  | j
  deriving DecidableEq

instance : Fintype ExState :=
  ⟨{ExState.i, ExState.j}, fun x => by cases x <;> simp⟩

instance : Nonempty ExState := ⟨ExState.i⟩

/-- The two actions `1`, `2` of Example 7.4.1 (p. 94), written `one`, `two`. -/
inductive ExAction
  | one
  | two
  deriving DecidableEq

instance : Fintype ExAction :=
  ⟨{ExAction.one, ExAction.two}, fun x => by cases x <;> simp⟩

instance : Nonempty ExAction := ⟨ExAction.one⟩

/-- Transitions of Example 7.4.1: at `i`, action `1` is a self transition and action `2` goes
to `j`; at `j` both actions are self transitions. -/
def exP : ExState → ExAction → ExState → ℝ
  | .i, .one, .i => 1
  | .i, .one, .j => 0
  | .i, .two, .i => 0
  | .i, .two, .j => 1
  | .j, _, .i => 0
  | .j, _, .j => 1

/-- Rewards of Example 7.4.1: `r(i,1) = 1/2`, `r(i,2) = 1`, `r(j,1) = 1/2`, `r(j,2) = 0`. -/
noncomputable def exR : ExState → ExAction → ℝ
  | .i, .one => 1 / 2
  | .i, .two => 1
  | .j, .one => 1 / 2
  | .j, .two => 0

/-- The deterministic policy `π(i) = 1`, `π(j) = 1` of Example 7.4.1, as an indicator policy. -/
def exPi : ExState → ExAction → ℝ :=
  fun _ a => if a = ExAction.one then 1 else 0

/-- The deterministic policy `π'(i) = 2`, `π'(j) = 2` of Example 7.4.1, as an indicator
policy. -/
def exPi' : ExState → ExAction → ℝ :=
  fun _ a => if a = ExAction.two then 1 else 0

end SampleComplexityRL.CPI


