-- Prove2me | Definitions.Def_SampleComplexityRL_MuPolicySearch_MuReset
-- name    : SampleComplexityRL_MuPolicySearch_MuReset
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T04:00:56.304035+00:00
-- url     : https://prove2.me/theorems/88266c14-1fcb-4bea-997e-21534eba4ea1
-- title:
--   μ-reset distributions, the μ-values V_{π,t}(μ), Q_{π,t}(μ,h), A_{π,t}(μ,h), policy classes Π₁^T and the NAPI run (Def. 6.2.1, §5.3, §6.2–6.3)
-- statement:
--   On top of the T-epoch model (horizon $T$, finite states $S$, finite actions $A$), this module defines the objects of Chapter 6 of Kakade's thesis.
--
--   1. **μ-reset distribution** (§6.2.1). A state-time distribution $\mu$ is given by its conditionals $\mu(\cdot\mid t)$, a probability distribution over $S$ for each $t<T$; it is uniform over times, so its joint law on $S\times\{0,\dots,T-1\}$ is $\mu(s,t)=\mu(s\mid t)/T$.
--   2. **ℓ1 distance** (p. 75). For two functions $p,q$ on $S\times\{0,\dots,T-1\}$, $\|p-q\|_1=\sum_{s}\sum_{t<T}|p(s,t)-q(s,t)|$.
--   3. **Generalized value functions** (Definition 6.2.1), for a policy $\pi$, a time $t$ and a deterministic decision rule $h:S\to A$:
--   $$V_{\pi,t}(\mu)=\mathbb E_{s\sim\mu(\cdot\mid t)}[V_{\pi,t}(s)],\quad Q_{\pi,t}(\mu,h)=\mathbb E_{s\sim\mu(\cdot\mid t)}[Q_{\pi,t}(s,h(s))],\quad A_{\pi,t}(\mu,h)=\mathbb E_{s\sim\mu(\cdot\mid t)}[A_{\pi,t}(s,h(s))].$$
--   4. **Policy classes** (p. 75). A class $\Pi_1$ of deterministic decision rules induces $\Pi=\Pi_1^T$: a deterministic non-stationary policy $\pi'$ belongs to $\Pi$ when $\pi'(\cdot,t)\in\Pi_1$ for every $t<T$.
--   5. **The NAPI / μ-PolicySearch run** (Algorithms 6 and 8). Start from an arbitrary deterministic policy $\pi_{\mathrm{init}}$ and update backward, $t=T-1,\dots,0$, setting $\tilde\pi(\cdot,t)=h_t$. The policy handed to the PolicyChooser at update $t$ uses $h_\tau$ at the epochs $\tau>t$ already updated and $\pi_{\mathrm{init}}$ at the epochs $\tau\le t$; the returned policy uses $h_t$ at every epoch $t<T$.
--   6. **Per-state error** (p. 62). If $\pi$ is the input policy at update $t$ and $h_t$ the output decision rule, $\varepsilon_t(s)=\max_{a\in A}Q_{\pi,t}(s,a)-Q_{\pi,t}(s,h_t(s))$.
--
--   These are the quantities in which the μ-optimality guarantee and the analysis of Exact μ-PolicySearch are stated.
--
--   **Formalization Note** The chapter works with deterministic classes $\Pi$ and $\Pi_1$ only (p. 69), so the generalized values are defined for deterministic decision rules $h$, with $\mathbb E_{a\sim h(\cdot\mid s)}$ evaluated at $a=h(s)$. The joint law `resetJoint` is $0$ for $t\ge T$. A run of the algorithm is described by the sequence of chosen decision rules `h` together with `init`; what the PolicyChooser must satisfy (an exact maximizer for Algorithm 8) is a hypothesis of the theorem that uses it, never built into the definition.
-- source:
--   Kakade, On the Sample Complexity of Reinforcement Learning, PhD thesis, University College London, 2003, p. 62 (§5.3.1–5.3.2, Algorithm 6, per state error), p. 73 (§6.2.1), p. 74 (Definition 6.2.1), p. 75 (Π = Π₁^T, ℓ1 distance), p. 76 (Algorithm 8)

import Mathlib
import Definitions.Def_SampleComplexityRL_Mismeasure_TEpoch
import Definitions.Def_SampleComplexityRL_PolicyGrad_TEpoch

namespace SampleComplexityRL.MuPolicySearch

/-- `μ` is a μ-reset state-time distribution (§6.2.1, p. 73): `μ t s` = μ(s | t), a probability
distribution over states for every time `t < T`; the joint distribution is uniform over the
times `{0, …, T-1}`. -/
def IsResetDist {S : Type} [Fintype S] (T : ℕ) (μ : ℕ → S → ℝ) : Prop :=
  ∀ t < T, (∀ s, 0 ≤ μ t s) ∧ ∑ s, μ t s = 1

/-- The joint state-time distribution of `μ`: `μ(s,t) = μ(s|t)/T` for `t < T`, `0` otherwise. -/
noncomputable def resetJoint {S : Type} (T : ℕ) (μ : ℕ → S → ℝ) (s : S) (t : ℕ) : ℝ :=
  if t < T then μ t s / (T : ℝ) else 0

/-- The ℓ1 distance `‖p − q‖₁ = Σ_{(s,t) ∈ S × {0,…,T-1}} |p(s,t) − q(s,t)|` of two
state-time functions (p. 75). -/
noncomputable def stateTimeL1 {S : Type} [Fintype S] (T : ℕ) (p q : S → ℕ → ℝ) : ℝ :=
  ∑ s, ∑ t ∈ Finset.range T, |p s t - q s t|

/-- `V_{π,t}(μ) = E_{s ∼ μ(·|t)}[V_{π,t}(s)]` (Definition 6.2.1, p. 74). -/
noncomputable def muValue {S A : Type} [Fintype S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (T : ℕ) (π : SampleComplexityRL.PolicyGrad.NSPolicy S A) (μ : ℕ → S → ℝ)
    (t : ℕ) : ℝ :=
  ∑ s, μ t s * SampleComplexityRL.PolicyGrad.tValue P r T π t s

/-- `Q_{π,t}(μ,h) = E_{s ∼ μ(·|t)}[Q_{π,t}(s, h(s))]` for a deterministic decision rule
`h : S → A` (Definition 6.2.1, p. 74). -/
noncomputable def muQValue {S A : Type} [Fintype S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (T : ℕ) (π : SampleComplexityRL.PolicyGrad.NSPolicy S A) (μ : ℕ → S → ℝ)
    (t : ℕ) (h : S → A) : ℝ :=
  ∑ s, μ t s * SampleComplexityRL.PolicyGrad.tQValue P r T π t s (h s)

/-- `A_{π,t}(μ,h) = E_{s ∼ μ(·|t)}[A_{π,t}(s, h(s))]` for a deterministic decision rule
`h : S → A` (Definition 6.2.1, p. 74). -/
noncomputable def muAdvantage {S A : Type} [Fintype S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (T : ℕ) (π : SampleComplexityRL.PolicyGrad.NSPolicy S A) (μ : ℕ → S → ℝ)
    (t : ℕ) (h : S → A) : ℝ :=
  ∑ s, μ t s * SampleComplexityRL.PolicyGrad.tAdvantage P r T π t s (h s)

/-- `h ∈ Π = Π₁^T` (p. 75): the deterministic non-stationary policy `h` uses a decision rule
from the class `Π₁` at every epoch `t < T`. -/
def InPolicyClass {S A : Type} (Pi1 : Set (S → A)) (T : ℕ) (h : ℕ → S → A) : Prop :=
  ∀ t < T, h t ∈ Pi1

/-- The policy that NAPI / Exact μ-PolicySearch (Algorithms 6 and 8, pp. 62, 76) passes to the
PolicyChooser at update `t`: the updates run backward `t = T-1, …, 0`, so epochs `τ > t` already
carry the chosen decision rules `h τ` and epochs `τ ≤ t` still carry the initial policy `init`. -/
def napiInput {S A : Type} (init h : ℕ → S → A) (t : ℕ) : ℕ → S → A :=
  fun τ => if t < τ then h τ else init τ

/-- The policy returned by NAPI / Exact μ-PolicySearch: `π̃(·,t) = h t` for every `t < T`
(epochs `≥ T` are never used and keep `init`). -/
def napiOutput {S A : Type} (T : ℕ) (init h : ℕ → S → A) : ℕ → S → A :=
  fun τ => if τ < T then h τ else init τ

/-- The per-state error of the PolicyChooser at update `t` (p. 62):
`ε_t(s) = max_a Q_{π,t}(s,a) − Q_{π,t}(s, h_t(s))`, `π` the input policy, `g = h_t` the output. -/
noncomputable def perStateError {S A : Type} [Fintype S] [Fintype A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (T : ℕ) (π : SampleComplexityRL.PolicyGrad.NSPolicy S A) (t : ℕ) (g : S → A)
    (s : S) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun a => SampleComplexityRL.PolicyGrad.tQValue P r T π t s a) - SampleComplexityRL.PolicyGrad.tQValue P r T π t s (g s)

end SampleComplexityRL.MuPolicySearch


