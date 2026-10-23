-- Prove2me | Definitions.Def_VLearning_CCE_WeightedBandit
-- name    : VLearning_CCE_WeightedBandit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:28:13.934987+00:00
-- url     : https://prove2.me/theorems/f622638d-c6aa-4479-96ba-5f1fb79d3c09
-- title:
--   (3), Protocol 2, Assumption 1, pp. 7–8 — learning rate α_t, weights α^i_t, adversarial bandit rules with noisy feedback, weighted regret
-- statement:
--   **Learning rate and weights (3).** For an episode length $H$ define
--   $$\alpha_t = \frac{H+1}{H+t},\qquad \alpha^0_t = \prod_{j=1}^t (1-\alpha_j),\qquad \alpha^i_t = \alpha_i\prod_{j=i+1}^t (1-\alpha_j)\quad (1\le i\le t).$$
--
--   **Adversarial bandit with noisy feedback (Protocol 2).** A bandit rule `ADV_BANDIT_UPDATE` on $B$ arms maps the feedback history $(b_1,\tilde\ell_1(b_1)),\dots,(b_t,\tilde\ell_t(b_t))$ to the next strategy $\theta_{t+1}\in\Delta_B$; a valid rule always outputs a probability vector and starts from the uniform strategy $\theta_1(b)=1/B$. In round $t$ an adversary chooses a loss vector $\ell_t\in[0,1]^B$, the learner plays $b_t\sim\theta_t$, and observes a noisy feedback $\tilde\ell_t(b_t)\in[0,1]$ with $\mathbb E[\tilde\ell_t(b_t)\mid \text{past}, b_t]=\ell_t(b_t)$.
--
--   The adversary is an **adaptive environment** with private randomness in a finite set $Z$: an initial draw $z_0$; the loss $\ell_t$ is a function of $z_0$ and of the past rounds $(b_i,z_i)_{i<t}$; given the past and $b_t$ the round's outcome $z_t$ is drawn from a kernel, and the feedback $\tilde\ell_t(b_t)$ is a function of the past, $b_t$ and $z_t$.
--
--   **Weighted regret (4).** After $t$ rounds,
--   $$\max_{\theta\in\Delta_B}\sum_{i=1}^t \alpha^i_t\big[\langle\theta_i,\ell_i\rangle-\langle\theta,\ell_i\rangle\big].$$
--
--   **Assumption 1.** A rule satisfies Assumption 1 with a function $\xi$ if for every $t\in\mathbb N$, every $\delta\in(0,1)$ and every valid adaptive environment, with probability at least $1-\delta$ the weighted regret after $t$ rounds is at most $\xi(B,t,\log(1/\delta))$.
--
--   These objects are the interface between V-learning and its bandit subroutine.
--
--   **Formalization Note** The maximum over the simplex is taken over its vertices (the objective is linear in $\theta$). The rule is a deterministic map of its feedback history (FTRL, Algorithm 5, is of this form). The probability of an event is a finite sum of history weights. The paper leaves the adversary's information unspecified; the encoding lets it depend on all past randomness but not on $b_t$ before $\ell_t$ is chosen. The second sentence of Assumption 1 (the upper bound $\Xi$ and the conditions on $\xi,\Xi$) is stated as hypotheses of the theorems that use it.
-- source:
--   Jin, Liu, Wang & Yu, V-Learning—A Simple, Efficient, Decentralized Algorithm for Multiagent RL, arXiv:2110.14555v1, p. 7, (3) and Protocol 2; p. 8, ADV_BANDIT_UPDATE paragraph, Assumption 1, (4)

import Mathlib

namespace VLearning.CCE

open Classical

/-- The learning rate `α_t = (H + 1)/(H + t)` of (3), p. 7. -/
noncomputable def lr (H t : ℕ) : ℝ := ((H : ℝ) + 1) / ((H : ℝ) + t)

/-- The weights of (3), p. 7: `α^0_t = ∏_{j=1}^t (1 - α_j)` and
`α^i_t = α_i ∏_{j=i+1}^t (1 - α_j)` for `i ≥ 1`. Only `0 ≤ i ≤ t` is ever used. -/
noncomputable def lrW (H t i : ℕ) : ℝ :=
  if i = 0 then ∏ j ∈ Finset.Icc 1 t, (1 - lr H j)
  else lr H i * ∏ j ∈ Finset.Ioc i t, (1 - lr H j)

/-- An adversarial-bandit update rule `ADV_BANDIT_UPDATE` on `B` arms (Protocol 2, p. 7):
the strategy `θ_{t+1}` played in round `t + 1` as a function of the feedback history
`[(b_1, ℓ̃_1(b_1)), …, (b_t, ℓ̃_t(b_t))]`, oldest first. -/
def BanditRule (B : ℕ) : Type := List (Fin B × ℝ) → Fin B → ℝ

/-- A valid rule outputs a probability vector on the arms after every history, and starts
from the uniform strategy `θ_1(b) = 1/B` (Protocol 2, line 1). -/
def BanditRule.Valid {B : ℕ} (alg : BanditRule B) : Prop :=
  (∀ hist b, 0 ≤ alg hist b) ∧ (∀ hist, ∑ b, alg hist b = 1) ∧ (∀ b, alg [] b = 1 / (B : ℝ))

/-- A (finitary) adaptive adversarial environment for Protocol 2, with private randomness in
the finite type `Z`:
* `init z₀` is the law of an initial private draw `z₀`;
* `loss z₀ past b` is the loss `ℓ_t(b)` chosen before round `t`, as a function of `z₀` and of the
  past rounds `past = [(b_1, z_1), …, (b_{t-1}, z_{t-1})]`;
* `kernel z₀ past b z` is the probability that the round's private outcome is `z` when the
  learner plays `b`;
* `fb z₀ past b z` is the noisy bandit feedback `ℓ̃_t(b)` observed by the learner. -/
structure AdaptiveEnv (B : ℕ) (Z : Type) where
  init : Z → ℝ
  loss : Z → List (Fin B × Z) → Fin B → ℝ
  kernel : Z → List (Fin B × Z) → Fin B → Z → ℝ
  fb : Z → List (Fin B × Z) → Fin B → Z → ℝ

namespace AdaptiveEnv

variable {B : ℕ} {Z : Type} [Fintype Z]

/-- Validity (p. 8): `init` and `kernel` are probability vectors, losses and feedbacks lie in
`[0, 1]`, and the feedback is conditionally unbiased: `𝔼[ℓ̃_t(b_t) | past, b_t] = ℓ_t(b_t)`. -/
def Valid (env : AdaptiveEnv B Z) : Prop :=
  (∀ z, 0 ≤ env.init z) ∧ (∑ z, env.init z = 1) ∧
  (∀ z₀ past b z, 0 ≤ env.kernel z₀ past b z) ∧ (∀ z₀ past b, ∑ z, env.kernel z₀ past b z = 1) ∧
  (∀ z₀ past b, env.loss z₀ past b ∈ Set.Icc (0 : ℝ) 1) ∧
  (∀ z₀ past b z, env.fb z₀ past b z ∈ Set.Icc (0 : ℝ) 1) ∧
  (∀ z₀ past b, ∑ z, env.kernel z₀ past b z * env.fb z₀ past b z = env.loss z₀ past b)

/-- The first `i` rounds `[(b_1, z_1), …, (b_i, z_i)]` of a `t`-round history `ω`. -/
def past {t : ℕ} (ω : Fin t → Fin B × Z) (i : ℕ) : List (Fin B × Z) := (List.ofFn ω).take i

/-- The feedback the learner has seen before round `i + 1` (0-based round `i`). -/
def fbList (env : AdaptiveEnv B Z) (z₀ : Z) {t : ℕ} (ω : Fin t → Fin B × Z) (i : ℕ) :
    List (Fin B × ℝ) :=
  (List.ofFn fun i' : Fin t =>
    ((ω i').1, env.fb z₀ (past ω i'.val) (ω i').1 (ω i').2)).take i

/-- The learner's strategy `θ` in (0-based) round `i`. -/
def theta (env : AdaptiveEnv B Z) (alg : BanditRule B) (z₀ : Z) {t : ℕ}
    (ω : Fin t → Fin B × Z) (i : ℕ) : Fin B → ℝ :=
  alg (env.fbList z₀ ω i)

/-- Probability of the `t`-round history `(z₀, ω)` when `alg` plays against `env`. -/
noncomputable def weight (env : AdaptiveEnv B Z) (alg : BanditRule B) (z₀ : Z) {t : ℕ}
    (ω : Fin t → Fin B × Z) : ℝ :=
  env.init z₀ * ∏ i : Fin t,
    env.theta alg z₀ ω i.val (ω i).1 * env.kernel z₀ (past ω i.val) (ω i).1 (ω i).2

/-- The weighted regret of (4), p. 8, after `t` rounds:
`max_{θ ∈ Δ_B} ∑_{i=1}^t α^i_t [⟨θ_i, ℓ_i⟩ − ⟨θ, ℓ_i⟩]`. The objective is linear in `θ`, so the
maximum over the simplex is the maximum over its vertices `b`. -/
noncomputable def weightedRegret (env : AdaptiveEnv B Z) (alg : BanditRule B) (H : ℕ) (z₀ : Z)
    {t : ℕ} (ω : Fin t → Fin B × Z) : ℝ :=
  ⨆ b : Fin B, ∑ i : Fin t, lrW H t (i.val + 1) *
    ((∑ b', env.theta alg z₀ ω i.val b' * env.loss z₀ (past ω i.val) b') -
      env.loss z₀ (past ω i.val) b)

/-- `ℙ(weighted regret after t rounds > x)`: a finite sum of history weights. -/
noncomputable def regretExceedProb (env : AdaptiveEnv B Z) (alg : BanditRule B) (H t : ℕ)
    (x : ℝ) : ℝ :=
  ∑ z₀ : Z, ∑ ω : Fin t → Fin B × Z,
    env.weight alg z₀ ω * (if x < env.weightedRegret alg H z₀ ω then 1 else 0)

end AdaptiveEnv

/-- **Assumption 1** (p. 8), first sentence: for every `t ∈ ℕ` and every `δ ∈ (0, 1)`, with
probability at least `1 − δ` the weighted regret (4) is at most `ξ(B, t, log(1/δ))` — against
every valid finitary adaptive environment. -/
def Assumption1 {B : ℕ} (H : ℕ) (alg : BanditRule B) (ξ : ℕ → ℕ → ℝ → ℝ) : Prop :=
  ∀ (Z : Type) [Fintype Z] (env : AdaptiveEnv B Z), env.Valid →
    ∀ (t : ℕ) (δ : ℝ), 0 < δ → δ < 1 →
      env.regretExceedProb alg H t (ξ B t (Real.log (1 / δ))) ≤ δ

end VLearning.CCE


