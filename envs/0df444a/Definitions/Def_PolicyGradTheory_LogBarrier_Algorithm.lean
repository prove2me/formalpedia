-- Prove2me | Definitions.Def_PolicyGradTheory_LogBarrier_Algorithm
-- name    : PolicyGradTheory_LogBarrier_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T16:56:45.329582+00:00
-- url     : https://prove2.me/theorems/d0113d35-4ee0-4c3a-89f1-3e77b34126a3
-- title:
--   (3), (12), (13), Lemma D.4 — softmax policy, log barrier objective L_λ, β_λ and the gradient ascent run
-- statement:
--   This module defines the softmax policy class, the log barrier regularized objective and the gradient ascent iteration on it.
--
--   Parameters are vectors $\theta\in\mathbb R^{|\mathcal S||\mathcal A|}$ with Euclidean norm $\|\theta\|_2$. Fix a finite MDP $(P,r,\gamma)$, a start distribution $\mu$ over states and a regularization parameter $\lambda$.
--
--   1. **Softmax policy** (3): $\displaystyle \pi_\theta(a\mid s)=\frac{\exp(\theta_{s,a})}{\sum_{a'\in\mathcal A}\exp(\theta_{s,a'})}$.
--   2. **Softmax objective:** $\theta\mapsto V^{\pi_\theta}(\mu)$.
--   3. **Log barrier regularized objective** (12), second line:
--   $$
--   L_\lambda(\theta)=V^{\pi_\theta}(\mu)+\frac{\lambda}{|\mathcal S|\,|\mathcal A|}\sum_{s,a}\log\pi_\theta(a\mid s)+\lambda\log|\mathcal A| .
--   $$
--   It equals $V^{\pi_\theta}(\mu)-\lambda\,\mathbb E_{s\sim\mathrm{Unif}_{\mathcal S}}[\mathrm{KL}(\mathrm{Unif}_{\mathcal A},\pi_\theta(\cdot\mid s))]$.
--   4. **Smoothness constant** of Lemma D.4: $\beta_\lambda=\dfrac{8}{(1-\gamma)^3}+\dfrac{2\lambda}{|\mathcal S|}$.
--   5. **Gradient ascent run** (13) with step size $\eta$: a sequence $(\theta^{(t)})_{t\ge0}$ with $\theta^{(t+1)}=\theta^{(t)}+\eta\nabla_\theta L_\lambda(\theta^{(t)})$ for all $t$.
--
--   These objects carry the polynomial convergence result of §5.2: approximately stationary points of $L_\lambda$ are approximately optimal, and gradient ascent with step $1/\beta_\lambda$ reaches one quickly.
--
--   **Formalization Note.** $\nabla_\theta$ is Mathlib's `gradient` on `EuclideanSpace ℝ (S × A)`. Since $\pi_\theta(a\mid s)>0$ for every $\theta$ (with $\mathcal A$ nonempty), $\log\pi_\theta(a\mid s)$ is the genuine logarithm. The constant $\beta_\lambda$ is the one Lemma D.4 proves, $8/(1-\gamma)^3$; Corollary 5.1 as printed writes $8\gamma/(1-\gamma)^3$ (see the goal theorem).
-- source:
--   arXiv:1908.00261v5, (3) p. 10, (12)–(13) p. 19, Lemma D.4 p. 75

import Mathlib
import Definitions.Def_PolicyGradTheory_ProjGA_MDP
import Definitions.Def_PolicyGradTheory_Softmax_Algorithm

namespace PolicyGradTheory.LogBarrier

open FoundationsML.ReinforcementLearning

/-- The log barrier regularized objective (12) (p. 19), in its second form:
`L_λ(θ) = V^{π_θ}(µ) + λ/(|S||A|) ∑_{s,a} log π_θ(a|s) + λ log |A|`. -/
noncomputable def logBarrierObj {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (μ : S → ℝ) (lam : ℝ)
    (θ : EuclideanSpace ℝ (S × A)) : ℝ :=
  PolicyGradTheory.Softmax.softmaxValue P r γ μ θ
    + lam / ((Fintype.card S : ℝ) * (Fintype.card A : ℝ))
      * ∑ s, ∑ a, Real.log (PolicyGradTheory.Softmax.softmaxPolicy θ s a)
    + lam * Real.log (Fintype.card A : ℝ)

/-- The smoothness constant of Lemma D.4 (p. 75): `β_λ = 8/(1−γ)³ + 2λ/|S|`. -/
noncomputable def betaLam (S : Type*) [Fintype S] (γ lam : ℝ) : ℝ :=
  8 / (1 - γ) ^ 3 + 2 * lam / (Fintype.card S : ℝ)

/-- A run of the policy gradient ascent updates (13) (p. 19) on `L_λ` with step size `η`:
`θ^{(t+1)} = θ^{(t)} + η ∇_θ L_λ(θ^{(t)})` for every `t`. -/
def IsLogBarrierRun {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (μ : S → ℝ) (lam η : ℝ)
    (θ : ℕ → EuclideanSpace ℝ (S × A)) : Prop :=
  ∀ t : ℕ, θ (t + 1) = θ t + η • gradient (logBarrierObj P r γ μ lam) (θ t)

end PolicyGradTheory.LogBarrier


