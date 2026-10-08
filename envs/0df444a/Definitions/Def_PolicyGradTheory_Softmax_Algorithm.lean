-- Prove2me | Definitions.Def_PolicyGradTheory_Softmax_Algorithm
-- name    : PolicyGradTheory_Softmax_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T03:10:00.949977+00:00
-- url     : https://prove2.me/theorems/d0d04892-e6ef-4440-ba74-8fb453529928
-- title:
--   (3), p. 10 and (11), p. 18 — softmax policy π_θ, the objective θ ↦ V^{π_θ}(µ), and the softmax policy gradient ascent run
-- statement:
--   This module defines the softmax policy class and the policy gradient ascent iteration studied in §5.1 of Agarwal, Kakade, Lee and Mahajan.
--
--   Let $\mathcal S$ and $\mathcal A$ be finite state and action sets and let $\theta\in\mathbb R^{|\mathcal S||\mathcal A|}$ be an unconstrained parameter vector with entries $\theta_{s,a}$. The module defines:
--
--   1. **Softmax policy** (3). For every state $s$ and action $a$,
--   $$
--   \pi_\theta(a\mid s)=\frac{\exp(\theta_{s,a})}{\sum_{a'\in\mathcal A}\exp(\theta_{s,a'})}.
--   $$
--   2. **Objective.** For a transition kernel $P$, rewards $r$, discount $\gamma$ and a start distribution $\mu$, the map $\theta\mapsto V^{\pi_\theta}(\mu)=\sum_s\mu(s)V^{\pi_\theta}(s)$.
--   3. **Gradient ascent run** (11). A sequence $(\theta^{(t)})_{t\ge 0}$ is a run of softmax policy gradient ascent with step size $\eta$ if
--   $$
--   \theta^{(t+1)}=\theta^{(t)}+\eta\,\nabla_\theta V^{(t)}(\mu)\qquad\text{for every } t\ge 0,
--   $$
--   where $V^{(t)}=V^{\pi_{\theta^{(t)}}}$; the initial parameter $\theta^{(0)}$ is arbitrary.
--   4. **The single-state function $F$** of (38) and Lemma D.1. For a fixed vector $c\in\mathbb R^{|\mathcal A|}$ and a parameter vector $x\in\mathbb R^{|\mathcal A|}$ of one state, $F(x)=\sum_a \mathrm{softmax}(x)_a\,c_a$ with $\mathrm{softmax}(x)_a=\exp(x_a)/\sum_{a'}\exp(x_{a'})$.
--
--   These objects are the subject of Theorem 5.1 and of every lemma of Appendix C.1.
--
--   **Formalization Note** Parameters live in the Euclidean space $\mathbb R^{\mathcal S\times\mathcal A}$ (`EuclideanSpace ℝ (S × A)`), so that the norm is the $\ell_2$ norm of the paper and Mathlib's `gradient` is $\nabla_\theta$. The policy is a probability vector at every state whenever $\mathcal A$ is nonempty.
-- source:
--   arXiv:1908.00261v5, (3), p. 10; (11), p. 18; (36) and (38), p. 60; Lemma D.1, p. 70

import Mathlib
import Definitions.Def_PolicyGradTheory_ProjGA_MDP

namespace PolicyGradTheory.Softmax

open FoundationsML.ReinforcementLearning

/-- The softmax policy parameterization (3) (arXiv:1908.00261v5, p. 10): for an unconstrained
parameter vector `θ ∈ ℝ^{|S||A|}`,
`π_θ(a|s) = exp(θ_{s,a}) / ∑_{a' ∈ A} exp(θ_{s,a'})`. -/
noncomputable def softmaxPolicy {S A : Type*} [Fintype A]
    (θ : EuclideanSpace ℝ (S × A)) : S → A → ℝ :=
  fun s a => Real.exp (θ (s, a)) / ∑ a', Real.exp (θ (s, a'))

/-- The objective of softmax policy gradient: `θ ↦ V^{π_θ}(µ)` (p. 10 and (11), p. 18). Its
Euclidean gradient on `ℝ^{|S||A|}` is the paper's `∇_θ V^{π_θ}(µ)`. -/
noncomputable def softmaxValue {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (μ : S → ℝ)
    (θ : EuclideanSpace ℝ (S × A)) : ℝ :=
  PolicyGradTheory.ProjGA.valueAt (softmaxPolicy θ) P r γ μ

/-- A run of softmax policy gradient ascent (11) (p. 18), restated as (36) (p. 60), with step
size `η` on `V^{π_θ}(µ)`: `θ^{(t+1)} = θ^{(t)} + η ∇_θ V^{(t)}(µ)` for every `t`; the initial
parameter `θ^{(0)}` is free. -/
def IsSoftmaxPGRun {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (μ : S → ℝ) (η : ℝ)
    (θ : ℕ → EuclideanSpace ℝ (S × A)) : Prop :=
  ∀ t : ℕ, θ (t + 1) = θ t + η • gradient (softmaxValue P r γ μ) (θ t)

/-- The single-state function `F` of (38) (p. 60) and Lemma D.1 (p. 70): for a parameter
vector `x = θ_s ∈ ℝ^{|A|}` of one state and a fixed vector `c ∈ ℝ^{|A|}`,
`F(x) = π_x(·|s) · c = ∑_a softmax(x)_a c_a`, where `softmax(x)_a = exp(x_a) / ∑_{a'} exp(x_{a'})`. -/
noncomputable def softmaxDot {A : Type*} [Fintype A] (c : A → ℝ)
    (x : EuclideanSpace ℝ A) : ℝ :=
  ∑ a, Real.exp (x a) / (∑ a', Real.exp (x a')) * c a

end PolicyGradTheory.Softmax


