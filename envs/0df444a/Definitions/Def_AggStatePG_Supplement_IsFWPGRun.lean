-- Prove2me | Definitions.Def_AggStatePG_Supplement_IsFWPGRun
-- name    : AggStatePG_Supplement_IsFWPGRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:23:12.264964+00:00
-- url     : https://prove2.me/theorems/f566945f-0abe-5215-b391-85bf4c96e580
-- title:
--   Algorithm 3 (Frank-Wolfe policy gradient on $\Pi_\phi$)
-- statement:
--   **Algorithm 3 (Frank-Wolfe policy gradient).** Input: a step size $\alpha$, an initial policy $\pi_1\in\Pi$ and an aggregation $\phi$. For $t=1,2,\dots$:
--
--   1. (maximize the linearization) $\tilde\pi_{t+1}=\arg\max_{\pi\in\Pi_\phi}\langle\nabla J(\pi_t),\pi-\pi_t\rangle$;
--   2. (soft policy update) $\pi_{t+1}=\alpha\tilde\pi_{t+1}+(1-\alpha)\pi_t$.
--
--   Here policies are stacked vectors in $\mathbb R^{|\mathcal S|\cdot|\mathcal A|}$ with the standard inner product, $J(\pi)=(1-\gamma)\sum_s\rho(s)V_\pi(s)$ and $\Pi_\phi$ is the state-aggregated policy class. Sequences $(\pi_t,\tilde\pi_t)$ form a **run** if $\pi_1$ is the input policy and both steps hold at every $t\ge1$.
--
--   Theorem 8 shows that this algorithm coincides with soft API with on-policy state weights (Algorithm 4).
--
--   **Formalization Note** The page writes $\tilde\pi_{t+1}=\arg\max$, presupposing a unique maximizer; the predicate only requires $\tilde\pi_{t+1}$ to be a maximizer, and Theorem 8 assumes uniqueness separately. $\nabla J$ is the gradient of the published `Jext`. Iterations are indexed from $t=1$; earlier entries are unconstrained and unused.
-- source:
--   Russo, Approximation Benefits of Policy Gradient Methods with Aggregated States, arXiv:2007.11684v3, Algorithm 3, p.17

import Mathlib
import Definitions.Def_AggStatePG_Jext
import Definitions.Def_AggStatePG_aggSet

namespace AggStatePG.Supplement

/-- **Algorithm 3** (Frank-Wolfe policy gradient; Russo, *Approximation Benefits of Policy Gradient
Methods with Aggregated States*, arXiv:2007.11684v3, Algorithm 3, p.17).
Input `α`, `π_1 ∈ Π`, `φ`. For `t = 1, 2, …`:
(2) `π̃_{t+1} = argmax_{π ∈ Π_φ} ⟨∇J(π_t), π − π_t⟩`;
(3) `π_{t+1} = α π̃_{t+1} + (1 − α) π_t`.
`IsFWPGRun P r γ ρ φ α x₁ x x̃` says that `x` (the policies `π_t`) and `x̃` (the maximizers
`π̃_t`) are a run of Algorithm 3 with these inputs: `x 1 = x₁` and, for every `t ≥ 1`, `x̃ (t+1)`
maximizes `y ↦ ⟨∇J(x t), y − x t⟩` over `Π_φ` and `x (t+1) = α x̃ (t+1) + (1 − α) x t`.

**Formalization Note.** Policies are stacked vectors in `EuclideanSpace ℝ (S × A)` with the
standard inner product (p.7); `Π_φ` is the published `aggSet φ` and `∇J` is Mathlib's `gradient` of
the published `Jext`. The page writes `π̃_{t+1} = argmax`, presupposing a unique maximizer; the
predicate only asks `x̃ (t+1)` to be a maximizer, and uniqueness is a hypothesis of Theorem 8.
Iterations are indexed from `t = 1`; `x 0`, `x̃ 0`, `x̃ 1` are unconstrained and never used. -/
def IsFWPGRun {S A ι : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (ρ : S → ℝ) (φ : S → ι) (α : ℝ)
    (x₁ : EuclideanSpace ℝ (S × A)) (x xt : ℕ → EuclideanSpace ℝ (S × A)) : Prop :=
  x 1 = x₁ ∧
    ∀ t : ℕ, 1 ≤ t →
      (xt (t + 1) ∈ (AggStatePG.aggSet φ : Set (EuclideanSpace ℝ (S × A))) ∧
        ∀ y ∈ (AggStatePG.aggSet φ : Set (EuclideanSpace ℝ (S × A))),
          inner ℝ (gradient (AggStatePG.Jext P r γ ρ) (x t)) (y - x t) ≤
            inner ℝ (gradient (AggStatePG.Jext P r γ ρ) (x t)) (xt (t + 1) - x t)) ∧
      x (t + 1) = α • xt (t + 1) + (1 - α) • x t

end AggStatePG.Supplement


