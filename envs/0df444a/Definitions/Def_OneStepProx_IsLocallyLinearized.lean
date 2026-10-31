-- Prove2me | Definitions.Def_OneStepProx_IsLocallyLinearized
-- name    : OneStepProx_IsLocallyLinearized
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:08:52.921483+00:00
-- url     : https://prove2.me/theorems/a648e98e-fa06-4894-b2a7-808186de22b4
-- title:
--   Assumption (i): $\nabla g_n$ is locally linearized at $\hat\theta$ by $H$ at rate $\sqrt n$, uniformly in probability
-- statement:
--   Let $(\Omega,\mathcal A,P)$ be a probability space, $\Theta\subseteq\mathbb R^d$, $g_n$ random functions, $\hat\theta=\hat\theta_n$ random points and $H$ a $d\times d$ matrix. This is assumption (i) of Theorem 2.1 for the matrix $H$: for each $M>0$,
--
--   $$
--   \sup_{\theta\in\Theta,\ \sqrt n\|\theta-\hat\theta\|<M}\Bigl\|\sqrt n\bigl(\nabla g_n(\theta)-\nabla g_n(\hat\theta)\bigr)-\sqrt n\,H(\theta-\hat\theta)\Bigr\|\xrightarrow{P}0 .
--   $$
--
--   Written out: for all $M>0$ and $\varepsilon>0$, the probability of the event that some $\theta\in\Theta$ with $\sqrt n\|\theta-\hat\theta\|<M$ has $\|\sqrt n(\nabla g_n(\theta)-\nabla g_n(\hat\theta))-\sqrt nH(\theta-\hat\theta)\|>\varepsilon$ tends to $0$.
--
--   The condition resembles differentiability of $\nabla g_n$ with Jacobian $H$, but because the limit is in probability it can hold when $\nabla g_n$ is not differentiable.
--
--   **Formalization Note** That event is exactly $\{\sup>\varepsilon\}$, so the real supremum, which is $0$ on an unbounded family in Lean, never appears. The paper's display carries no norm. No measurability is assumed: the probability of an event is its outer measure.
-- source:
--   Bassett & Deride, One-Step Estimation with Scaled Proximal Methods, arXiv:2004.14521v3, Theorem 2.1 (i), p.6

import Mathlib

open MeasureTheory Filter Topology

namespace OneStepProx

/-- Assumption (i) of Theorem 2.1 (Bassett & Deride, arXiv:2004.14521v3, p.6): for each `M > 0`,
`sup_{√n‖θ − θ̂‖ < M} ‖√n(∇gₙ(θ) − ∇gₙ(θ̂)) − √n H(θ − θ̂)‖ →ᴾ 0`.

**Formalization Note.** The convergence is written out: for every `ε > 0`, the probability that
some `θ ∈ Θ` in the ball of radius `M/√n` around `θ̂ₙ` has `‖…‖ > ε` tends to `0`. That event is
exactly `{sup > ε}`; writing it this way avoids the real `⨆`, which is `0` on an unbounded family.
The paper's display carries no norm; the sup is of the Euclidean norm of the vector. The
probability of an event that need not be measurable is its outer measure. `H` acts through
`Matrix.toEuclideanLin`. -/
def IsLocallyLinearized {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Θ : Set (EuclideanSpace ℝ (Fin d))) (g : ℕ → Ω → EuclideanSpace ℝ (Fin d) → ℝ)
    (θhat : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (H : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ∀ M : ℝ, 0 < M → ∀ ε : ℝ, 0 < ε →
    Tendsto
      (fun n : ℕ => P {ω | ∃ θ ∈ Θ, Real.sqrt n * ‖θ - θhat n ω‖ < M ∧
        ε < ‖Real.sqrt n • (gradient (g n ω) θ - gradient (g n ω) (θhat n ω))
            - Real.sqrt n • Matrix.toEuclideanLin H (θ - θhat n ω)‖})
      atTop (𝓝 0)

end OneStepProx


