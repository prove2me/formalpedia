-- Prove2me | Definitions.Def_LogRegretOCO_ONS_Run
-- name    : LogRegretOCO_ONS_Run
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T21:34:43.63982+00:00
-- url     : https://prove2.me/theorems/316657d0-bfc7-47f5-b963-306095205336
-- title:
--   The Online Newton Step algorithm (Fig. 2)
-- statement:
--   Let $\mathcal P\subseteq\mathbb R^n$, let $G,D,\alpha$ be real parameters, and let $f_1,f_2,\dots:\mathbb R^n\to\mathbb R$ be the cost functions. The **Online Newton Step** (ONS) uses
--   $$
--   \beta=\tfrac12\min\Big\{\frac{1}{4GD},\,\alpha\Big\},\qquad \varepsilon=\frac{1}{\beta^2D^2},
--   $$
--   writes $\nabla_\tau=\nabla f_\tau(x_\tau)$ for the gradient at the point played in round $\tau$, and maintains
--   $$
--   A_t=\sum_{i=1}^{t}\nabla_i\nabla_i^\top+\varepsilon I_n .
--   $$
--   A sequence $x_1,x_2,\dots$ is a *run* of ONS if $x_1\in\mathcal P$ is arbitrary and, for every round $t\ge1$,
--   $$
--   x_{t+1}=\Pi^{A_t}_{\mathcal P}\Big(x_t-\frac1\beta A_t^{-1}\nabla_t\Big),
--   $$
--   where $\Pi^{A_t}_{\mathcal P}$ is the generalized projection in the norm induced by $A_t$ (any minimiser is allowed). This is Fig. 2's rule "in iteration $t>1$, use $x_t=\Pi^{A_{t-1}}_{\mathcal P}(x_{t-1}-\frac1\beta A_{t-1}^{-1}\nabla_{t-1})$", written with the index shift of the proof on p. 177. Note that $A_t$ already contains the current gradient $\nabla_t$.
--
--   **Formalization Note** $\beta$, $\varepsilon$ and $A_t$ are `def`s (`onsBeta`, `onsEps`, `onsMatrix`) so every statement shows the paper's formulas. The cost functions are ambient functions on $\mathbb R^n$ so that gradients at boundary points of $\mathcal P$ make sense; $\nabla f_t(x)$ is Mathlib's `gradient`. The inverse is Mathlib's `Matrix.inv`; under the theorems' hypotheses $G,D,\alpha>0$ one has $\varepsilon>0$, so $A_t$ is positive definite and `Matrix.inv` is the true inverse. The run is a predicate on the whole trajectory, required at every round, so any adversary (including an adaptive one) is covered by quantifying over all cost sequences.
-- source:
--   Hazan, Agarwal, Kale, Logarithmic regret algorithms for online convex optimization, Mach Learn 69 (2007), p. 176, Fig. 2; p. 177, proof of Theorem 2 (y_{t+1}, x_{t+1})

import Mathlib
import Definitions.Def_LogRegretOCO_ONS_Basic
open Matrix

namespace LogRegretOCO.ONS

/-- The ONS step-size parameter `β = ½ min{1/(4GD), α}` (Fig. 2, p. 176). -/
noncomputable def onsBeta (G D α : ℝ) : ℝ := (1 / 2) * min (1 / (4 * G * D)) α

/-- The ONS regularisation parameter `ε = 1/(β²D²)` (Fig. 2, p. 176). -/
noncomputable def onsEps (G D α : ℝ) : ℝ := 1 / (onsBeta G D α ^ 2 * D ^ 2)

/-- The ONS matrix `A_t = Σ_{i=1}^t ∇_i ∇_iᵀ + ε Iₙ` with `∇_i = ∇f_i(x_i)` (Fig. 2, p. 176). -/
noncomputable def onsMatrix {n : ℕ} (G D α : ℝ) (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (t : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  regGram (onsEps G D α) (fun i => gradient (f i) (x i)) t

/-- `x` is a run of the Online Newton Step (Fig. 2, p. 176) on the cost functions `f` over `P`
with parameters `G, D, α`: `x₁ ∈ P` is arbitrary, and for every round `t ≥ 1`
`x_{t+1}` is a generalized projection, in the norm induced by `A_t`, of
`y_{t+1} = x_t − (1/β) A_t⁻¹ ∇_t` onto `P` (the indexing of the proof on p. 177). -/
def IsONSRun {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n))) (G D α : ℝ)
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n)) : Prop :=
  x 1 ∈ P ∧
    ∀ t : ℕ, 1 ≤ t →
      IsGenProj P (onsMatrix G D α f x t)
        (x t - (1 / onsBeta G D α) •
          WithLp.toLp 2 ((onsMatrix G D α f x t)⁻¹ *ᵥ WithLp.ofLp (gradient (f t) (x t))))
        (x (t + 1))

end LogRegretOCO.ONS


