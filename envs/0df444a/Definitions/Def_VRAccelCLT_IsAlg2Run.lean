-- Prove2me | Definitions.Def_VRAccelCLT_IsAlg2Run
-- name    : VRAccelCLT_IsAlg2Run
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:20:12.31359+00:00
-- url     : https://prove2.me/theorems/728a055e-c4c5-4c3f-a8b0-c80bad93e10c
-- title:
--   A run of Algorithm 2 (variance-reduced accelerated SGD)
-- statement:
--   Given a step length $\alpha$, a momentum parameter $\beta$, an initial point $x_0\in\mathbb R^m$ and gradient noise $(w_k)_{k\ge0}$, a **run of Algorithm 2** is a pair of random sequences $(x_k)_{k\ge0},(y_k)_{k\ge0}$ in $\mathbb R^m$ with $x_0=y_0$ and, for every $k\ge0$,
--
--   $$
--   \begin{aligned}
--   y_{k+1}&=x_k-\alpha\big(\nabla f(x_k)+w_{k,N_k}\big),&&(10a)\\
--   x_{k+1}&=y_{k+1}+\beta\,(y_{k+1}-y_k).&&(10b)
--   \end{aligned}
--   $$
--
--   This is Nesterov's accelerated gradient method in which the exact gradient is replaced by an average of $N_k$ sampled gradients; the batch sizes enter through the noise.
--
--   **Formalization Note** The recursion holds pathwise for every outcome; $x_0$ is a deterministic vector. The definition fixes no sign of $\alpha,\beta$; the theorems state the paper's parameter values.
-- source:
--   Lei, Shanbhag, Variance-Reduced Accelerated First-order Methods: Central Limit Theorems and Confidence Statements, arXiv:2006.07769v3, Algorithm 2, eqs. (10a)–(10b), p.7

import Mathlib

namespace VRAccelCLT

/-- **A run of Algorithm 2 (variance-reduced accelerated SGD).** Lei, Shanbhag,
arXiv:2006.07769v3, Algorithm 2, p.7: "Given arbitrary initial values x0 = y0 ∈ Rm, positive
constants α, β, and a positive integer sequence {Nk}k≥0. Then iterate the following equations for
k ≥ 0. yk+1 = xk − α(∇f(xk) + wk,Nk), (10a) xk+1 = yk+1 + β(yk+1 − yk), (10b)".

`IsAlg2Run f α β x0 w x y` says that the random sequences `x, y : ℕ → Ω → ℝᵐ` start at the
deterministic point `x₀ = y₀` and satisfy (10a)–(10b) pathwise with the gradient noise `w`.

**Formalization Note.** The batch sizes `N_k` enter only through the noise `w` (see `IsVRNoise`).
No sign condition on `α, β` is built in; the theorems state the paper's values of `α` and
`β = (1−γ)/(1+γ)` (which is `0` when `αη = 1`, i.e. `η = L` and `α = 1/L`). -/
def IsAlg2Run {m : ℕ} {Ω : Type*} (f : EuclideanSpace ℝ (Fin m) → ℝ) (α β : ℝ)
    (x0 : EuclideanSpace ℝ (Fin m)) (w x y : ℕ → Ω → EuclideanSpace ℝ (Fin m)) : Prop :=
  (∀ ω, x 0 ω = x0) ∧ (∀ ω, y 0 ω = x0) ∧
    ∀ (k : ℕ) (ω : Ω),
      y (k + 1) ω = x k ω - α • (gradient f (x k ω) + w k ω) ∧
      x (k + 1) ω = y (k + 1) ω + β • (y (k + 1) ω - y k ω)

end VRAccelCLT


