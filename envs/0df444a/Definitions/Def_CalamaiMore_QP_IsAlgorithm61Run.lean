-- Prove2me | Definitions.Def_CalamaiMore_QP_IsAlgorithm61Run
-- name    : CalamaiMore_QP_IsAlgorithm61Run
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T20:58:53.841613+00:00
-- url     : https://prove2.me/theorems/8ad01ae4-14fb-4d86-962e-3a8cbb993b0d
-- title:
--   Algorithm 6.1 — gradient projection active-set algorithm for quadratic programming
-- statement:
--   Fix a polyhedral set $\Omega = \{x : \langle c_j, x\rangle \ge \delta_j,\ j = 1,\dots,m\}$ with active sets $A(x)$, a function $f$, and constants $\gamma_1, \gamma_2, \gamma_3$, $\mu_1, \mu_2$.
--
--   **Gradient projection step.** From $x_k$ with step $\alpha_k$, the point $x_{k+1}$ is obtained by a gradient projection step if $\alpha_k > 0$, $x_{k+1} = P(x_k - \alpha_k \nabla f(x_k))$, and
--
--   $$
--   f(x_{k+1}) \le f(x_k) + \mu_1 \langle \nabla f(x_k), x_{k+1} - x_k \rangle, \tag{2.1}
--   $$
--
--   $$
--   \alpha_k \ge \gamma_1 \quad\text{or}\quad \alpha_k \ge \gamma_2 \bar\alpha_k > 0, \tag{2.2}
--   $$
--
--   where $\bar\alpha_k$ satisfies
--
--   $$
--   f(x_k(\bar\alpha_k)) > f(x_k) + \mu_2 \langle \nabla f(x_k), x_k(\bar\alpha_k) - x_k \rangle, \tag{2.3}
--   $$
--
--   with $x_k(\alpha) = P(x_k - \alpha\nabla f(x_k))$, and $\alpha_k \le \gamma_3$ (3.2).
--
--   **Algorithm 6.1.** A run consists of iterates $x_k$, working sets $W_k$ and steps $\alpha_k$ ($k \ge 0$) with $x_0 \in \Omega$ such that, for every $k$, $x_k \in \Omega$, $W_k \subseteq A(x_k)$, and
--
--   1. if $x_k$ is a global minimizer of problem (6.2) $\min\{f(y) : \langle c_j, y\rangle = \delta_j,\ j \in W_k\}$, then $x_{k+1}$ is obtained from $x_k$ by a gradient projection step with step $\alpha_k$ satisfying (2.1), (2.2) and (3.2);
--   2. otherwise $x_{k+1} \in \Omega$, $f(x_{k+1}) \le f(x_k)$ and $W_k \subseteq W_{k+1}$; and if $W_{k+1} = W_k$, then $x_{k+1}$ is a global minimizer of (6.2).
--
--   The algorithm uses the gradient projection method to choose a new working set whenever the current one has been exhausted, in place of the Lagrange-multiplier test of standard active-set methods.
--
--   **Formalization Note** The run is a predicate on three sequences $x : \mathbb{N} \to E$, $W : \mathbb{N} \to$ `Finset (Fin m)`, $\alpha : \mathbb{N} \to \mathbb{R}$, indexed from $k = 0$; it does not stop by itself (the algorithm is halted when a stationary iterate is reached). $W_0$ is any subset of $A(x_0)$. The paper's "$\subset$" is inclusion $\subseteq$. The constants are parameters of the predicate; their ranges ($\gamma_1, \gamma_2 > 0$, $\mu_1, \mu_2 \in (0,1)$) are hypotheses of the theorems that use it. In step (b), $\alpha_k$ is unconstrained.
-- source:
--   Calamai & Moré, Projected gradient methods for linearly constrained problems, Math. Programming 39 (1987), p. 97, Eqs. (2.1)–(2.3); p. 103, Eq. (3.2); pp. 110–111, Eq. (6.2) and Algorithm 6.1

import Mathlib
import Definitions.Def_CalamaiMore_QP_proj
import Definitions.Def_CalamaiMore_QP_polyhedron

namespace CalamaiMore.QP

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- One gradient projection step of Calamai–Moré, (2.1), (2.2), (2.3) (p. 97) and (3.2)
(p. 103), from `xk` with step `αk` to `xnext`:
* `αk > 0` and `xnext = P(xk - αk ∇f(xk))`;
* (2.1) `f(xnext) ≤ f(xk) + μ₁ ⟨∇f(xk), xnext - xk⟩`;
* (2.2) `αk ≥ γ₁`, or `αk ≥ γ₂ ᾱ > 0` for some `ᾱ` satisfying (2.3)
  `f(xk(ᾱ)) > f(xk) + μ₂ ⟨∇f(xk), xk(ᾱ) - xk⟩`, where `xk(ᾱ) = P(xk - ᾱ ∇f(xk))`;
* (3.2) `αk ≤ γ₃`. -/
def IsProjectionStep (f : E → ℝ) (Ω : Set E) (γ₁ γ₂ γ₃ μ₁ μ₂ : ℝ)
    (xk : E) (αk : ℝ) (xnext : E) : Prop :=
  0 < αk ∧
  xnext = projPath f Ω xk αk ∧
  f xnext ≤ f xk + μ₁ * inner ℝ (gradient f xk) (xnext - xk) ∧
  (γ₁ ≤ αk ∨
    ∃ αbar : ℝ, 0 < γ₂ * αbar ∧ γ₂ * αbar ≤ αk ∧
      f xk + μ₂ * inner ℝ (gradient f xk) (projPath f Ω xk αbar - xk)
        < f (projPath f Ω xk αbar)) ∧
  αk ≤ γ₃

/-- A run of Algorithm 6.1 of Calamai–Moré (p. 111) on the polyhedron
`Ω = {x : ⟨c_j, x⟩ ≥ δ_j}` with constants `γ₁ γ₂ γ₃ μ₁ μ₂`: iterates `x : ℕ → E`, working sets
`W : ℕ → Finset (Fin m)` and steps `α : ℕ → ℝ` such that `x 0 ∈ Ω` and, for every `k`,
* `x k ∈ Ω` and `W k ⊆ A(x k)`;
* (a) if `x k` is a global minimizer of (6.2) for `W k`, then `x (k+1)` is obtained from `x k`
  by a gradient projection step with step `α k` satisfying (2.1), (2.2) and (3.2);
* (b) otherwise `x (k+1) ∈ Ω`, `f (x (k+1)) ≤ f (x k)`, `W k ⊆ W (k+1)`, and if
  `W (k+1) = W k` then `x (k+1)` is a global minimizer of (6.2) for `W k`. -/
def IsAlgorithm61Run {m : ℕ} (f : E → ℝ) (c : Fin m → E) (δ : Fin m → ℝ)
    (γ₁ γ₂ γ₃ μ₁ μ₂ : ℝ) (x : ℕ → E) (W : ℕ → Finset (Fin m)) (α : ℕ → ℝ) : Prop :=
  x 0 ∈ polyhedron c δ ∧
  ∀ k : ℕ,
    x k ∈ polyhedron c δ ∧
    W k ⊆ activeSet c δ (x k) ∧
    (IsWorkingSetMinimizer f c δ (W k) (x k) →
      IsProjectionStep f (polyhedron c δ) γ₁ γ₂ γ₃ μ₁ μ₂ (x k) (α k) (x (k + 1))) ∧
    (¬ IsWorkingSetMinimizer f c δ (W k) (x k) →
      x (k + 1) ∈ polyhedron c δ ∧
      f (x (k + 1)) ≤ f (x k) ∧
      W k ⊆ W (k + 1) ∧
      (W (k + 1) = W k → IsWorkingSetMinimizer f c δ (W k) (x (k + 1))))

end CalamaiMore.QP


