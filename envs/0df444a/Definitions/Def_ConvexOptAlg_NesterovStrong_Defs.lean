-- Prove2me | Definitions.Def_ConvexOptAlg_NesterovStrong_Defs
-- name    : ConvexOptAlg_NesterovStrong_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T17:40:26.057798+00:00
-- url     : https://prove2.me/theorems/6cc9c8ef-42a6-481f-b3ed-2e528efa0d25
-- title:
--   §3.7.1, pp. 290–292 — β-smoothness, Nesterov's accelerated gradient descent for κ = β/α, the functions Φ_s (3.17), the centres v_s (3.21)
-- statement:
--   Throughout, $\mathbb R^n$ carries the Euclidean inner product $x^\top y$ and norm $\|\cdot\|$, $f:\mathbb R^n\to\mathbb R$ is a function and $g:\mathbb R^n\to\mathbb R^n$ is a map standing for its gradient $\nabla f$. For $\alpha,\beta\in\mathbb R$ put $\kappa=\beta/\alpha$ (the condition number).
--
--   1. **β-smoothness.** $f$ is $\beta$-smooth if $g(x)=\nabla f(x)$ is the gradient of $f$ at every $x$ and the gradient is $\beta$-Lipschitz:
--   $$\|\nabla f(x)-\nabla f(y)\|\le\beta\|x-y\|\qquad\text{for all }x,y\in\mathbb R^n .$$
--   2. **Nesterov's accelerated gradient descent (strongly convex case).** A pair of sequences $(x_t)_{t\ge1}$, $(y_t)_{t\ge1}$ is a run of the method if $x_1=y_1$ (an arbitrary starting point) and, for every $t\ge1$,
--   $$y_{t+1}=x_t-\frac1\beta\nabla f(x_t),\qquad x_{t+1}=\Big(1+\frac{\sqrt\kappa-1}{\sqrt\kappa+1}\Big)y_{t+1}-\frac{\sqrt\kappa-1}{\sqrt\kappa+1}\,y_t .$$
--   3. **The functions $\Phi_s$.** Given points $(x_s)_{s\ge1}$, define by induction
--   $$\Phi_1(z)=f(x_1)+\frac\alpha2\|z-x_1\|^2,\qquad \Phi_{s+1}(z)=\Big(1-\frac1{\sqrt\kappa}\Big)\Phi_s(z)+\frac1{\sqrt\kappa}\Big(f(x_s)+\nabla f(x_s)^\top(z-x_s)+\frac\alpha2\|z-x_s\|^2\Big).$$
--   4. **The centres $v_s$.** $v_1=x_1$ and
--   $$v_{s+1}=\Big(1-\frac1{\sqrt\kappa}\Big)v_s+\frac1{\sqrt\kappa}x_s-\frac1{\alpha\sqrt\kappa}\nabla f(x_s).$$
--   5. **The values $\Phi^*_s$.** $\Phi^*_s=\Phi_s(v_s)$, the value of $\Phi_s$ at its centre.
--
--   These are the objects of the estimate-sequence proof of Theorem 3.18; the run is the algorithm, and $\Phi_s$, $v_s$, $\Phi_s^*$ are the auxiliary quantities of its analysis.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`. Sequences are indexed by `ℕ` with the first element at index $1$; index $0$ is unused (`Phi … 0` and `v … 0` are set to $0$ and appear in no statement). The book defines $\Phi^*_s=\min_{x}\Phi_s(x)$; here $\Phi^*_s$ is defined as $\Phi_s(v_s)$, and the milestone `eq_3_21_form` states $\Phi_s(z)=\Phi^*_s+\frac\alpha2\|z-v_s\|^2$, which shows that $v_s$ is the minimizer and that the two definitions agree (for $\alpha>0$). $\alpha$-strong convexity is the published `OnlineConvexOpt.ConvexBasics.StronglyConvexOn Set.univ f g α`, which is exactly (3.13) with gradient map $g$.
-- source:
--   Bubeck, arXiv:1405.4980v2, §3.7.1, p. 290 (the method); proof of Theorem 3.18, Eq. (3.17), p. 291, and Eq. (3.21), p. 292; β-smoothness §3.2, p. 266; κ = β/α §3.4, p. 278

import Mathlib
import Definitions.Def_OnlineConvexOpt_ConvexBasics_StronglyConvexOn

open scoped InnerProductSpace

namespace ConvexOptAlg.NesterovStrong

/-- Bubeck, §3.4, p. 278: the condition number `κ = β / α`. -/
noncomputable def kappa (α β : ℝ) : ℝ := β / α

/-- Bubeck, §3.2, p. 266: `f` is `β`-smooth with gradient map `g`. The map `g` is the gradient of
`f` at every point (`g x` stands for the book's `∇f(x)`), and it is `β`-Lipschitz:
`‖∇f(x) − ∇f(y)‖ ≤ β‖x − y‖` for all `x, y ∈ ℝⁿ`. -/
def IsBetaSmooth {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ) : Prop :=
  (∀ x, HasGradientAt f (g x) x) ∧ ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖

/-- Bubeck, §3.7.1, p. 290: `(x, y)` is a run of Nesterov's accelerated gradient descent for
a `β`-smooth, `α`-strongly convex function with gradient map `g`. The run starts at an arbitrary
point `x 1 = y 1` (index `0` is unused) and, for every `t ≥ 1`,
`y_{t+1} = x_t − (1/β) ∇f(x_t)` and
`x_{t+1} = (1 + (√κ − 1)/(√κ + 1)) y_{t+1} − ((√κ − 1)/(√κ + 1)) y_t`, with `κ = β/α`. -/
def IsNesterovSCRun {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (α β : ℝ) (x y : ℕ → EuclideanSpace ℝ (Fin n)) : Prop :=
  x 1 = y 1 ∧ ∀ t : ℕ, 1 ≤ t →
    y (t + 1) = x t - (1 / β) • g (x t) ∧
    x (t + 1) =
      (1 + (Real.sqrt (kappa α β) - 1) / (Real.sqrt (kappa α β) + 1)) • y (t + 1) -
        ((Real.sqrt (kappa α β) - 1) / (Real.sqrt (kappa α β) + 1)) • y t

/-- Bubeck, proof of Theorem 3.18, Eq. (3.17), p. 291: the functions `Φ_s`, `s ≥ 1`, built from
the points `x_s`:
`Φ₁(z) = f(x₁) + (α/2)‖z − x₁‖²` and
`Φ_{s+1}(z) = (1 − 1/√κ) Φ_s(z) + (1/√κ)(f(x_s) + ∇f(x_s)ᵀ(z − x_s) + (α/2)‖z − x_s‖²)`.
`Phi … s` is `Φ_s`; index `0` is unused (set to `0`). -/
noncomputable def Phi {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (α β : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) : ℕ → EuclideanSpace ℝ (Fin n) → ℝ
  | 0, _ => 0
  | 1, z => f (x 1) + α / 2 * ‖z - x 1‖ ^ 2
  | s + 2, z =>
      (1 - 1 / Real.sqrt (kappa α β)) * Phi f g α β x (s + 1) z +
        1 / Real.sqrt (kappa α β) *
          (f (x (s + 1)) + ⟪g (x (s + 1)), z - x (s + 1)⟫_ℝ + α / 2 * ‖z - x (s + 1)‖ ^ 2)

/-- Bubeck, proof of Theorem 3.18, Eq. (3.21), p. 292: the centres `v_s` of the functions
`Φ_s`, `v₁ = x₁` (the minimizer of `Φ₁`) and
`v_{s+1} = (1 − 1/√κ) v_s + (1/√κ) x_s − (1/(α√κ)) ∇f(x_s)`. Index `0` is unused (set to `0`). -/
noncomputable def v {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (α β : ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n)) : ℕ → EuclideanSpace ℝ (Fin n)
  | 0 => 0
  | 1 => x 1
  | s + 2 =>
      (1 - 1 / Real.sqrt (kappa α β)) • v g α β x (s + 1) +
        (1 / Real.sqrt (kappa α β)) • x (s + 1) -
          (1 / (α * Real.sqrt (kappa α β))) • g (x (s + 1))

/-- Bubeck, proof of Theorem 3.18, p. 291–292: `Φ∗_s`, the value of `Φ_s` at `v_s`. The book
defines `Φ∗_s = min_{x ∈ ℝⁿ} Φ_s(x)`; that the minimum is attained at `v_s` is the milestone
`eq_3_21_form` (`Φ_s(z) = Φ∗_s + (α/2)‖z − v_s‖²`). -/
noncomputable def PhiStar {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (α β : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (s : ℕ) : ℝ :=
  Phi f g α β x s (v g α β x s)

end ConvexOptAlg.NesterovStrong


