-- Prove2me | Definitions.Def_NonmonotoneLS_RLinear_Regions
-- name    : NonmonotoneLS_RLinear_Regions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T00:22:57.964807+00:00
-- url     : https://prove2.me/theorems/5a949d3e-4749-4942-8b67-e29d77c83f6f
-- title:
--   Level set $\mathcal L$, $d_{\max}$, the region $\bar{\mathcal L}$ and strong convexity (3.1)
-- statement:
--   Let $f : \mathbb{R}^n \to \mathbb{R}$ and let $x_k$, $d_k$ be the iterates and directions of a run.
--
--   1. The **level set** is $\mathcal L = \{x \in \mathbb{R}^n : f(x) \le f(x_0)\}$.
--   2. $d_{\max} = \sup_k \|d_k\| \in [0, \infty]$.
--   3. $\bar{\mathcal L}$ is the set of $x \in \mathbb{R}^n$ whose distance to $\mathcal L$ is at most $\mu d_{\max}$.
--   4. $f$ is **strongly convex with constant** $\gamma$ if $\gamma > 0$ and, for all $x, y \in \mathbb{R}^n$,
--
--   $$f(x) \ge f(y) + \nabla f(y)(x - y) + \frac{1}{2\gamma}\|x - y\|^2. \quad (3.1)$$
--
--   $\bar{\mathcal L}$ is the region on which the proof of Theorem 3.1 takes a Lipschitz constant for $\nabla f$: it contains every point $x + t d_k$ with $x \in \mathcal L$ and $0 \le t \le \mu$.
--
--   **Formalization Note.** $d_{\max}$ and the distance to $\mathcal L$ are computed in $[0, \infty]$. If the directions are unbounded, $d_{\max} = \infty$ and $\bar{\mathcal L}$ is the whole space; a real-valued supremum would instead return $0$ and shrink $\bar{\mathcal L}$ to the closure of $\mathcal L$. Strong convexity keeps the paper's constant $\gamma$ (the modulus is $1/\gamma$) rather than Mathlib's `StrongConvexOn`.
-- source:
--   Zhang, Hager, A Nonmonotone Line Search Technique and Its Application to Unconstrained Optimization, SIAM J. Optim. 14 (2004), p. 1049, Eq. (3.1); p. 1050, proof of Theorem 3.1 (definitions of L, d_max and L-bar; also p. 1047, Theorem 2.2)

import Mathlib
import Definitions.Def_NonmonotoneLS_Shared_Params

open scoped ENNReal NNReal InnerProductSpace

namespace NonmonotoneLS.RLinear

variable {n : ℕ}

/-- The level set `𝓛 = {y : f(y) ≤ f(x₀)}` (p. 1050). -/
def levelSet (f : EuclideanSpace ℝ (Fin n) → ℝ) (x₀ : EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {y | f y ≤ f x₀}

/-- `d_max = sup_k ‖d_k‖`, taken in `[0, ∞]` (it is `∞` when the directions are unbounded). -/
noncomputable def dmax (d : ℕ → EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  ⨆ k, (‖d k‖₊ : ℝ≥0∞)

/-- `𝓛̄`: the points whose distance to `𝓛 = {y : f(y) ≤ f(x₀)}` is at most `μ d_max`
(p. 1050), computed in `[0, ∞]`. -/
noncomputable def Lbar (p : Shared.Params) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {y | Metric.infEDist y (levelSet f (x 0)) ≤ ENNReal.ofReal p.μ * dmax d}

/-- Strong convexity in the form (3.1) (p. 1049), with the paper's constant `γ > 0`
(the modulus is `1/γ`): `f(x) ≥ f(y) + ∇f(y)(x - y) + (1/(2γ)) ‖x - y‖²` for all `x, y`. -/
def IsStronglyConvexWith (f : EuclideanSpace ℝ (Fin n) → ℝ) (γ : ℝ) : Prop :=
  0 < γ ∧ ∀ x y : EuclideanSpace ℝ (Fin n),
    f y + ⟪gradient f y, x - y⟫_ℝ + 1 / (2 * γ) * ‖x - y‖ ^ 2 ≤ f x

end NonmonotoneLS.RLinear


