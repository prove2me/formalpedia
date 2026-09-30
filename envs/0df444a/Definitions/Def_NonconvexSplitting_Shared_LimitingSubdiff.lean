-- Prove2me | Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
-- name    : NonconvexSplitting_Shared_LimitingSubdiff
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T12:33:34.188296+00:00
-- url     : https://prove2.me/theorems/0998ec63-dbcc-43e0-a08c-0d79f6a777d5
-- title:
--   Limiting subdifferential of an extended-real-valued function
-- statement:
--   Let $X$ be a real inner product space and $f : X \to [-\infty, +\infty]$.
--
--   A vector $v$ is a **regular subgradient** of $f$ at $x$ if $f(x) < +\infty$ and, for every $\varepsilon > 0$, there is a neighbourhood $U$ of $x$ such that
--   $$
--   f(x) + \langle v, z - x\rangle - \varepsilon\,\|z - x\| \le f(z) \qquad \text{for all } z \in U .
--   $$
--   For $f$ finite at $x$ and never equal to $-\infty$ this is the condition $\liminf_{z \to x} \frac{f(z) - f(x) - \langle v, z - x\rangle}{\|z - x\|} \ge 0$.
--
--   The **limiting subdifferential** $\partial f(x)$ is the set of vectors $v$ such that $f(x) < +\infty$ and there are sequences $x^t \to x$ with $f(x^t) \to f(x)$ and $v^t \to v$, where each $v^t$ is a regular subgradient of $f$ at $x^t$:
--   $$
--   \partial f(x) := \Bigl\{ v : \exists\, x^t \xrightarrow{f} x,\ v^t \to v,\ v^t \text{ a regular subgradient of } f \text{ at } x^t \text{ for each } t \Bigr\}.
--   $$
--
--   This is the subdifferential in which stationarity of the nonconvex composite problem $\min_x h(x) + P(\mathcal M x)$ is expressed; for convex $f$ it is the convex subdifferential and for continuously differentiable $f$ it is $\{\nabla f(x)\}$.
--
--   **Formalization Note** Values live in `EReal`; the liminf condition is encoded in its equivalent $\varepsilon$-neighbourhood form, which avoids a liminf over a punctured neighbourhood in `EReal`. The $f$-attentive convergence $f(x^t) \to f(x)$ is in the topology of `EReal`. Both notions are defined for a general real inner product space; the paper uses $\mathbb{R}^n$.
--
--   **Shared definition.** Serves chunks `01-admm-stationary` (p. 3, Eq. (2); previously `NonconvexSplitting.ProxADMM.LimitingSubdiff`), `03-admm-kl-convergence` (p. 3, Eq. (2) and the definition of dom ∂f on p. 4; previously `NonconvexSplitting.ADMMKL.LimitingSubdiff`) and `04-proximal-gradient` (p. 3, Eq. (2); previously `NonconvexSplitting.ProxGrad.LimitingSubdiff`). Every copy had the same Lean body, identical up to the namespace, and the same conventions; it is reviewed once here for all of them.
-- source:
--   Li & Pong, Global Convergence of Splitting Methods for Nonconvex Composite Optimization, arXiv:1407.0753v6, p. 3, Eq. (2); shared by chunks 01-admm-stationary, 03-admm-kl-convergence, 04-proximal-gradient

import Mathlib

open Filter Topology
open scoped InnerProductSpace

namespace NonconvexSplitting.Shared

/-- `v` is a regular (Fréchet) subgradient of the extended-real-valued function `f` at `x`:
`f x < +∞` and, for every `ε > 0`, `f x + ⟪v, z - x⟫ - ε ‖z - x‖ ≤ f z` for all `z` near `x`.
For `f` never equal to `-∞` this is the condition
`liminf_{z → x} (f z - f x - ⟪v, z - x⟫) / ‖z - x‖ ≥ 0` inside (2) of Li–Pong (p. 3). -/
def IsRegularSubgrad {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → EReal) (x v : X) : Prop :=
  f x ≠ ⊤ ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ z in 𝓝 x,
    f x + ((⟪v, z - x⟫_ℝ - ε * ‖z - x‖ : ℝ) : EReal) ≤ f z

/-- The limiting subdifferential (2) of Li–Pong (p. 3): `v ∈ ∂f(x)` iff `f x < +∞` and there are
sequences `xs t → x` with `f (xs t) → f x` and `vs t → v`, where each `vs t` is a regular
subgradient of `f` at `xs t`. -/
def LimitingSubdiff {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → EReal) (x : X) : Set X :=
  {v | f x ≠ ⊤ ∧ ∃ xs vs : ℕ → X,
    Tendsto xs atTop (𝓝 x) ∧ Tendsto (fun t => f (xs t)) atTop (𝓝 (f x)) ∧
    Tendsto vs atTop (𝓝 v) ∧ ∀ t, IsRegularSubgrad f (xs t) (vs t)}

end NonconvexSplitting.Shared


