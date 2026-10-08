-- Prove2me | Definitions.Def_PrimalDualSubgrad_Stoch_ProxSetting
-- name    : PrimalDualSubgrad_Stoch_ProxSetting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:44:37.745351+00:00
-- url     : https://prove2.me/theorems/1b85ed4d-1739-4844-9cac-945599b335be
-- title:
--   Prox-function of a closed convex set, the argmin map $\pi_\beta$, the sequence $\hat\beta_k$ and the gap $\delta_k(D)$
-- statement:
--   Let $E$ be a finite-dimensional real vector space with an arbitrary norm $\|\cdot\|$, and let $E^*$ be its dual with the dual norm $\|s\|_* = \max\{\langle s, x\rangle : \|x\| \le 1\}$; the value of $s \in E^*$ at $x \in E$ is written $\langle s, x\rangle$.
--
--   1. **Prox-function.** Let $Q \subseteq E$ be closed and convex. A function $d$ is a *prox-function* of $Q$ with convexity parameter $\sigma > 0$ and prox-center $x_0$ if $d$ is continuous on $Q$, strongly convex on $Q$ in the sense
--   $$d(\alpha x + (1-\alpha) y) \le \alpha d(x) + (1-\alpha) d(y) - \tfrac12 \sigma \alpha (1-\alpha) \|x - y\|^2 \qquad (x, y \in Q,\ \alpha \in [0,1]),$$
--   and $x_0 \in Q$ minimizes $d$ over $Q$ with $d(x_0) = 0$.
--
--   2. **Argmin map.** A map $(\beta, s) \mapsto \pi_\beta(s)$ is an argmin map for $(Q, d)$ if, for every $\beta > 0$ and $s \in E^*$, the point $\pi_\beta(s)$ lies in $Q$ and minimizes $x \mapsto -\langle s, x\rangle + \beta d(x)$ over $Q$.
--
--   3. **The sequence $\hat\beta$.** $\hat\beta_0 = \hat\beta_1 = 1$ and $\hat\beta_{i+1} = \hat\beta_i + 1/\hat\beta_i$ for $i \ge 1$ (so $\hat\beta_2 = 2$).
--
--   4. **Gap.** For $D \in \mathbb R$ let $\mathcal F_D = \{x \in Q : d(x) \le D\}$. For test points $x_0, x_1, \dots \in E$ and answers $g_0, g_1, \dots \in E^*$, the gap after $k+1$ steps with unit weights is
--   $$\delta_k(D) = \max_x\Big\{ \sum_{i=0}^k \langle g_i, x_i - x\rangle : x \in \mathcal F_D \Big\}.$$
--
--   These are the objects of the dual averaging framework on which both the deterministic method of simple dual averages and its stochastic version are built.
--
--   **Formalization Note** $E^*$ is `StrongDual ℝ E` with the operator norm. Strong convexity is Mathlib's `StrongConvexOn Q σ d`, whose modulus $\alpha(1-\alpha)\frac{\sigma}{2}\|x-y\|^2$ is exactly (1.8). The paper writes $\sigma \ge 0$ on p. 5, but its Appendix definition (p. 36) and every bound with $1/\sigma$ need $\sigma > 0$, which is required here. The argmin map is a function together with its defining property, not a choice. The gap is a real supremum: for $D \ge 0$ the set $\mathcal F_D$ contains $x_0$ and is bounded (by $d(x) \ge \frac{\sigma}{2}\|x - x_0\|^2$ on $Q$), so the supremum is a maximum; every statement using it assumes $D \ge 0$.
-- source:
--   Nesterov, Primal-dual subgradient methods for convex problems, Math. Program. 120 (2009), p. 5, (1.8)–(1.9); p. 6, F_D; p. 7, (2.4); p. 8, (2.10); p. 10, (2.19)

import Mathlib

namespace PrimalDualSubgrad.Stoch

open Finset

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Nesterov 2009, p. 5, (1.8)–(1.9): `d` is a prox-function of the closed convex set `Q` with
convexity parameter `σ > 0` and prox-center `x0`. `StrongConvexOn Q σ d` is exactly (1.8)
(Mathlib's modulus is `a * b * (σ / 2) * ‖x - y‖ ^ 2`); it also contains the convexity of `Q`.
The prox-center minimizes `d` on `Q` and is normalized by `d x0 = 0`. `d` is only continuous on
`Q`, not differentiable; its values outside `Q` play no role. -/
structure ProxFunction (Q : Set E) (d : E → ℝ) (σ : ℝ) (x0 : E) : Prop where
  isClosed : IsClosed Q
  convex : Convex ℝ Q
  continuousOn : ContinuousOn d Q
  sigma_pos : 0 < σ
  strongConvexOn : StrongConvexOn Q σ d
  x0_mem : x0 ∈ Q
  x0_isMin : ∀ x ∈ Q, d x0 ≤ d x
  d_x0 : d x0 = 0

/-- Nesterov 2009, p. 7, (2.4): `π β s` is a minimizer over `Q` of `x ↦ -⟨s, x⟩ + β d(x)`, for
every `β > 0` and every `s ∈ E*` (the minimizer is unique by strong convexity, so `π` is
determined on `β > 0`). The dual space `E*` is `StrongDual ℝ E` and `⟨s, x⟩ = s x`. -/
def IsArgminMap (Q : Set E) (d : E → ℝ) (π : ℝ → StrongDual ℝ E → E) : Prop :=
  ∀ β : ℝ, 0 < β → ∀ s : StrongDual ℝ E,
    π β s ∈ Q ∧ ∀ x ∈ Q, -(s (π β s)) + β * d (π β s) ≤ -(s x) + β * d x

/-- Nesterov 2009, p. 10, (2.19): `β̂₀ = β̂₁ = 1`, `β̂_{i+1} = β̂_i + 1/β̂_i` for `i ≥ 1`. -/
noncomputable def betaHat : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | (n + 2) => betaHat (n + 1) + 1 / betaHat (n + 1)

/-- The set `F_D = {x ∈ Q : d(x) ≤ D}` (Nesterov 2009, p. 6). -/
def levelSet (Q : Set E) (d : E → ℝ) (D : ℝ) : Set E := {x | x ∈ Q ∧ d x ≤ D}

/-- Nesterov 2009, p. 8, (2.10), with all weights `λ_i = 1` (the case of (2.21) and of (6.4)):
`δ_k(D) = max { ∑_{i=0}^k ⟨g_i, x_i - x⟩ : x ∈ F_D }`, written as a real `sSup`. When `d` is a
prox-function with `σ > 0` and `D ≥ 0`, the set `F_D` contains the prox-center and is bounded, so
the supremum is over a nonempty bounded-above set (and is attained, `F_D` being compact). -/
noncomputable def gap (Q : Set E) (d : E → ℝ) (g : ℕ → StrongDual ℝ E) (x : ℕ → E) (k : ℕ)
    (D : ℝ) : ℝ :=
  sSup ((fun y => ∑ i ∈ range (k + 1), g i (x i - y)) '' levelSet Q d D)

end PrimalDualSubgrad.Stoch


