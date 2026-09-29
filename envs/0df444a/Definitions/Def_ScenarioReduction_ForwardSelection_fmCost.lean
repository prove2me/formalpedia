-- Prove2me | Definitions.Def_ScenarioReduction_ForwardSelection_fmCost
-- name    : ScenarioReduction_ForwardSelection_fmCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T14:56:00.772038+00:00
-- url     : https://prove2.me/theorems/0b4b49d8-c019-420b-beaa-737613c247e6
-- title:
--   Cost $c(\omega,\tilde\omega)=\max\{1,h(\|\omega-\omega_0\|),h(\|\tilde\omega-\omega_0\|)\}\|\omega-\tilde\omega\|$ of eq. (3) and its scenario matrix
-- statement:
--   Let $E$ be a finite-dimensional real vector space with a norm $\|\cdot\|$ (the paper's $\mathbb R^s$ with "some norm"), let $\omega_0\in E$ be a fixed reference point, and let $h:\mathbb R_+\to\mathbb R_+$ be a **growth function**: $h$ is continuous and nondecreasing on $[0,\infty)$, $h(0)=0$, and $h(r)\ge 0$ for $r\ge 0$.
--
--   The **cost** of eq. (3) is
--   $$
--   c(\omega,\tilde\omega)=\max\bigl\{1,\;h(\|\omega-\omega_0\|),\;h(\|\tilde\omega-\omega_0\|)\bigr\}\cdot\|\omega-\tilde\omega\|,\qquad \omega,\tilde\omega\in E .
--   $$
--   For $N$ scenarios $\omega_1,\dots,\omega_N\in E$, the **scenario cost matrix** has entries $c(\omega_i,\omega_j)$.
--
--   The cost $c$ is nonnegative, symmetric and vanishes on the diagonal; it measures distances between scenarios with a weight that grows with the distance from $\omega_0$, and it is the cost of every transportation problem and every reduction cost $D_J$ of this mission.
--
--   **Formalization Note** The file declares three objects: the predicate `IsGrowthFunction h` bundling the standing assumptions on $h$ (p. 187), the cost `fmCost h ω₀ x y`, and the matrix `scenCost h ω₀ ω i j = fmCost h ω₀ (ω i) (ω j)` for scenarios `ω : Fin N → E` (indices $0,\dots,N-1$ stand for the paper's $1,\dots,N$). $h$ is given on all of $\mathbb R$; its values at negative arguments are never used, since it is only evaluated at norms. The closed set $\Omega\subset\mathbb R^s$ of the paper plays no role beyond containing the scenarios and is omitted.
-- source:
--   Heitsch, Römisch, Scenario Reduction Algorithms in Stochastic Programming, Comput. Optim. Appl. 24 (2003), p. 187, eq. (3) and the assumptions on h above it; p. 188 (some norm on R^s)

import Mathlib

namespace ScenarioReduction.ForwardSelection

/-- The standing assumptions on the growth function `h` (Heitsch–Römisch 2003, p. 187):
`h : ℝ₊ → ℝ₊` is continuous and nondecreasing with `h 0 = 0`. The function is given on all of `ℝ`,
and every assumption is imposed on `[0, ∞)`, the only arguments at which it is evaluated. -/
def IsGrowthFunction (h : ℝ → ℝ) : Prop :=
  ContinuousOn h (Set.Ici 0) ∧ MonotoneOn h (Set.Ici 0) ∧ h 0 = 0 ∧ ∀ r : ℝ, 0 ≤ r → 0 ≤ h r

/-- The cost of eq. (3), p. 187:
`c(ω, ω̃) = max{1, h(‖ω − ω₀‖), h(‖ω̃ − ω₀‖)} · ‖ω − ω̃‖`. -/
noncomputable def fmCost {E : Type*} [NormedAddCommGroup E] (h : ℝ → ℝ) (ω₀ x y : E) : ℝ :=
  max (max 1 (h ‖x - ω₀‖)) (h ‖y - ω₀‖) * ‖x - y‖

/-- The cost matrix of `N` scenarios `ω 0, …, ω (N-1)`: entry `(i, j)` is `c(ωᵢ, ωⱼ)` of eq. (3). -/
noncomputable def scenCost {E : Type*} [NormedAddCommGroup E] {N : ℕ} (h : ℝ → ℝ) (ω₀ : E)
    (ω : Fin N → E) (i j : Fin N) : ℝ :=
  fmCost h ω₀ (ω i) (ω j)

end ScenarioReduction.ForwardSelection


