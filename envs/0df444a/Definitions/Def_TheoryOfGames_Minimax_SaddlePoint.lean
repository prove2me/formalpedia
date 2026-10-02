-- Prove2me | Definitions.Def_TheoryOfGames_Minimax_SaddlePoint
-- name    : TheoryOfGames_Minimax_SaddlePoint
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T03:04:34.735863+00:00
-- url     : https://prove2.me/theorems/c06b5487-55ce-40f0-9894-8049f37640d3
-- title:
--   Max–Min operations, saddle points and the sets $A^\phi$, $B^\phi$ (13.2, 13.4.2, 13.5.1)
-- statement:
--   Let $\phi(x, y)$ be a real-valued function of two variables, $x$ ranging over a set $X$ and $y$ over a set $Y$ (no finiteness or topology is assumed).
--
--   1. $\operatorname{Min}_y \phi(x, y)$ is a function of $x$ alone and $\operatorname{Max}_x \phi(x, y)$ a function of $y$ alone (13.2.2); from them one forms the two expressions of (13:4),
--   $$\operatorname{Max}_x \operatorname{Min}_y \phi(x, y), \qquad \operatorname{Min}_y \operatorname{Max}_x \phi(x, y).$$
--   2. **Standing hypothesis** (13.2.1): the book restricts its considerations "to such functions, for which Max and Min exist". Here this is the predicate `MaxMinAttained φ`: $\operatorname{Min}_y \phi(x,y)$ is attained for every $x$, $\operatorname{Max}_x \phi(x,y)$ is attained for every $y$, and the outer maximum of $\operatorname{Min}_y\phi(x,y)$ over $x$ and the outer minimum of $\operatorname{Max}_x\phi(x,y)$ over $y$ are attained.
--   3. **Saddle point** (13.4.2): $x_0, y_0$ is a saddle point of $\phi$ if at the same time $\phi(x, y_0)$ assumes its maximum at $x = x_0$ and $\phi(x_0, y)$ assumes its minimum at $y = y_0$:
--   $$\phi(x, y_0) \le \phi(x_0, y_0) \le \phi(x_0, y) \quad \text{for all } x \in X,\ y \in Y.$$
--   4. **The sets $A^\phi$, $B^\phi$** (13.5.1): $A^\phi$ is the set of all $x_0$ at which $\operatorname{Min}_y \phi(x, y)$ assumes its maximum, and $B^\phi$ the set of all $y_0$ at which $\operatorname{Max}_x \phi(x, y)$ assumes its minimum.
--
--   These are the notions of the "functional calculus" of §13 on which the theory of zero-sum two-person games rests: applied with $\phi = K$ on mixed strategies they give the good strategies of §17.
--
--   **Formalization Note** $\operatorname{Min}_y$ and $\operatorname{Max}_x$ are written as the real infimum `⨅` and supremum `⨆`. These coincide with the book's attained minimum and maximum exactly under the standing hypothesis `MaxMinAttained φ`, which every theorem using these definitions assumes; without it the real `⨅`/`⨆` may take a junk value.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), pp. 89–90, 13.2.1–13.2.2; p. 94, (13:4); p. 95, 13.4.2; pp. 95–96, 13.5.1

import Mathlib

namespace TheoryOfGames.Minimax

variable {X Y : Type*}

/-- `Min_y φ(x, y)`, a function of `x` (13.2.2). It is the attained minimum whenever
`MaxMinAttained φ` holds. -/
noncomputable def minOver (φ : X → Y → ℝ) (x : X) : ℝ := ⨅ y, φ x y

/-- `Max_x φ(x, y)`, a function of `y` (13.2.2). It is the attained maximum whenever
`MaxMinAttained φ` holds. -/
noncomputable def maxOver (φ : X → Y → ℝ) (y : Y) : ℝ := ⨆ x, φ x y

/-- `Max_x Min_y φ(x, y)`, the first expression of (13:4). -/
noncomputable def maxMin (φ : X → Y → ℝ) : ℝ := ⨆ x, minOver φ x

/-- `Min_y Max_x φ(x, y)`, the second expression of (13:4). -/
noncomputable def minMax (φ : X → Y → ℝ) : ℝ := ⨅ y, maxOver φ y

/-- The standing hypothesis of 13.2.1 ("we are restricting our considerations to such
functions, for which Max and Min exist"), for the four maxima and minima of (13:4):
`Min_y φ(x, y)` is attained for every `x`, `Max_x φ(x, y)` is attained for every `y`,
`Max_x Min_y φ(x, y)` is attained and `Min_y Max_x φ(x, y)` is attained. -/
structure MaxMinAttained (φ : X → Y → ℝ) : Prop where
  min_attained : ∀ x, ∃ y₀, ∀ y, φ x y₀ ≤ φ x y
  max_attained : ∀ y, ∃ x₀, ∀ x, φ x y ≤ φ x₀ y
  maxMin_attained : ∃ x₀, ∀ x, minOver φ x ≤ minOver φ x₀
  minMax_attained : ∃ y₀, ∀ y, maxOver φ y₀ ≤ maxOver φ y

/-- Saddle point (13.4.2): `x₀, y₀` is a saddle point of `φ` if at the same time `φ(x, y₀)`
assumes its maximum at `x = x₀` and `φ(x₀, y)` assumes its minimum at `y = y₀`. -/
def IsSaddlePoint (φ : X → Y → ℝ) (x₀ : X) (y₀ : Y) : Prop :=
  (∀ x, φ x y₀ ≤ φ x₀ y₀) ∧ (∀ y, φ x₀ y₀ ≤ φ x₀ y)

/-- `A^φ` (13.5.1): the set of all `x₀` at which `Min_y φ(x, y)` assumes its maximum. -/
def setA (φ : X → Y → ℝ) : Set X := {x₀ | ∀ x, minOver φ x ≤ minOver φ x₀}

/-- `B^φ` (13.5.1): the set of all `y₀` at which `Max_x φ(x, y)` assumes its minimum. -/
def setB (φ : X → Y → ℝ) : Set Y := {y₀ | ∀ y, maxOver φ y₀ ≤ maxOver φ y}

end TheoryOfGames.Minimax


