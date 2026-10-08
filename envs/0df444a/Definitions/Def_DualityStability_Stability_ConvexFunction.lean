-- Prove2me | Definitions.Def_DualityStability_Stability_ConvexFunction
-- name    : DualityStability_Stability_ConvexFunction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:41:50.100161+00:00
-- url     : https://prove2.me/theorems/f7acdf5e-25c5-4749-a53d-a3f7d56364a8
-- title:
--   Convex, proper convex, concave and proper concave functions with values in [−∞, +∞], §2, pp. 170–171
-- statement:
--   Let $E$ be a real vector space. Following Rockafellar, an (infinite-valued) **convex function** on $E$ is an everywhere-defined function $f : E \to [-\infty, +\infty]$ whose (upper) **epigraph**
--
--   $$
--   \operatorname{epi} f = \{(x, \mu) \mid x \in E,\ \mu \in \mathbb{R},\ \mu \ge f(x)\}
--   $$
--
--   is a convex subset of $E \oplus \mathbb{R}$.
--
--   1. A convex function $f$ is **proper** if $f(x) > -\infty$ for every $x$ and $f(x) < +\infty$ for at least one $x$.
--   2. A function $g : F \to [-\infty, +\infty]$ is **concave** if $-g$ is convex.
--   3. A concave function $g$ is **proper** if $g(y) < +\infty$ for every $y$ and $g(y) > -\infty$ for at least one $y$, i.e. if $-g$ is proper convex.
--
--   These are the classes of the objective pieces $f$ and $g$ of the problem $(P)$: minimize $f(x) - g(Ax)$.
--
--   **Formalization Note** Values are in `EReal`. Convexity is the paper's own definition, convexity of the epigraph in $E \times \mathbb{R}$ (with real second coordinate); for functions that never take $-\infty$ it is equivalent to the inequality $f(\lambda x_1 + (1-\lambda)x_2) \le \lambda f(x_1) + (1-\lambda) f(x_2)$, $0<\lambda<1$. Concavity is literally "$-g$ is convex", with EReal negation.
-- source:
--   Rockafellar, Duality and Stability in Extremum Problems Involving Convex Functions, Pacific J. Math. 21 (1967), p. 170 (convex function, proper), p. 171 (concave function), §2

import Mathlib

namespace DualityStability.Stability

/-- Rockafellar (1967), §2, p. 170: an (infinite-valued) *convex function* `f` on `E` is an
everywhere-defined function with values in `[−∞, +∞]` whose (upper) epigraph
`{(x, μ) | x ∈ E, μ ∈ ℝ, μ ≥ f(x)}` is a convex set in `E ⊕ ℝ`. -/
def ConvexFn {E : Type*} [AddCommGroup E] [Module ℝ E] (f : E → EReal) : Prop :=
  Convex ℝ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)}

/-- Rockafellar (1967), §2, p. 170: a convex function `f` is *proper* if `f(x) > −∞` for all `x`
and `f(x) < +∞` for at least one `x`. -/
def ProperConvexFn {E : Type*} [AddCommGroup E] [Module ℝ E] (f : E → EReal) : Prop :=
  ConvexFn f ∧ (∀ x, ⊥ < f x) ∧ ∃ x, f x < ⊤

/-- Rockafellar (1967), §2, p. 171: `g` is *concave* if `−g` is convex. -/
def ConcaveFn {F : Type*} [AddCommGroup F] [Module ℝ F] (g : F → EReal) : Prop :=
  ConvexFn (fun y => -g y)

/-- A concave function `g` is *proper* if `−g` is a proper convex function, i.e. `g(y) < +∞` for
all `y` and `g(y) > −∞` for at least one `y` (Rockafellar (1967), pp. 170–171). -/
def ProperConcaveFn {F : Type*} [AddCommGroup F] [Module ℝ F] (g : F → EReal) : Prop :=
  ConcaveFn g ∧ (∀ y, g y < ⊤) ∧ ∃ y, ⊥ < g y

end DualityStability.Stability


