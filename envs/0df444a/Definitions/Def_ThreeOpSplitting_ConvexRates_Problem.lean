-- Prove2me | Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
-- name    : ThreeOpSplitting_ConvexRates_Problem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:53:09.180999+00:00
-- url     : https://prove2.me/theorems/e90f0eef-016c-411e-861a-96f47bf7d79d
-- title:
--   Problem (3.1): closed proper convex functions, proximal maps, smooth convex term and the objective $f+g+h$
-- statement:
--   Let $H$ be a real Hilbert space. This file fixes the data of problem (3.1) of Davis and Yin,
--   $$\min_{x \in H}\; f(x) + g(x) + h(x).$$
--
--   1. A function $f : H \to (-\infty, +\infty]$ is **closed, proper and convex** if it never takes the value $-\infty$, it is finite at some point, it is lower semicontinuous, and its epigraph $\{(x,t) \in H \times \mathbb R : f(x) \le t\}$ is convex.
--   2. For $\gamma > 0$, a map $P : H \to H$ is **the proximal map** $\operatorname{prox}_{\gamma f}$ if for every $x \in H$ the point $P(x)$ minimises
--   $$y \mapsto f(y) + \frac{1}{2\gamma}\|y - x\|^2 .$$
--   3. A function $h : H \to \mathbb R$ is **convex and $\beta^{-1}$-smooth** if it is convex, (Fréchet) differentiable, and its gradient satisfies $\|\nabla h(x) - \nabla h(y)\| \le \beta^{-1}\|x - y\|$ for all $x, y$.
--   4. The **objective** is $(f + g + h)(x) = f(x) + g(x) + h(x) \in (-\infty, +\infty]$.
--
--   These are the standing assumptions of Section 3.1: $f, g$ closed, proper, convex; $h$ convex and differentiable with $\beta^{-1}$-Lipschitz gradient. The proximal maps are the resolvents $J_{\gamma\partial f}$, $J_{\gamma\partial g}$ that Algorithm 2 evaluates.
--
--   **Formalization Note** Extended values are kept: $f$ and $g$ take values in `EReal`, so indicator functions of closed convex sets (constrained problems) are included. The proximal map is not constructed; a map is required to satisfy the minimisation property. For $f$ closed, proper, convex and $\gamma > 0$ the minimiser exists and is unique, so nothing is lost, and the minimum value is automatically finite. The constant $\beta > 0$ is a separate hypothesis wherever it is used.
-- source:
--   Davis and Yin, A Three-Operator Splitting Scheme and its Optimization Applications, Set-Valued Var. Anal. 25 (2017), https://doi.org/10.1007/s11228-017-0421-z, p. 838, Section 3.1, problem (3.1) and Algorithm 2

import Mathlib

open InnerProductSpace

namespace ThreeOpSplitting.ConvexRates

/-- `f : H → (-∞, +∞]` is closed, proper and convex: it never takes the value `-∞`, it is finite
somewhere, it is lower semicontinuous (closed), and its epigraph `{(x, t) | f x ≤ t}` is convex. -/
def IsProperClosedConvex {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) : Prop :=
  (∀ x : H, f x ≠ ⊥) ∧ (∃ x : H, f x ≠ ⊤) ∧ LowerSemicontinuous f ∧
    Convex ℝ {p : H × ℝ | f p.1 ≤ (p.2 : EReal)}

/-- `P` is (a choice of) the proximal map `prox_{γf}`: for every `x`, `P x` minimises
`y ↦ f y + ‖y - x‖² / (2γ)`. For `f` closed, proper, convex and `γ > 0` the minimiser exists and
is unique, so `P` is then determined. -/
def IsProx {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (γ : ℝ) (f : H → EReal) (P : H → H) : Prop :=
  ∀ x y : H, f (P x) + ((‖P x - x‖ ^ 2 / (2 * γ) : ℝ) : EReal) ≤
    f y + ((‖y - x‖ ^ 2 / (2 * γ) : ℝ) : EReal)

/-- `h : H → ℝ` is convex and differentiable and its gradient `∇h` is `β⁻¹`-Lipschitz. -/
def IsSmoothConvex {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (β : ℝ) (h : H → ℝ) : Prop :=
  ConvexOn ℝ Set.univ h ∧ Differentiable ℝ h ∧
    ∀ x y : H, ‖gradient h x - gradient h y‖ ≤ β⁻¹ * ‖x - y‖

/-- The objective `(f + g + h)(x)` of problem (3.1), valued in `(-∞, +∞]`. -/
noncomputable def objective {H : Type*} (f g : H → EReal) (h : H → ℝ) (x : H) : EReal :=
  f x + g x + (h x : EReal)

end ThreeOpSplitting.ConvexRates


