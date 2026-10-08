-- Prove2me | Definitions.Def_RobinsonNSIFT_Implicit_Basic
-- name    : RobinsonNSIFT_Implicit_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T05:49:43.805144+00:00
-- url     : https://prove2.me/theorems/e8788c66-fc68-4c01-9113-c4b95ac7540a
-- title:
--   Strong approximation in x (Definition 2.4) and lower bounds for the expansion modulus δ(f, S)
-- statement:
--   This file fixes the two notions on which Robinson's nonsmooth implicit-function theorem rests.
--
--   1. **Expansion modulus.** For a map $f$ between metric spaces $(X,d)$ and $(Y,e)$ and a set $S \subseteq X$, Robinson (p. 298) writes
--   $$
--   \delta(f, S) = \inf\left\{ \frac{e[f(x_1), f(x_2)]}{d(x_1, x_2)} \;:\; x_1 \neq x_2,\ x_1, x_2 \in S \right\}.
--   $$
--   A positive value means that $f$ is one-to-one on $S$ and that its inverse is Lipschitzian with modulus $\delta(f,S)^{-1}$. We say that **$f$ expands $S$ at rate at least $d$** when
--   $$
--   d \cdot d(x_1, x_2) \le e[f(x_1), f(x_2)] \qquad \text{for all } x_1, x_2 \in S,
--   $$
--   that is, exactly when $d \le \delta(f, S)$.
--
--   2. **Strong approximation in $x$** (Definition 2.4, p. 295). Let $X, Y, Z$ be normed linear spaces, $F : X \times Y \to Z$, $f : X \to Z$, $x_0 \in X$, $y_0 \in Y$. Then $f$ **strongly approximates $F$ in $x$ at $(x_0, y_0)$**, written $f \approx_x F$ at $(x_0,y_0)$, if for each $\varepsilon > 0$ there are neighborhoods $U$ of $x_0$ and $V$ of $y_0$ such that for all $x, x' \in U$ and all $y \in V$,
--   $$
--   \big\| [F(x,y) - f(x)] - [F(x',y) - f(x')] \big\| \le \varepsilon \|x - x'\|.
--   $$
--   In words: the difference $F(\cdot, y) - f$ is Lipschitzian near $x_0$ with arbitrarily small modulus, uniformly for $y$ near $y_0$. It replaces the strong partial Fréchet derivative of the classical implicit-function theorem.
--
--   **Formalization Note** The paper's $\delta(f,S)$ is an infimum that equals $+\infty$ when $S$ has fewer than two points; a real-valued infimum would return the junk value $0$ there. The file therefore records lower bounds `ExpansionAtLeast f S d` (meaning $d \le \delta(f,S)$), and every statement of the mission quantifies over all such $d$. The paper's $F$ is defined only on $\Xi \times H$ and $f$ only on $\Xi$; here they are total curried functions `F x y`, and every statement of the mission constrains them on $\Xi \times H$ only. The neighborhoods in Definition 2.4 are arbitrary members of the neighborhood filter (they need not be open), as in the paper.
-- source:
--   Robinson, An Implicit-Function Theorem for a Class of Nonsmooth Functions, Math. Oper. Res. 16(2) (1991), §2 and §3, Definition 2.4 and the definition of δ(f, X), pp. 294, 295, 298

import Mathlib

namespace RobinsonNSIFT.Implicit

open Set Filter Topology Metric

/-- Robinson (1991), p. 298: "δ(f, S) ≥ d". Every pair of points of `S` is separated by `f`
at rate at least `d`: `d · dist x₁ x₂ ≤ dist (f x₁) (f x₂)` for all `x₁, x₂ ∈ S`. The paper's
`δ(f, S) = inf {e[f(x₁), f(x₂)] / d(x₁, x₂) | x₁ ≠ x₂, x₁, x₂ ∈ S}` is the largest such `d`. -/
def ExpansionAtLeast {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    (f : α → β) (S : Set α) (d : ℝ) : Prop :=
  ∀ x₁ ∈ S, ∀ x₂ ∈ S, d * dist x₁ x₂ ≤ dist (f x₁) (f x₂)

/-- Robinson (1991), Definition 2.4, p. 295: `f` strongly approximates `F` in `x` at `(x₀, y₀)`,
written `f ≈ₓ F at (x₀, y₀)`. `F` is curried: `F x y` is the paper's `F(x, y)`. -/
def StronglyApproxInX {X Y Z : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedAddCommGroup Z] (f : X → Z) (F : X → Y → Z) (x₀ : X) (y₀ : Y) : Prop :=
  ∀ ε > (0 : ℝ), ∃ U ∈ 𝓝 x₀, ∃ V ∈ 𝓝 y₀, ∀ x ∈ U, ∀ x' ∈ U, ∀ y ∈ V,
    ‖(F x y - f x) - (F x' y - f x')‖ ≤ ε * ‖x - x'‖

end RobinsonNSIFT.Implicit


