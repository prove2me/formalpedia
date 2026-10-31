-- Prove2me | Definitions.Def_AccelNewtonDinkelbach_superdiff
-- name    : AccelNewtonDinkelbach_superdiff
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:14:36.971991+00:00
-- url     : https://prove2.me/theorems/abb9bab7-081e-41bf-93e9-ed4f2e7208b3
-- title:
--   Set of supergradients $\partial f(x_0)$ of a proper concave function on $\mathbb R$
-- statement:
--   Let $f:\mathbb R\to\bar{\mathbb R}=\mathbb R\cup\{\pm\infty\}$ be a proper concave function with effective domain $\operatorname{dom}(f)=\{x:-\infty<f(x)<\infty\}$. For $x_0\in\operatorname{dom}(f)$, the **set of supergradients** of $f$ at $x_0$ is
--
--   $$\partial f(x_0)=\{g\in\mathbb R:\ f(x)\le f(x_0)+g\,(x-x_0)\ \text{ for all } x\in\mathbb R\}.$$
--
--   It is a closed interval (possibly empty or unbounded). At an interior point of $\operatorname{dom}(f)$ it is the interval between the right derivative $f'_+(x_0)$ and the left derivative $f'_-(x_0)$ (for a concave function $f'_+(x_0)\le f'_-(x_0)$). The Newton–Dinkelbach method queries one element of this set at each iterate.
--
--   **Formalization Note** The proper concave $f$ is encoded by a set `dom` (its effective domain) and a real function `f` concave on `dom`; a point outside `dom` is a point where the paper's $f$ equals $-\infty$, so the defining inequality is required only for $x\in$ `dom` (it holds trivially elsewhere).
-- source:
--   Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, §2 (Preliminaries), p.6

import Mathlib

namespace AccelNewtonDinkelbach

/-- **Set of supergradients `∂f(x₀)` of a proper concave function on `ℝ`.**
Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, §2, p.6: "For a point x0 ∈ dom(f), denote the set
of supergradients of f at x0 as ∂f(x0) := {g : f(x) ≤ f(x0) + g(x − x0) ∀x ∈ R}."

`superdiff dom f x₀` is the set of slopes `g` with `f y ≤ f x₀ + g (y − x₀)` for every `y ∈ dom`.

**Formalization Note** A proper concave `f : ℝ → ℝ̄` is encoded by its effective domain
`dom : Set ℝ` together with a real-valued `f : ℝ → ℝ` that is concave on `dom`: a point outside
`dom` is a point where the paper's `f` is `−∞`, and the values of the Lean `f` there are ignored.
For `y ∉ dom` the paper's inequality `−∞ ≤ …` holds trivially, so quantifying over `y ∈ dom` is the
paper's set. The paper defines `∂f(x₀)` only for `x₀ ∈ dom(f)`; every use below asserts that
membership separately. -/
def superdiff (dom : Set ℝ) (f : ℝ → ℝ) (x₀ : ℝ) : Set ℝ :=
  {g : ℝ | ∀ y ∈ dom, f y ≤ f x₀ + g * (y - x₀)}

end AccelNewtonDinkelbach


