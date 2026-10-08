-- Prove2me | Definitions.Def_DualityStability_Stability_perturbInf
-- name    : DualityStability_Stability_perturbInf
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:42:04.29199+00:00
-- url     : https://prove2.me/theorems/bc9e7bbe-a6cc-4f0d-829f-9f8c1eea880e
-- title:
--   The perturbation function h(z) = inf (P(z)), §4, p. 174
-- statement:
--   Let $E, F$ be real topological vector spaces, $A : E \to F$ a continuous linear map, $f : E \to [-\infty,+\infty]$ and $g : F \to [-\infty,+\infty]$. The problem $(P)$ is: minimize $f(x) - g(Ax)$ over $x \in E$. For each $z \in F$ the **perturbed problem** obtained by translating the graph of $g$ by $z$ is
--
--   $$
--   (P(z)) \qquad \text{minimize } f(x) - g_z(Ax), \qquad g_z(y) = g(y - z),
--   $$
--
--   so that $(P(0)) = (P)$. Its infimum defines the **perturbation function**
--
--   $$
--   h(z) = \inf (P(z)) = \inf_{x \in E} \{ f(x) - g(Ax - z) \} \in [-\infty, +\infty].
--   $$
--
--   The behaviour of $h$ near $z = 0$ is what "stably set" and Theorem 1 are about.
--
--   **Formalization Note** The infimum is `⨅` in the complete lattice `EReal`, so an empty or unbounded-below infimum is $-\infty$ as in the paper. EReal subtraction is $a + (-b)$; under the standing properness hypotheses ($f > -\infty$, $g < +\infty$) the form $(+\infty) - (+\infty)$ never occurs.
-- source:
--   Rockafellar, Duality and Stability in Extremum Problems Involving Convex Functions, Pacific J. Math. 21 (1967), p. 174, §4, definition of (P(z)) and of h in Lemma 2

import Mathlib

namespace DualityStability.Stability

/-- Rockafellar (1967), §4, p. 174: the perturbed problem `(P(z))` is
"minimize `f(x) − g_z(Ax)`, where `g_z(y) = g(y − z)`", and
`h(z) = inf (P(z)) = inf_x {f(x) − g(Ax − z)}`, an infimum in `[−∞, +∞]`.
`(P(0)) = (P)`, so `h(0) = inf (P)`.

EReal subtraction is `a − b = a + (−b)`; for a proper convex `f` (never `−∞`) and a proper concave
`g` (never `+∞`) the undefined form `+∞ − (+∞)` never occurs. -/
noncomputable def perturbInf {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    (f : E → EReal) (g : F → EReal) (A : E →L[ℝ] F) (z : F) : EReal :=
  ⨅ x : E, f x - g (A x - z)

end DualityStability.Stability


