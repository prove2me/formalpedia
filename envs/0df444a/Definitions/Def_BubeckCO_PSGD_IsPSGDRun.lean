-- Prove2me | Definitions.Def_BubeckCO_PSGD_IsPSGDRun
-- name    : BubeckCO_PSGD_IsPSGDRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:25:35.810445+00:00
-- url     : https://prove2.me/theorems/fb7eb03e-9860-4674-9a7d-14410f1980c3
-- title:
--   A run of projected subgradient descent (3.2)–(3.3)
-- statement:
--   Let $X \subseteq \mathbb{R}^n$, $f : X \to \mathbb{R}$, a step size $\eta$ and a horizon $t \in \mathbb{N}$. Sequences $x_1, x_2, \dots$ and $g_1, g_2, \dots$ in $\mathbb{R}^n$ form a **run of projected subgradient descent for $t$ steps** if, for every $s = 1, \dots, t$,
--
--   1. $g_s \in \partial f(x_s)$ is a subgradient of $f$ at $x_s \in X$ in the sense of Definition 1.2;
--   2. with $y_{s+1} = x_s - \eta g_s$ (equation (3.2)), the next iterate is its projection
--   $$
--   x_{s+1} = \Pi_X(y_{s+1}) = \operatorname{argmin}_{y \in X} \|y_{s+1} - y\| \qquad \text{(equation (3.3))}.
--   $$
--
--   The subgradients $g_s$ are arbitrary elements of $\partial f(x_s)$, i.e. whatever a first-order oracle returns. This predicate is the object about which Theorem 3.2 and the bounds in its proof are stated.
--
--   **Formalization Note** Indices are 1-based: $x_1$ is the starting point, and $x_0$, $g_0$ and the values beyond the horizon are unconstrained. $y_{s+1}$ is inlined as $x_s - \eta g_s$. The book's run is infinite; constraining only steps $1, \dots, t$ loses nothing, since every finite run extends to an infinite one. The standing assumptions on $X$, $f$ and $\eta > 0$ are hypotheses of the theorems about runs, not part of this predicate.
-- source:
--   Bubeck, Convex Optimization: Algorithms and Complexity, Found. Trends Mach. Learn. 8(3-4), 2015, p. 264 (PDF p. 37), equations (3.2)–(3.3) (projected subgradient descent)

import Mathlib
import Definitions.Def_BubeckCO_PSGD_IsSubgradient
import Definitions.Def_BubeckCO_PSGD_IsEuclideanProj

namespace BubeckCO.PSGD

/-- **A run of projected subgradient descent ((3.2)–(3.3)) for `t` steps.**
Bubeck, Convex Optimization: Algorithms and Complexity, Found. Trends Mach. Learn. 8(3-4), 2015,
p. 264 (PDF p. 37), equations (3.2)–(3.3): "the projected subgradient descent algorithm which
iterates the following equations for `t ≥ 1`:
`y_{t+1} = x_t − η g_t`, where `g_t ∈ ∂f(x_t)`, (3.2)
`x_{t+1} = Π_X(y_{t+1})`. (3.3)"

`IsPSGDRun X f η x g t` says that for every step `s` with `1 ≤ s ≤ t`, `g s` is a subgradient of
`f` at `x s` relative to `X` (Definition 1.2; this includes `x s ∈ X`) and `x (s + 1)` is the
Euclidean projection onto `X` of `y_{s+1} = x s − η • g s`.

**Formalization Note.** Indices are 1-based: `x 1` is the starting point, and `x 0`, `g 0` and the
values beyond the horizon (`x s` for `s > t + 1`, `g s` for `s > t`) are unconstrained. The
intermediate point `y_{s+1}` of (3.2) is inlined as `x s − η • g s`. `g` is an arbitrary
sequence of subgradients, i.e. whatever the first-order oracle returns (p. 238). The book's run is
infinite; restricting to steps `1, …, t` loses nothing for statements about `x_1, …, x_{t+1}`,
since every finite run extends to an infinite one. The standing conditions on `X`, `f` and
`η > 0` are hypotheses of the theorems about runs, not part of this predicate. -/
def IsPSGDRun {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (η : ℝ) (x g : ℕ → EuclideanSpace ℝ (Fin n))
    (t : ℕ) : Prop :=
  ∀ s, 1 ≤ s → s ≤ t →
    IsSubgradient X f (x s) (g s) ∧ IsEuclideanProj X (x s - η • g s) (x (s + 1))

end BubeckCO.PSGD


