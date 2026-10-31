-- Prove2me | Definitions.Def_TensorAHPE_IsProperClosedConvex
-- name    : TensorAHPE_IsProperClosedConvex
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:25:18.016989+00:00
-- url     : https://prove2.me/theorems/96fe639e-ad45-4fbf-8bfd-abc584acac99
-- title:
--   Proper closed convex function $h:\mathbb R^n\to(-\infty,+\infty]$
-- statement:
--   A function $h : E \to [-\infty,+\infty]$ on a real normed space $E$ is **proper closed convex** if
--
--   1. $h(x) > -\infty$ for every $x$, and $h(x) < +\infty$ for at least one $x$ (proper);
--   2. $h$ is lower semicontinuous (closed);
--   3. its epigraph $\{(x,t) \in E\times\mathbb R : h(x) \le t\}$ is a convex set (convex).
--
--   This is the class of the nonsmooth term $h$ in the composite problem $\min_x f(x)+h(x)$ of the paper; $h$ may take the value $+\infty$, so constraints $x \in X$ are covered through indicator functions.
--
--   **Formalization Note** The function is valued in `EReal`. Closedness is lower semicontinuity of the extended-real function; convexity is convexity of the epigraph in $E\times\mathbb R$.
-- source:
--   Jiang, Wang & Zhang, An Optimal High-Order Tensor Method for Convex Optimization, arXiv:1812.06557v3, Eq. (1.1), p.2 ("h is convex but possibly non-smooth") and §2, p.6 ("a proper closed convex function h")

import Mathlib

namespace TensorAHPE

/-- **Proper closed convex extended-real function.**
Jiang, Wang & Zhang, *An Optimal High-Order Tensor Method for Convex Optimization*,
arXiv:1812.06557v3, Eq. (1.1), p.2 ("h is convex but possibly non-smooth") and §2, p.6
("a proper closed convex function h").

`IsProperClosedConvex h` says: `h` never takes the value `−∞`, `h` is not identically `+∞`,
`h` is lower semicontinuous (closed), and the epigraph `{(x, t) : h x ≤ t}` is convex.

**Formalization Note.** The function is valued in `EReal`, so `h` may take the value `+∞` (an
indicator of a convex set, for instance). "Closed" is lower semicontinuity of `h : E → EReal`,
equivalently closedness of its epigraph. Convexity of an extended-real function is convexity of
its epigraph in `E × ℝ`. -/
def IsProperClosedConvex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : E → EReal) : Prop :=
  (∀ x, h x ≠ ⊥) ∧ (∃ x, h x ≠ ⊤) ∧ LowerSemicontinuous h ∧
    Convex ℝ {p : E × ℝ | h p.1 ≤ (p.2 : EReal)}

end TensorAHPE


