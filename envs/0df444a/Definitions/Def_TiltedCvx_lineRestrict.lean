-- Prove2me | Definitions.Def_TiltedCvx_lineRestrict
-- name    : TiltedCvx_lineRestrict
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:39:17.619772+00:00
-- url     : https://prove2.me/theorems/3c973320-cafa-430e-a753-72cee2c381e6
-- title:
--   Restriction of $f$ to a line or an interval of a line
-- statement:
--   Let $\ell=\{x+te : t\in\mathbb R\}$ be a line with $\|e\|=1$ and $I\subseteq\mathbb R$. The restriction of $f$ to the part $\{x+te : t\in I\}$ of $\ell$, regarded as a function on the one-dimensional Euclidean space $\mathbb R$ and extended by $+\infty$, is
--
--   $$
--   t\mapsto\begin{cases} f(x+te), & t\in I,\\ +\infty, & t\notin I.\end{cases}
--   $$
--
--   For $I=\mathbb R$ this is $f|_\ell$.
--
--   **Formalization Note** The unit-speed parametrization $t\mapsto x+te$ is an isometry of $\mathbb R$ onto $\ell$ (proof of Corollary 2, p.21), so it identifies $\ell$ with $\mathbb R$ as Euclidean spaces.
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Theorems 9 and 16, pp.20, 24; proof of Corollary 2, p.21

import Mathlib

namespace TiltedCvx

open Classical in
/-- **Restriction of `f` to (an interval of) a line.** Pedramfar–Khanna–Quinn–Aggarwal,
arXiv:2611.03472, Theorems 9 and 16, pp.20, 24, and the proof of Corollary 2, p.21: the
restriction `f|ℓ` of `f` to the line `ℓ = {x + t e : t ∈ ℝ}`, "regarded as a one-dimensional
Euclidean space", and the restriction to an interval `I` of `ℓ`, extended by `+∞`.

**Formalization Note** The line is parametrized at unit speed (`‖e‖ = 1` in every use), as in the
proof of Corollary 2: `t ↦ x + t e` is an isometry of `ℝ` onto `ℓ`, so `ℓ` with its Euclidean
structure is identified with `ℝ`. Points of `ℝ` outside `I` get `+∞`; `I = Set.univ` gives
`f|ℓ`. -/
noncomputable def lineRestrict {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → EReal) (x e : E) (I : Set ℝ) : ℝ → EReal :=
  fun t => if t ∈ I then f (x + t • e) else ⊤

end TiltedCvx


