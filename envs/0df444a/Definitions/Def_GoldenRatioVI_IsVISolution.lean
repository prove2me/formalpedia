-- Prove2me | Definitions.Def_GoldenRatioVI_IsVISolution
-- name    : GoldenRatioVI_IsVISolution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:22:17.213042+00:00
-- url     : https://prove2.me/theorems/6d8496d4-5935-403b-9725-175bed0df01c
-- title:
--   Solution of the variational inequality (1)
-- statement:
--   Let $g:\mathcal E\to(-\infty,+\infty]$ have domain $D$ and let $F:\mathcal E\to\mathcal E$. A point $z^*$ **solves the variational inequality (1)** if $z^*\in D$ and
--   $$\langle F(z^*),\,z-z^*\rangle+g(z)-g(z^*)\ \ge\ 0\qquad\text{for all } z\in D.$$
--   The solution set of (1) is denoted $S$; condition (C1) says $S\neq\emptyset$.
--
--   Problem (1) is equivalent to the monotone inclusion $0\in(F+\partial g)(z^*)$; for $g=\delta_C$ it is the classical variational inequality over $C$.
--
--   **Formalization Note** For $z\notin D$ the left-hand side is $+\infty$, so only $z\in D$ is tested. A solution lies in $D$ because $F$ is defined on $\operatorname{dom} g$ only and $g(z^*)$ must be finite.
-- source:
--   Malitsky, Golden Ratio Algorithms for Variational Inequalities, preprint (2018), §1, p. 1, eq. (1)

import Mathlib

namespace GoldenRatioVI

/-- **A solution of the variational inequality (1).**
Malitsky, *Golden Ratio Algorithms for Variational Inequalities*, preprint (2018), §1, p. 1, eq. (1):
"find z∗ ∈ E s.t. ⟨F(z∗), z − z∗⟩ + g(z) − g(z∗) ≥ 0 ∀z ∈ E".

`IsVISolution D g F zs` says: `zs ∈ D` and `0 ≤ ⟪F zs, z − zs⟫ + g z − g zs` for every `z ∈ D`.
The solution set `S` of (1) is `{zs | IsVISolution D g F zs}`.

**Formalization Note.** The extended-valued `g` is the pair `(D, g)` (`D = dom g`). For `z ∉ D` the
paper's left-hand side is `+∞ ≥ 0`, so only `z ∈ D` carries content. A solution must lie in `D`:
`F(z∗)` is defined only on `dom g` (C3), and `g(z∗) = +∞` would make the left side undefined. -/
def IsVISolution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (D : Set E) (g : E → ℝ) (F : E → E) (zs : E) : Prop :=
  zs ∈ D ∧ ∀ z ∈ D, 0 ≤ inner ℝ (F zs) (z - zs) + g z - g zs

end GoldenRatioVI


