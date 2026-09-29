-- Prove2me | Definitions.Def_VectorSpaceOpt_support_functional
-- name    : VectorSpaceOpt_support_functional
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-24T15:48:17.05716+00:00
-- url     : https://prove2.me/theorems/8ad95f89-674e-44c6-a043-ed6e2fdc6dc6
-- title:
--   Support functional of a set
-- statement:
--   Let $K$ be a set in a real normed vector space $X$. Its **support functional** is the map on the dual space $X^*$ given by
--
--   $$h(x^*) = \sup_{x \in K}\, \langle x, x^*\rangle .$$
--
--   Geometrically, consider the family of half-spaces $\{x : \langle x, x^*\rangle \le c\}$ as $c$ increases; $h(x^*)$ is the infimum of those $c$ for which $K$ is contained in the half-space. The support functional of a convex set therefore determines the set up to closure, since a closed convex set is the intersection of all closed half-spaces containing it:
--
--   $$K = \bigcap_{x^*}\, \{x : \langle x, x^*\rangle \le h(x^*)\}.$$
--
--   When $K$ is the unit sphere of $X$, its support functional is simply the norm on $X^*$.
--
--   **Formalization Note.** The supremum may be infinite, so the value is taken in the extended reals $\overline{\mathbb{R}} = [-\infty, +\infty]$: it is $+\infty$ for a set unbounded in the direction of $x^*$, and $-\infty$ on the empty set (the supremum of no values). Statements that combine $h$ with real quantities therefore work in the extended reals as well.
-- source:
--   David G. Luenberger, Optimization by Vector Space Methods, John Wiley & Sons, 1969, §5.13, pp. 135–136

import Mathlib

/-- Luenberger §5.13: the *support functional* of a set `K` in a real normed space,
`h(f) = sup_{k ∈ K} ⟨k, f⟩`, valued in `EReal` since the supremum may be `+∞`
(and is `-∞` on the empty set). -/
noncomputable def VectorSpaceOpt_support_functional {X : Type} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (K : Set X) (f : X →L[ℝ] ℝ) : EReal :=
  ⨆ k : K, ((f k : ℝ) : EReal)


