-- Prove2me | Definitions.Def_HighDimProb_DvoretzkyMilman_StableDimension
-- name    : HighDimProb_DvoretzkyMilman_StableDimension
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:13:02.583768+00:00
-- url     : https://prove2.me/theorems/601a87eb-3a33-4f7f-ae57-c92d84b592d3
-- title:
--   The stable dimension $d(T)$ of a bounded subset of $\mathbb R^n$
-- statement:
--   The **stable dimension** $d(T) := w^2/\mathrm{diam}^2$ of a bounded set $T\subseteq\mathbb
--   R^n$, given its Gaussian width $w$ and diameter $\mathrm{diam}$ — a robust, real-valued
--   substitute for the linear-algebraic dimension of $T$, and the quantity the goal theorem's
--   measurement-count hypothesis $m\le c\varepsilon^2d(T)$ is stated in terms of.
--
--   **Formalization Note** The book's own Definition 7.6.2 defines $d(T)$ via
--   $h(T-T)^2/\mathrm{diam}(T)^2$, where $h(T)^2 := \mathbb E\sup_{t\in T}\langle g,t\rangle^2$ is
--   a squared variant of Gaussian width, and states $d(T) \asymp w(T)^2/\mathrm{diam}(T)^2$ (equal
--   up to an absolute constant, by the book's own Exercise 7.6.1) rather than literal equality.
--   This mission formalizes $d(T)$ directly as the $w$-based right-hand quantity of that
--   equivalence, since the goal theorem's own proof uses only the inequality direction
--   $d(T)\le Cw(T)^2/\mathrm{diam}(T)^2$ and the goal's hypothesis already carries an unpinned
--   absolute constant $c$ that absorbs the equivalence constants — see
--   `Def_HighDimProb_DvoretzkyMilman_StableDimension.lean` and `MODERATION_NOTES.md` for the full
--   reasoning.
-- source:
--   Vershynin, High-Dimensional Probability (2018), p. 179, Definition 7.6.2

import Mathlib

namespace HighDimProb.DvoretzkyMilman

/-- The **stable dimension** `d(T)` of a bounded set `T ⊆ ℝⁿ`, given its Gaussian width `w` and
diameter `diam`, as `w²/diam²`. Vershynin, *High-Dimensional Probability* (2018), Definition
7.6.2, p. 179 (PDF p. 187): "the stable dimension of `T` is defined as `d(T) := h(T-T)²/diam(T)² ≍
w(T)²/diam(T)²`," where `h(T)² := E sup_{t∈T}⟨g,t⟩²` is a squared variant of Gaussian width the
book shows (Exercise 7.6.1) is equivalent to `w(T)` up to an absolute constant factor, and `≍`
denotes that equivalence-up-to-constants, not equality.

**Formalization Note** This chunk formalizes `d(T)` directly as `w(T)²/diam(T)²` — the
right-hand, `w`-based quantity of the book's own `≍` — rather than building a fourth,
near-duplicate "expected supremum of squared inner products" definition (`h(T)`) solely to divide
it by `diam(T)²` again. Theorem 11.3.3's own proof uses only the inequality direction `d(T) ≤
Cw(T)²/diam(T)²` (via Definition 7.6.2's `≍`, "provided the absolute constant `c` is chosen
sufficiently small"), never the literal value of `h(T-T)`; since the goal's own hypothesis
`m ≤ cε²d(T)` carries an unpinned absolute constant `c`, substituting the boundedly-equivalent
`w`-based quantity for the `h`-based one, absorbing the equivalence constants of Exercise 7.6.1
into `c`, preserves the theorem's truth content exactly rather than approximating it. Recorded as
a formalization decision in `MODERATION_NOTES.md`, not a silent substitution. -/
noncomputable def stableDimension (w diam : ℝ) : ℝ :=
  w ^ 2 / diam ^ 2

end HighDimProb.DvoretzkyMilman


