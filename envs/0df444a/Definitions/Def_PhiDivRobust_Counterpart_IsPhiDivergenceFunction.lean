-- Prove2me | Definitions.Def_PhiDivRobust_Counterpart_IsPhiDivergenceFunction
-- name    : PhiDivRobust_Counterpart_IsPhiDivergenceFunction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T18:45:52.700978+00:00
-- url     : https://prove2.me/theorems/baa5b569-105b-4a1b-a7ed-1f0998c91556
-- title:
--   φ-divergence function: convex on [0, ∞), φ(1) = 0, finite on (0, ∞), possibly +∞ at 0
-- statement:
--   A **φ-divergence function** is a function $\phi:\mathbb R\to\mathbb R\cup\{\pm\infty\}$ with the following properties:
--
--   1. $\phi(t) > -\infty$ for every $t$;
--   2. $\phi(t) < +\infty$ for every $t > 0$;
--   3. $\phi(1) = 0$;
--   4. $\phi$ is convex on $[0,\infty)$: for all $t, u \ge 0$ and $\theta\in[0,1]$,
--
--   $$\phi(\theta t + (1-\theta)u) \le \theta\,\phi(t) + (1-\theta)\,\phi(u).$$
--
--   The value $\phi(0)$ may be finite (Kullback–Leibler, $\phi(t) = t\log t - t + 1$) or $+\infty$ (Burg entropy, $\chi^2$-distance, $J$-divergence, whose effective domain is $(0,\infty)$). Values of $\phi$ at negative arguments play no role.
--
--   This is the class of functions for which the φ-divergence $I_\phi(p,q)=\sum_i q_i\phi(p_i/q_i)$ and the conjugate $\phi^*$ are used throughout the mission; every example of Table 2 of the paper belongs to it.
--
--   **Formalization Note** $\phi$ takes values in `EReal`. Convexity is written out pointwise because Mathlib's `ConvexOn` needs a module codomain; since $\phi\ne-\infty$, no $-\infty+\infty$ arises, and `EReal`'s convention $0\cdot(+\infty)=0$ makes the endpoints $\theta\in\{0,1\}$ harmless. Finiteness on $(0,\infty)$ is the paper's "convex for $t\ge0$" read together with its footnote 2 (dom $\phi = (0,\infty)$ for the examples of Table 4).
-- source:
--   Ben-Tal, den Hertog, De Waegenaere, Melenberg, Rennen, Robust Solutions of Optimization Problems Affected by Uncertain Probabilities, Management Sci. 59(2), 2013, p. 343, sentence after Eq. (2); p. 344, Table 2 note and footnote 2

import Mathlib
open Matrix

namespace PhiDivRobust.Counterpart

/-- A φ-divergence function (Ben-Tal et al. 2013, p. 343, the sentence after Eq. (2); Table 2 note and
footnote 2, p. 344). `φ : ℝ → EReal` is never `-∞`, is finite on `(0, ∞)`, satisfies `φ(1) = 0`, and is
convex on `[0, ∞)` (convexity written out in `EReal`, since `ConvexOn` needs a module codomain).
The value `φ 0` may be `+∞` (Burg, χ², J divergences); values at `t < 0` are unconstrained and never
used. -/
structure IsPhiDivergenceFunction (φ : ℝ → EReal) : Prop where
  ne_bot : ∀ t, φ t ≠ ⊥
  ne_top_of_pos : ∀ t, 0 < t → φ t ≠ ⊤
  map_one : φ 1 = 0
  convex : ∀ t u θ : ℝ, 0 ≤ t → 0 ≤ u → 0 ≤ θ → θ ≤ 1 →
    φ (θ * t + (1 - θ) * u) ≤ (θ : EReal) * φ t + ((1 - θ : ℝ) : EReal) * φ u

end PhiDivRobust.Counterpart


