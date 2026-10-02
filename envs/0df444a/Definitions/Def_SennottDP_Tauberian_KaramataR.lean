-- Prove2me | Definitions.Def_SennottDP_Tauberian_KaramataR
-- name    : SennottDP_Tauberian_KaramataR
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T12:51:03.805326+00:00
-- url     : https://prove2.me/theorems/c2a79505-3cf2-4d60-a6c8-97bf59059f9c
-- title:
--   The jump function r of Fig. A.1: r(x) = 1/x for x ≥ 1/e, 0 below
-- statement:
--   The function $r$ of Fig. A.1 is
--   $$r(x) = \begin{cases} 0, & x < e^{-1},\\ 1/x, & x \ge e^{-1}. \end{cases}$$
--   It has a jump discontinuity at $e^{-1}$, where it takes the value $r(e^{-1}) = e$. It is used on the interval $(0,1)$.
--
--   It is the test function in Karamata's proof of the Tauberian theorem: for $\alpha \in (0,1)$, $\alpha^n r(\alpha^n)$ equals $1$ when $\alpha^n \ge e^{-1}$ and $0$ otherwise, so it cuts a power series down to a partial sum.
--
--   **Formalization Note** `r : ℝ → ℝ` is defined on all of `ℝ` by the same rule; only its values on `(0,1)` and its integral over `[0,1]` are used.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), pp. 280–281, Section A.4, Fig. A.1 and (A.26); p. 285, (A.40)

import Mathlib

namespace SennottDP.Tauberian

/-- Sennott (1999), §A.4, pp. 280–281, Fig. A.1: the function `r` with a jump at `e^{-1}`:
`r(α) = 0` for `α < e^{-1}` and `r(α) = 1/α` for `α ≥ e^{-1}` (the book uses it on `(0, 1)`).
The value at the jump is `r(e^{-1}) = e`, as in Fig. A.1 and in (A.40), where
`α^n ≥ e^{-1}` is the condition for `r(α^n) = α^{-n}`. -/
noncomputable def r (x : ℝ) : ℝ :=
  if Real.exp (-1) ≤ x then x⁻¹ else 0

end SennottDP.Tauberian


