-- Prove2me | Definitions.Def_ToddKK14_Diameter_Bound
-- name    : ToddKK14_Diameter_Bound
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T01:44:19.32001+00:00
-- url     : https://prove2.me/theorems/a771abc0-f666-438d-8ce6-7f50d1c9b20d
-- title:
--   p. 2 — the bound ⌊(n − d)^{log₂ d}⌋ of Theorem 1
-- statement:
--   For natural numbers $d$ and $n$, the **Todd bound** is the natural number
--
--   $$
--   \operatorname{toddBound}(d,n) \;=\; \big\lfloor (n-d)^{\log_2 d} \big\rfloor ,
--   $$
--
--   where $n-d$ is the real difference, $\log_2$ is the logarithm to base 2 (the paper fixes this base: "All logarithms are to base 2"), and the power is the real power $x^y$.
--
--   This is the right-hand side of Todd's Theorem 1, $\Delta(d,n)\le (n-d)^{\log d}$. Graph distances are natural numbers, so a distance is at most $(n-d)^{\log_2 d}$ exactly when it is at most the floor. Sample values: $\operatorname{toddBound}(1,2)=1$, $\operatorname{toddBound}(2,7)=5$, $\operatorname{toddBound}(4,8)=16$, $\operatorname{toddBound}(d,d)=0$ for $d\ge 2$.
--
--   **Formalization Note** The real power is `Real.rpow`, for which $0^0=1$; hence $\operatorname{toddBound}(1,1)=1$, and the paper's separate clause $\Delta(1,1)=0$ is stated separately in the goal theorem. `Real.logb 2 0 = 0` is a junk value, but at $d \ge 1$ the exponent $\log_2 d$ is a genuine logarithm.
-- source:
--   Todd, An improved Kalai-Kleitman bound for the diameter of a polyhedron, arXiv:1402.3579v2, p. 2, Theorem 1 and the remark after it

import Mathlib

namespace ToddKK14.Diameter

/-- Todd (2014), p. 2, Theorem 1: the bound `(n - d) ^ (log₂ d)` ("All logarithms are to base 2"),
as a natural number. Graph distances are natural numbers, so a distance is at most
`(n - d) ^ (log₂ d)` exactly when it is at most the floor `⌊(n - d) ^ (log₂ d)⌋`. The subtraction
`n - d` is taken in `ℝ` and the power is the real power `Real.rpow`. -/
noncomputable def toddBound (d n : ℕ) : ℕ := ⌊((n : ℝ) - d) ^ Real.logb 2 d⌋₊

end ToddKK14.Diameter


