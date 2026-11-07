-- Prove2me | Definitions.Def_GSRandomOrder_acceptProb
-- name    : GSRandomOrder_acceptProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:01:54.580662+00:00
-- url     : https://prove2.me/theorems/535b39d1-b0a3-4929-b3ae-67ea93bee9c8
-- title:
--   Acceptance probability $\alpha_x(A,S,t)$ of the survival algorithm, eq. (9)
-- statement:
--   When item $x$ arrives at real time $t$, with arrived set $S$ and accepted set $A$, the survival algorithm accepts $x$ (in its step 3) with probability
--   $$
--   \alpha_x(A,S,t)=\frac{1}{et}\cdot\frac{\mu^{v/x}_{S,t}(A)}{\mu^{v}_{S,t}(A)},\qquad\text{with }0/0:=0.
--   $$
--   The numerator is the probability of the current accepted set had $x$ been present from the start, and $1/(et)$ is the probability that $x$ would have been early had the arrival times of $S+x$ been reshuffled on $[0,t]$.
--
--   **Formalization Note** Lean's division returns $0$ when the denominator is $0$, which realizes $0/0:=0$. The value is not clamped to $[0,1]$: that it lies in $[0,1]$ is part of Theorem 3.1.
-- source:
--   Paes Leme, Pál, Patel, Gross Substitutes Welfare in Random Order, STOC 2027 submission (manuscript sha256 69787f50…), §3.1, p.9, eq. (9)

import Mathlib
import Definitions.Def_GSRandomOrder_contract
import Definitions.Def_GSRandomOrder_survivalLaw

set_option autoImplicit false

namespace GSRandomOrder

/-- **Acceptance probability** of the survival algorithm (Paes Leme, Pál, Patel, *Gross
Substitutes Welfare in Random Order*, STOC 2027 submission, manuscript sha256 69787f50…, §3.1,
p.9, eq. (9)): when item `x` arrives at real time `t`, with arrived set `S` and accepted set `A`,
`α_x(A, S, t) = (1/(et)) · μ^{v/x}_{S,t}(A) / μ^v_{S,t}(A)`, with `0/0 := 0`.

**Formalization Note.** Lean's division gives `a / 0 = 0` for every `a`, which realizes `0/0 := 0`
(and, at a state with `μ^v_{S,t}(A) = 0`, the comparison inequality makes the numerator `0` as
well). `e` is `Real.exp 1`. No clamping to `[0, 1]` is applied: that `α` lies in `[0, 1]` is a
clause of Theorem 3.1. -/
noncomputable def acceptProb {n : ℕ} (v : Finset (Fin n) → WithBot ℝ) (x : Fin n)
    (A S : Finset (Fin n)) (t : ℝ) : ℝ :=
  1 / (Real.exp 1 * t) * (survivalLaw (contract v x) S t A / survivalLaw v S t A)

end GSRandomOrder


