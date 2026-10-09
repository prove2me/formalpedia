-- Prove2me | Definitions.Def_RamanujanNotebooks_shared_hypPFQTerm
-- name    : RamanujanNotebooks_shared_hypPFQTerm
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T00:49:22.035696+00:00
-- url     : https://prove2.me/theorems/e2305fae-3f8c-4110-9f2f-0c892ca5efa6
-- title:
--   Ramanujan's Notebooks, shared: hypPFQTerm
-- statement:
--   `k`-th term `(α_1)_k ⋯ (α_p)_k / ((β_1)_k ⋯ (β_q)_k k!) · x^k` of the generalized
--   hypergeometric series `_pF_q(α_1, …, α_p; β_1, …, β_q; x)` of Part II, (0.1), p. 8; the upper
--   parameters are in the list `num`, the lower ones in `den`.  It is the summand of the shared
--   `hypPFQ`.
--   Only the term is defined: a chapter states the value of a series by `HasSum` (absolute
--   convergence), by `Filter.Tendsto` of the partial sums (argument `-1`, conditional convergence),
--   or as a finite sum (terminating series).
--   Junk: if a lower parameter is `0` or a negative integer `-m`, the denominator vanishes for
--   `k > m` and Lean returns `0` for those terms; this is not a hypergeometric term, so every use
--   must exclude it for the indices that occur.
--   Reference: `hypPFQTerm [1/2, 1/2] [1] 1 2 = 9/64`, `hypPFQTerm [] [] x k = x^k / k!`.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks.

import Mathlib
import Definitions.Def_RamanujanNotebooks_shared_shiftedFactorial

namespace RamanujanNotebooks

/-- `k`-th term `(α_1)_k ⋯ (α_p)_k / ((β_1)_k ⋯ (β_q)_k k!) · x^k` of the generalized
hypergeometric series `_pF_q(α_1, …, α_p; β_1, …, β_q; x)` of Part II, (0.1), p. 8; the upper
parameters are in the list `num`, the lower ones in `den`.  It is the summand of the shared
`hypPFQ`.
Only the term is defined: a chapter states the value of a series by `HasSum` (absolute
convergence), by `Filter.Tendsto` of the partial sums (argument `-1`, conditional convergence),
or as a finite sum (terminating series).
Junk: if a lower parameter is `0` or a negative integer `-m`, the denominator vanishes for
`k > m` and Lean returns `0` for those terms; this is not a hypergeometric term, so every use
must exclude it for the indices that occur.
Reference: `hypPFQTerm [1/2, 1/2] [1] 1 2 = 9/64`, `hypPFQTerm [] [] x k = x^k / k!`. -/
noncomputable def hypPFQTerm (num den : List ℂ) (x : ℂ) (k : ℕ) : ℂ :=
  (num.map fun a => shiftedFactorial a k).prod /
    ((den.map fun b => shiftedFactorial b k).prod * (k.factorial : ℂ)) * x ^ k

end RamanujanNotebooks


