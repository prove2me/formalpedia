-- Prove2me | Definitions.Def_RamanujanNotebooks_shared_hypPFQ
-- name    : RamanujanNotebooks_shared_hypPFQ
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T21:25:30.625993+00:00
-- url     : https://prove2.me/theorems/1fd1405d-c1fc-4017-8ae6-de4430c8ef8a
-- title:
--   Ramanujan's Notebooks, shared: hypPFQ
-- statement:
--   Generalized hypergeometric series
--   `_pF_q(α_1, …, α_p; β_1, …, β_q; x) = ∑_{k ≥ 0} (α_1)_k ⋯ (α_p)_k / ((β_1)_k ⋯ (β_q)_k) · x^k / k!`
--   (Part III, (0.2), p. 88; Part II, Chapter 10), the upper parameters in the list `num`,
--   the lower ones in `den`.
--
--   Domain (absolute convergence, no vanishing denominator): no lower parameter in
--   `{0, -1, -2, …}`, and
--   * `p ≤ q`: every `x`;
--   * `p = q + 1`: `‖x‖ < 1`; also `‖x‖ = 1` when `Re (∑ β - ∑ α) > 0`;
--   * any `p`, `q`, some upper parameter a nonpositive integer `-n`: the series terminates (a
--     polynomial of degree `≤ n`) and `x` is free; a lower parameter `-m` with `m ≥ n` is then
--     harmless (the terms of index `> n` have numerator `0`).
--   Outside: a non-summable family gives `0` (so for `p = q + 1`, `‖x‖ > 1` this is NOT the
--   analytic continuation; for `‖x‖ = 1` with `-1 < Re (∑ β - ∑ α) ≤ 0`, `x ≠ 1`, the series
--   converges only conditionally and Lean returns `0`: use `Filter.Tendsto` of partial sums);
--   a term with a zero denominator is `0`.
--   Reference: `hypPFQ [] [] x = exp x`, `hypPFQ [a] [] x = (1 - x)^{-a}`.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks.

import Mathlib
import Definitions.Def_RamanujanNotebooks_shared_shiftedFactorial

noncomputable section

namespace RamanujanNotebooks

/-- Generalized hypergeometric series
`_pF_q(α_1, …, α_p; β_1, …, β_q; x) = ∑_{k ≥ 0} (α_1)_k ⋯ (α_p)_k / ((β_1)_k ⋯ (β_q)_k) · x^k / k!`
(Part III, (0.2), p. 88; Part II, Chapter 10), the upper parameters in the list `num`,
the lower ones in `den`.

Domain (absolute convergence, no vanishing denominator): no lower parameter in
`{0, -1, -2, …}`, and
* `p ≤ q`: every `x`;
* `p = q + 1`: `‖x‖ < 1`; also `‖x‖ = 1` when `Re (∑ β - ∑ α) > 0`;
* any `p`, `q`, some upper parameter a nonpositive integer `-n`: the series terminates (a
  polynomial of degree `≤ n`) and `x` is free; a lower parameter `-m` with `m ≥ n` is then
  harmless (the terms of index `> n` have numerator `0`).
Outside: a non-summable family gives `0` (so for `p = q + 1`, `‖x‖ > 1` this is NOT the
analytic continuation; for `‖x‖ = 1` with `-1 < Re (∑ β - ∑ α) ≤ 0`, `x ≠ 1`, the series
converges only conditionally and Lean returns `0`: use `Filter.Tendsto` of partial sums);
a term with a zero denominator is `0`.
Reference: `hypPFQ [] [] x = exp x`, `hypPFQ [a] [] x = (1 - x)^{-a}`. -/
def hypPFQ (num den : List ℂ) (x : ℂ) : ℂ :=
  ∑' k : ℕ, (num.map fun a => shiftedFactorial a k).prod /
    ((den.map fun b => shiftedFactorial b k).prod * (k.factorial : ℂ)) * x ^ k

end RamanujanNotebooks

end


