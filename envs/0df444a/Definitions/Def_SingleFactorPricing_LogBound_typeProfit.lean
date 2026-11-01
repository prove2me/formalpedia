-- Prove2me | Definitions.Def_SingleFactorPricing_LogBound_typeProfit
-- name    : SingleFactorPricing_LogBound_typeProfit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:14:57.182097+00:00
-- url     : https://prove2.me/theorems/e14de477-d556-4272-a64c-2d0cf24e5212
-- title:
--   Type profit $R_j(p)$
-- statement:
--   For a customer type $t$ with demands $d_{t,i}(p)$, $i\in N$, at the price vector $p$, the **type profit** is
--
--   $$
--   R_t(p)=\sum_{i\in N}p_i\,d_{t,i}(p).
--   $$
--
--   It is the profit the firm earns from a unit mass of type $t$ customers, and the object each personalized price vector maximizes.
--
--   **Formalization Note** The demand is a function `d : T → (N → ℝ) → N → ℝ`. There is no cost vector, because footnote 1 of the paper removes costs by the change of variables $p\leftarrow p-c$.
-- source:
--   Gallego, Berbeglia, Bounds and Heuristics for Multi-Product Personalized Pricing, arXiv:2102.03038v2, §2, p.2

import Mathlib

open MeasureTheory

namespace SingleFactorPricing.LogBound

/-- **Type profit** `R_j(p)`. Gallego, Berbeglia, arXiv:2102.03038v2, §2, p.2:
"The profit function for type j customers is given by `R_j(p) := ∑_{i∈N} p_i d_ij(p)`."

**Formalization Note.** `d t p i` is the demand for product `i` of customer type `t` at the price
vector `p`. `N` is the finite set of products and `T` the type space. There is no cost vector:
footnote 1, p.2 removes costs by a change of variables. -/
noncomputable def typeProfit {N T : Type*} [Fintype N] (d : T → (N → ℝ) → N → ℝ) (t : T)
    (p : N → ℝ) : ℝ :=
  ∑ i, p i * d t p i

end SingleFactorPricing.LogBound


