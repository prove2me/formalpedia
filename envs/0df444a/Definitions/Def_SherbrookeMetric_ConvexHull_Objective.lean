-- Prove2me | Definitions.Def_SherbrookeMetric_ConvexHull_Objective
-- name    : SherbrookeMetric_ConvexHull_Objective
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:48:42.177371+00:00
-- url     : https://prove2.me/theorems/1b90bbea-370e-4385-9ccb-c9719a2aa2af
-- title:
--   Equation (11) — separable cost of an item allocation
-- statement:
--   For finitely many items $i$, choose a nonnegative integer stock level $m_i$, a real unit cost $c_i$, and an item function $\Xi_i$ on stock levels. The **original allocation objective** is
--
--   $$
--   J(m)=\sum_i\bigl(c_i m_i+\Xi_i(m_i)\bigr).
--   $$
--
--   This is equation (11), evaluated with the original item functions. Its separable form lets the Appendix derive an allocation rule item by item.
--
--   **Formalization Note** The finite item type may be empty; its sum is then zero. The goal theorem separately assumes each present item's cost is positive and its function is nonincreasing and bounded below.
-- source:
--   Sherbrooke, METRIC: A Multi-Echelon Technique for Recoverable Item Control, Oper. Res. 16 (1968), p. 140, Appendix, Eq. (11); DOI 10.1287/opre.16.1.122

import Mathlib

namespace SherbrookeMetric.ConvexHull

/-- Equation (11), p. 140: the cost of a vector of integer stock levels,
evaluated with the original item functions. -/
def objective {ι : Type*} [Fintype ι] (c : ι → ℝ) (Ξ : ι → ℕ → ℝ)
    (m : ι → ℕ) : ℝ :=
  ∑ i : ι, (c i * (m i : ℝ) + Ξ i (m i))

end SherbrookeMetric.ConvexHull


