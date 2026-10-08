-- Prove2me | Definitions.Def_GilmoreGomory61_CuttingStock_Knapsack
-- name    : GilmoreGomory61_CuttingStock_Knapsack
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T07:54:27.112826+00:00
-- url     : https://prove2.me/theorems/2e0f14f0-e27c-4e39-a0f4-18fe7d2f62a4
-- title:
--   p. 853 — extended-real knapsack value F_s(x)
-- statement:
--   For multipliers $b_i$, the **knapsack value** $F_s(x)$ is the supremum of the prices of patterns using only the first $s$ piece lengths and fitting available length $x$:
--
--   $$
--   F_s(x)=\sup\left\{\sum_{i<s}b_i a_i:\ a_i\in\mathbb N,\ \sum_{i<s}\ell_i a_i\le x\right\}.
--   $$
--
--   This is the quantity computed by the dynamic programming recursion before a new cutting column is selected.
--
--   **Formalization Note** The value lies in the extended reals, so an empty feasible pattern set has value $-\infty$. Patterns are full finite vectors with coordinates at and after $s$ set to zero. The later maximum and recursion theorems assume positive lengths where needed.
-- source:
--   Gilmore and Gomory, A linear programming approach to the cutting-stock problem, Oper. Res. 9(6) (1961), p. 853, definition of F_s(x)

import Mathlib
import Definitions.Def_GilmoreGomory61_CuttingStock_Model

namespace GilmoreGomory61.CuttingStock

/-- The extended-real knapsack value Fₛ(x), p. 853. It is bottom if no pattern fits. -/
noncomputable def knapF {m k : ℕ} (I : Instance m k) (b : Fin m → ℝ)
    (s : ℕ) (x : ℝ) : EReal :=
  ⨆ (a : Fin m → ℕ) (_ : (∀ i : Fin m, s ≤ i.val → a i = 0) ∧ patLen I a ≤ x),
    ((∑ i, b i * (a i : ℝ) : ℝ) : EReal)

end GilmoreGomory61.CuttingStock


