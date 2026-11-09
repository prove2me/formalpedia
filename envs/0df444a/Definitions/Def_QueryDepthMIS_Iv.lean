-- Prove2me | Definitions.Def_QueryDepthMIS_Iv
-- name    : QueryDepthMIS_Iv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:25:48.50779+00:00
-- url     : https://prove2.me/theorems/1b4fffc8-60ec-414c-a43c-e7d00cc24c36
-- title:
--   Geometric intervals $I_i = [(1+\alpha)^{i-1}, (1+\alpha)^i) \cap \{1, \dots, n\}$
-- statement:
--   For $\alpha > 0$ the positions $\{1, \dots, n\}$ are divided into the geometrically growing intervals
--   $$
--   I_i = [(1 + \alpha)^{i-1}, (1 + \alpha)^{i}) \cap \{1, \dots, n\}, \qquad 1 \le i \le b .
--   $$
--   **Formalization Note** The same formula gives $I_0 = \emptyset$, which occurs only as $I_{i-1}$ for $i = 1$.
-- source:
--   Mitrović–Sheu, Tight Query Depth of Recursive Randomized Greedy MIS, STOC 2027 submission (manuscript sha256 805e76d8…), §3.4, p.14

import Mathlib

set_option autoImplicit false

namespace QueryDepthMIS

/-- The geometric intervals of positions (Mitrović–Sheu, *Tight Query Depth of Recursive Randomized Greedy MIS*, STOC 2027 submission (manuscript sha256 805e76d8…), §3.4, p.14): "Divide {1, 2, …, n} into
I₁, I₂, …, I_b, where b = 1 + ⌊log_{1+α} n⌋ and I_i = [(1 + α)^{i−1}, (1 + α)^i) ∩ {1, …, n}
(1 ≤ i ≤ b)."

`Iv α n i = {x ∈ {1, …, n} : (1 + α)^{i−1} ≤ x < (1 + α)^i}`.

**Formalization Note** For `i = 0` the formula (with natural subtraction, `0 − 1 = 0`) gives the
empty set; `I₀` occurs only as `I_{i−1}` for `i = 1`. -/
noncomputable def Iv (α : ℝ) (n i : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 n).filter
    (fun x => (1 + α) ^ (i - 1) ≤ (x : ℝ) ∧ (x : ℝ) < (1 + α) ^ i)

end QueryDepthMIS


