-- Prove2me | Definitions.Def_ConstrSOSP_gridArrow
-- name    : ConstrSOSP_gridArrow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:02:56.062288+00:00
-- url     : https://prove2.me/theorems/06223275-ec0e-4c5b-be71-b710996a882f
-- title:
--   Arrow at a grid point (table of $\nabla f(a,b)$)
-- statement:
--   The prescribed arrow at the grid point $(a,b)$, transcribed from the table of $\nabla f(a,b)$ on p.31: Up on the lower green boundary, the blue columns (with bases and solution tops) and the blue corridors; Left on the black corridor and the right green boundary; Down on the upper orange boundary, the red column near the green boundary, the red columns above solution columns and the point $(6k-5,3)$ for $k\in$ Columns, $k>1$; Right elsewhere.
--
--   **Formalization Note** Integer coordinates; cases tested in the page's order.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), p.31

import Mathlib
import Definitions.Def_ConstrSOSP_Dir
import Definitions.Def_ConstrSOSP_InColumns
import Definitions.Def_ConstrSOSP_InSolutions

namespace ConstrSOSP

open Classical in
/-- **The arrow (prescribed gradient) at a grid point** (arXiv:2604.02285, 2 Nov 2026, the table
of `∇f(a, b)` on the grid, p.31), for an Iter circuit `C` with `n` inputs:
* **Up** for `2 ≤ a ≤ 6·2ⁿ + 6`, `0 ≤ b ≤ 1` (green lower boundary); `6k − 2 ≤ a ≤ 6k − 1`,
  `2 ≤ b ≤ 6k + 1`, `k ∈ Columns` (blue column with its base); `6k − 2 ≤ a ≤ 6k − 1`,
  `b = 6k + 2`, `k ∈ Solutions` (top of a solution column); `6k ≤ a ≤ 6k + 2`, `b = 6k + 1`,
  `k ∈ [2ⁿ]`, `C(k) > k`, `C(k) ∈ Columns` (start of a blue corridor); `6k + 1 ≤ a ≤ 6k + 2`,
  `b = 6l + 1`, `k ∈ [2ⁿ]`, `l ∈ Columns`, `C(l) ∈ Columns`, `C(l) > k > l`;
  `6k − 3 ≤ a ≤ 6k + 2`, `b = 6l + 1`, `k ∈ [2ⁿ] ∖ Columns`, `l ∈ Columns`, `C(l) ∈ Columns`,
  `C(l) > k > l`; `a = 6k − 3`, `b = 6l + 1`, `k ∈ Columns`, `l ∈ [2ⁿ]`, `C(l) ∈ Columns`,
  `C(l) ≥ k > l` (blue corridor entering a blue column at a crossing);
* **Left** for `6k ≤ a ≤ 6k + 1`, `b = 2`, `k ∈ Columns`; `6k − 4 ≤ a ≤ 6k + 1`, `b = 2`,
  `k ∈ [2ⁿ] ∖ Columns`; `6·2ⁿ + 2 ≤ a ≤ 6·2ⁿ + 4`, `b = 2`; `6·2ⁿ + 5 ≤ a ≤ 6·2ⁿ + 6`,
  `2 ≤ b ≤ 6·2ⁿ + 4` (green right boundary);
* **Down** for `2 ≤ a ≤ 6·2ⁿ + 6`, `6·2ⁿ + 5 ≤ b ≤ 6·2ⁿ + 6` (orange upper boundary);
  `a = 6·2ⁿ + 4`, `3 ≤ b ≤ 6·2ⁿ + 4` (red column near the green boundary); `6k − 2 ≤ a ≤ 6k − 1`,
  `6k + 3 ≤ b ≤ 6·2ⁿ + 4`, `k ∈ Solutions` (red column above a solution column); `a = 6k − 5`,
  `b = 3`, `k ∈ Columns`, `k > 1`;
* **Right** elsewhere.

**Formalization Note** Coordinates are integers; the cases are tested in the order of the page.
The gradient each arrow stands for is `dirGrad`. -/
noncomputable def gridArrow (C : Circuit) (a b : ℤ) : Dir :=
  if (2 ≤ a ∧ a ≤ (6 * 2 ^ C.n + 6 : ℤ) ∧ 0 ≤ b ∧ b ≤ 1) ∨
      (∃ k : ℕ, InColumns C k ∧ (6 * k - 2 : ℤ) ≤ a ∧ a ≤ (6 * k - 1 : ℤ) ∧ 2 ≤ b ∧
        b ≤ (6 * k + 1 : ℤ)) ∨
      (∃ k : ℕ, InSolutions C k ∧ (6 * k - 2 : ℤ) ≤ a ∧ a ≤ (6 * k - 1 : ℤ) ∧
        b = (6 * k + 2 : ℤ)) ∨
      (∃ k : ℕ, 1 ≤ k ∧ k ≤ 2 ^ C.n ∧ k < C.app k ∧ InColumns C (C.app k) ∧
        (6 * k : ℤ) ≤ a ∧ a ≤ (6 * k + 2 : ℤ) ∧ b = (6 * k + 1 : ℤ)) ∨
      (∃ k l : ℕ, 1 ≤ k ∧ k ≤ 2 ^ C.n ∧ InColumns C l ∧ InColumns C (C.app l) ∧
        k < C.app l ∧ l < k ∧ (6 * k + 1 : ℤ) ≤ a ∧ a ≤ (6 * k + 2 : ℤ) ∧
        b = (6 * l + 1 : ℤ)) ∨
      (∃ k l : ℕ, 1 ≤ k ∧ k ≤ 2 ^ C.n ∧ ¬ InColumns C k ∧ InColumns C l ∧
        InColumns C (C.app l) ∧ k < C.app l ∧ l < k ∧ (6 * k - 3 : ℤ) ≤ a ∧
        a ≤ (6 * k + 2 : ℤ) ∧ b = (6 * l + 1 : ℤ)) ∨
      (∃ k l : ℕ, InColumns C k ∧ 1 ≤ l ∧ l ≤ 2 ^ C.n ∧ InColumns C (C.app l) ∧
        k ≤ C.app l ∧ l < k ∧ a = (6 * k - 3 : ℤ) ∧ b = (6 * l + 1 : ℤ)) then
    Dir.up
  else if (∃ k : ℕ, InColumns C k ∧ (6 * k : ℤ) ≤ a ∧ a ≤ (6 * k + 1 : ℤ) ∧ b = 2) ∨
      (∃ k : ℕ, 1 ≤ k ∧ k ≤ 2 ^ C.n ∧ ¬ InColumns C k ∧ (6 * k - 4 : ℤ) ≤ a ∧
        a ≤ (6 * k + 1 : ℤ) ∧ b = 2) ∨
      ((6 * 2 ^ C.n + 2 : ℤ) ≤ a ∧ a ≤ (6 * 2 ^ C.n + 4 : ℤ) ∧ b = 2) ∨
      ((6 * 2 ^ C.n + 5 : ℤ) ≤ a ∧ a ≤ (6 * 2 ^ C.n + 6 : ℤ) ∧ 2 ≤ b ∧
        b ≤ (6 * 2 ^ C.n + 4 : ℤ)) then
    Dir.left
  else if (2 ≤ a ∧ a ≤ (6 * 2 ^ C.n + 6 : ℤ) ∧ (6 * 2 ^ C.n + 5 : ℤ) ≤ b ∧
        b ≤ (6 * 2 ^ C.n + 6 : ℤ)) ∨
      (a = (6 * 2 ^ C.n + 4 : ℤ) ∧ 3 ≤ b ∧ b ≤ (6 * 2 ^ C.n + 4 : ℤ)) ∨
      (∃ k : ℕ, InSolutions C k ∧ (6 * k - 2 : ℤ) ≤ a ∧ a ≤ (6 * k - 1 : ℤ) ∧
        (6 * k + 3 : ℤ) ≤ b ∧ b ≤ (6 * 2 ^ C.n + 4 : ℤ)) ∨
      (∃ k : ℕ, InColumns C k ∧ 1 < k ∧ a = (6 * k - 5 : ℤ) ∧ b = 3) then
    Dir.down
  else
    Dir.right

end ConstrSOSP


