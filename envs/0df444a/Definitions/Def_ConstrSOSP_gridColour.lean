-- Prove2me | Definitions.Def_ConstrSOSP_gridColour
-- name    : ConstrSOSP_gridColour
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:03:05.184513+00:00
-- url     : https://prove2.me/theorems/5c4ece75-46fd-4cd5-8ef8-7a35593cb479
-- title:
--   Colour of a grid point (table of $f(a,b)$)
-- statement:
--   The colour of the grid point $(a,b)$ for the Iter circuit $C$, transcribed from the table of $f(a,b)$ on p.30: blue on the blue columns $6k-3\le a\le 6k-1$, $3\le b\le 6k+2$ ($k\in$ Columns), their bases and the blue corridors; black on the black corridor at $b=2$; green on the lower boundary $b\le1$ and the right boundary; orange on the left boundary $a\le1$ and the upper boundary; red elsewhere. The value of $f$ at the grid point is the colour function of its colour.
--
--   **Formalization Note** Integer coordinates; the cases are tested in the page's order (regions of different colours are disjoint).
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), §5.3, p.30

import Mathlib
import Definitions.Def_ConstrSOSP_Colour
import Definitions.Def_ConstrSOSP_InColumns

namespace ConstrSOSP

open Classical in
/-- **The colour of a grid point** (arXiv:2604.02285, 2 Nov 2026, the table of `f(a, b)` on the
grid, §5.3, p.30), for an Iter circuit `C` with `n` inputs (`[2ⁿ] = {1, …, 2ⁿ}`):
* **blue** for `6k − 3 ≤ a ≤ 6k − 1`, `3 ≤ b ≤ 6k + 2`, `k ∈ Columns` (blue column); `a = 6k − 2`,
  `b = 2`, `k ∈ Columns` (blue column base); `6k ≤ a ≤ 6k + 2`, `6k + 1 ≤ b ≤ 6k + 2`, `k ∈ [2ⁿ]`,
  `C(k) > k`, `C(k) ∈ Columns` (start of a blue corridor); `6k + 1 ≤ a ≤ 6k + 2`,
  `6l + 1 ≤ b ≤ 6l + 2`, `k ∈ [2ⁿ]`, `l ∈ Columns`, `C(l) ∈ Columns`, `C(l) > k > l` (blue
  corridor exiting a blue column at a crossing); `6k − 3 ≤ a ≤ 6k + 2`, `6l + 1 ≤ b ≤ 6l + 2`,
  `k ∈ [2ⁿ] ∖ Columns`, `l ∈ Columns`, `C(l) ∈ Columns`, `C(l) > k > l` (blue corridor crossing a
  missing column);
* **black** for `6k − 1 ≤ a ≤ 6k + 1`, `b = 2`, `k ∈ Columns`; `6k − 4 ≤ a ≤ 6k + 1`, `b = 2`,
  `k ∈ [2ⁿ] ∖ Columns`; `6·2ⁿ + 2 ≤ a ≤ 6·2ⁿ + 4`, `b = 2`;
* **green** for `2 ≤ a ≤ 6·2ⁿ + 6`, `0 ≤ b ≤ 1`; `6·2ⁿ + 5 ≤ a ≤ 6·2ⁿ + 6`, `2 ≤ b ≤ 6·2ⁿ + 4`;
* **orange** for `0 ≤ a ≤ 1`, `0 ≤ b ≤ 6·2ⁿ + 6`; `2 ≤ a ≤ 6·2ⁿ + 6`, `6·2ⁿ + 5 ≤ b ≤ 6·2ⁿ + 6`;
* **red** elsewhere.

**Formalization Note** Coordinates are integers; the cases are tested in the order of the page
(the regions of different colours are disjoint). The value of `f` at the grid point is the colour
function of this colour at the point (`colourPhi`). -/
noncomputable def gridColour (C : Circuit) (a b : ℤ) : Colour :=
  if (∃ k : ℕ, InColumns C k ∧ (6 * k - 3 : ℤ) ≤ a ∧ a ≤ (6 * k - 1 : ℤ) ∧ 3 ≤ b ∧
        b ≤ (6 * k + 2 : ℤ)) ∨
      (∃ k : ℕ, InColumns C k ∧ a = (6 * k - 2 : ℤ) ∧ b = 2) ∨
      (∃ k : ℕ, 1 ≤ k ∧ k ≤ 2 ^ C.n ∧ k < C.app k ∧ InColumns C (C.app k) ∧
        (6 * k : ℤ) ≤ a ∧ a ≤ (6 * k + 2 : ℤ) ∧ (6 * k + 1 : ℤ) ≤ b ∧ b ≤ (6 * k + 2 : ℤ)) ∨
      (∃ k l : ℕ, 1 ≤ k ∧ k ≤ 2 ^ C.n ∧ InColumns C l ∧ InColumns C (C.app l) ∧
        k < C.app l ∧ l < k ∧ (6 * k + 1 : ℤ) ≤ a ∧ a ≤ (6 * k + 2 : ℤ) ∧
        (6 * l + 1 : ℤ) ≤ b ∧ b ≤ (6 * l + 2 : ℤ)) ∨
      (∃ k l : ℕ, 1 ≤ k ∧ k ≤ 2 ^ C.n ∧ ¬ InColumns C k ∧ InColumns C l ∧
        InColumns C (C.app l) ∧ k < C.app l ∧ l < k ∧ (6 * k - 3 : ℤ) ≤ a ∧
        a ≤ (6 * k + 2 : ℤ) ∧ (6 * l + 1 : ℤ) ≤ b ∧ b ≤ (6 * l + 2 : ℤ)) then
    Colour.blue
  else if (∃ k : ℕ, InColumns C k ∧ (6 * k - 1 : ℤ) ≤ a ∧ a ≤ (6 * k + 1 : ℤ) ∧ b = 2) ∨
      (∃ k : ℕ, 1 ≤ k ∧ k ≤ 2 ^ C.n ∧ ¬ InColumns C k ∧ (6 * k - 4 : ℤ) ≤ a ∧
        a ≤ (6 * k + 1 : ℤ) ∧ b = 2) ∨
      ((6 * 2 ^ C.n + 2 : ℤ) ≤ a ∧ a ≤ (6 * 2 ^ C.n + 4 : ℤ) ∧ b = 2) then
    Colour.black
  else if (2 ≤ a ∧ a ≤ (6 * 2 ^ C.n + 6 : ℤ) ∧ 0 ≤ b ∧ b ≤ 1) ∨
      ((6 * 2 ^ C.n + 5 : ℤ) ≤ a ∧ a ≤ (6 * 2 ^ C.n + 6 : ℤ) ∧ 2 ≤ b ∧
        b ≤ (6 * 2 ^ C.n + 4 : ℤ)) then
    Colour.green
  else if (0 ≤ a ∧ a ≤ 1 ∧ 0 ≤ b ∧ b ≤ (6 * 2 ^ C.n + 6 : ℤ)) ∨
      (2 ≤ a ∧ a ≤ (6 * 2 ^ C.n + 6 : ℤ) ∧ (6 * 2 ^ C.n + 5 : ℤ) ≤ b ∧
        b ≤ (6 * 2 ^ C.n + 6 : ℤ)) then
    Colour.orange
  else
    Colour.red

end ConstrSOSP


