-- Prove2me | Definitions.Def_AvgPHETH_Supplement_treeValFrom
-- name    : AvgPHETH_Supplement_treeValFrom
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:38:52.525719+00:00
-- url     : https://prove2.me/theorems/3c1217a6-c694-49ed-8de0-748aae5c936a
-- title:
--   Induced values of a selector tree, from a node downwards
-- statement:
--   In a selector tree with root bit $B$ and selectors $S$, the induced value of a node $v$ at depth $j\ge1$ with index $y$ among its siblings is
--
--   $$T(v)=\begin{cases}T(\mathrm{parent}(v))\lor\mathbf 1[y\ne S(\mathrm{parent}(v))]&j\text{ odd},\\ T(\mathrm{parent}(v))\land\mathbf 1[y=S(\mathrm{parent}(v))]&j\text{ even}.\end{cases}$$
--
--   This definition computes the induced value of a descendant of a node, given the node, its induced value and the remaining path; it is the recursion behind the induced value $T^k_x(y_1,\dots,y_j)$.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Definition 8.1, p.38 (PDF 40)

import Mathlib
import Definitions.Def_AvgPHETH_Supplement_CVar

namespace AvgPHETH.Supplement

/-- The induced value of a descendant of a node of the selector tree `T^k_x`, given the node
`pre = (y₁, …, y_{j})`, its induced value `val`, and the remaining path `ys`
(Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Definition 8.1, p.38 (PDF 40)): going down to the child with index `y`, at depth `j + 1`,
the value becomes `T(parent) ∨ 1[y ≠ S(parent)]` if `j + 1` is odd and `T(parent) ∧ 1[y = S(parent)]`
if `j + 1` is even.

**Formalization Note** `β` is a total assignment of values to the construction variables; the selector
of the node `pre` is `β ⟨k, x, false, pre⟩`. -/
def treeValFrom (β : CVar → List Bool) (k : ℕ) (x : List Bool) :
    List (List Bool) → Bool → List (List Bool) → Bool
  | _, val, [] => val
  | pre, val, y :: rest =>
      treeValFrom β k x (pre ++ [y])
        (if (pre.length + 1) % 2 = 1 then val || decide (y ≠ β ⟨k, x, false, pre⟩)
         else val && decide (y = β ⟨k, x, false, pre⟩))
        rest

end AvgPHETH.Supplement


