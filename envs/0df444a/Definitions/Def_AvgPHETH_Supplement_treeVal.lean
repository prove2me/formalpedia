-- Prove2me | Definitions.Def_AvgPHETH_Supplement_treeVal
-- name    : AvgPHETH_Supplement_treeVal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:39:28.469973+00:00
-- url     : https://prove2.me/theorems/1d71b19f-cec6-4e78-bbed-63ceef856e22
-- title:
--   The induced value $T^k_x(y_1,\dots,y_j)$ of a selector tree
-- statement:
--   Let an assignment give every root bit $B^k_x$ and every selector a value. The selector tree $T^k_x$ has $T(\mathrm{root})=B^k_x$ and, for a node $v$ at depth $j\ge1$ with index $y$ among its siblings,
--
--   $$T(v)=\begin{cases}T(\mathrm{parent}(v))\lor\mathbf 1[y\ne S(\mathrm{parent}(v))]&j\text{ odd},\\ T(\mathrm{parent}(v))\land\mathbf 1[y=S(\mathrm{parent}(v))]&j\text{ even}.\end{cases}$$
--
--   This definition is the induced value at the node $(y_1,\dots,y_j)$. For a leaf it is the answer $V_k(x,y_1,\dots,y_k)$ of the oracle. The child selected by $S(v)$ has value $T(v)$ and every other child has the neutral value of the gate of $v$, so the AND-rooted alternating tree evaluates to its root bit on the induced leaf values, and that leaf assignment is critical.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Definition 8.1, p.38 (PDF 40)

import Mathlib
import Definitions.Def_AvgPHETH_Supplement_treeValFrom

namespace AvgPHETH.Supplement

/-- The induced value `T^k_x(y₁, …, y_j)` at the node `(y₁, …, y_j)` of the selector tree `T^k_x` whose
root bit and selectors are given by the assignment `β`
(Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Definition 8.1, p.38 (PDF 40)): `T(root) = B`, and for a node `v` at depth
`j ≥ 1` with index `y` among its siblings, `T(v) = T(parent(v)) ∨ 1[y ≠ S(parent(v))]` if `j` is odd and
`T(v) = T(parent(v)) ∧ 1[y = S(parent(v))]` if `j` is even. For a leaf this is the answer
`V_k(x, y₁, …, y_k)` (§8.1, p.39 (PDF 41)).

**Formalization Note** The root bit is `1` iff the value of `B^k_x` is the one-bit string `[true]`. -/
def treeVal (β : CVar → List Bool) (k : ℕ) (x : List Bool) (ys : List (List Bool)) : Bool :=
  treeValFrom β k x [] (decide (β ⟨k, x, true, []⟩ = [true])) ys

end AvgPHETH.Supplement


