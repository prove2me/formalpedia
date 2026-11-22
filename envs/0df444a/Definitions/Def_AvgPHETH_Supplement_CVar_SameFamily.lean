-- Prove2me | Definitions.Def_AvgPHETH_Supplement_CVar_SameFamily
-- name    : AvgPHETH_Supplement_CVar_SameFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:37:25.584641+00:00
-- url     : https://prove2.me/theorems/c69ea868-9932-4fe3-a610-236b8d69c62c
-- title:
--   Families of construction variables
-- statement:
--   Two construction variables are in the same **family** if they are in the same group $(k,n)$, are of the same kind (root bit or selector) and have the same depth $j$.
--
--   Within a group, for each $1\le j<k$ the selectors $S^k_{x,y_1,\dots,y_j}$ form the family at depth $j$, and the root bits $B^k_x$ and the root selectors $S^k_x$ form two separate families at depth $0$. Each restriction round treats each family independently.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, "Construction variables", p.39 (PDF 41)

import Mathlib
import Definitions.Def_AvgPHETH_Supplement_CVar

namespace AvgPHETH.Supplement

/-- Two construction variables are in the same **family**: the same group `(k, n = |x|)`, the same
kind and the same depth. Within a group, the root bits `B^k_x` and the root selectors `S^k_x` form two
separate families at depth `0`, and for `1 ≤ j < k` the selectors `S^k_{x,y₁,…,y_j}` form the family
at depth `j` (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, "Construction variables", p.39 (PDF 41)). -/
def CVar.SameFamily (v w : CVar) : Prop :=
  v.k = w.k ∧ v.x.length = w.x.length ∧ v.isBit = w.isBit ∧ v.path.length = w.path.length

end AvgPHETH.Supplement


