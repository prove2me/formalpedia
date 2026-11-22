-- Prove2me | Definitions.Def_AvgPHETH_Supplement_CVar_IsValid
-- name    : AvgPHETH_Supplement_CVar_IsValid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:36:04.5702+00:00
-- url     : https://prove2.me/theorems/87e57d62-cfc3-494c-9a10-c2cccadfbd2c
-- title:
--   Which names are construction variables
-- statement:
--   A name is a construction variable of the oracle construction if $(k,|x|)$ is active and it is either the root bit $B^k_x$, or the selector $S^k_{x,y_1,\dots,y_j}$ of an internal node with $0\le j<k$ and $y_i\in Y_i(|x|)=\{0,1\}^{a_i(|x|)}$ for every $i\le j$ (for $j=0$ this is the root selector $S^k_x$).
--
--   The variables with a given $k$ and $|x|=n$ form the group $(k,n)$.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, "Construction variables", p.39 (PDF 41)

import Mathlib
import Definitions.Def_AvgPHETH_Supplement_CVar
import Definitions.Def_AvgPHETH_Supplement_IsActive
import Definitions.Def_AvgPHETH_Supplement_aPar

namespace AvgPHETH.Supplement

/-- The name `v` is a construction variable: `(k, |x|)` is active and `v` is either the root bit
`B^k_x`, or the selector of an internal node `(y₁, …, y_j)`, `0 ≤ j < k`, `y_i ∈ Y_i(|x|) = {0,1}^{a_i(|x|)}`
(Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, "Construction variables", p.39 (PDF 41)). -/
def CVar.IsValid (ε : ℕ → ℝ) (v : CVar) : Prop :=
  IsActive ε v.k v.x.length ∧
    if v.isBit = true then v.path = []
    else v.path.length < v.k ∧
      ∀ (i : ℕ) (h : i < v.path.length), (v.path[i]).length = aPar ε (i + 1) v.x.length

end AvgPHETH.Supplement


