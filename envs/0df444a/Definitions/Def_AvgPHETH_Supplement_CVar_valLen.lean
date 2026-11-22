-- Prove2me | Definitions.Def_AvgPHETH_Supplement_CVar_valLen
-- name    : AvgPHETH_Supplement_CVar_valLen
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:36:48.88667+00:00
-- url     : https://prove2.me/theorems/47ebd71f-05a7-4876-af19-77779ae507e6
-- title:
--   The alphabet of a construction variable
-- statement:
--   A root bit $B^k_x$ takes values in $\{0,1\}$, strings of length $1$. A selector at depth $j$, $S^k_{x,y_1,\dots,y_j}$, takes values in $Y_{j+1}(|x|)=\{0,1\}^{a_{j+1}(|x|)}$: it names one of the children of its node.
--
--   This definition is the length of the value: $1$ for a root bit and $a_{j+1}(|x|)$ for a selector at depth $j$.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, "Construction variables", p.39 (PDF 41)

import Mathlib
import Definitions.Def_AvgPHETH_Supplement_CVar
import Definitions.Def_AvgPHETH_Supplement_aPar

namespace AvgPHETH.Supplement

/-- The length of the value of a construction variable: `1` for a root bit `B^k_x` (alphabet `{0,1}`),
and `a_{j+1}(|x|)` for a selector at depth `j` (alphabet `Y_{j+1}(|x|) = {0,1}^{a_{j+1}(|x|)}`)
(Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, "Construction variables", p.39 (PDF 41)). -/
noncomputable def CVar.valLen (ε : ℕ → ℝ) (v : CVar) : ℕ :=
  if v.isBit = true then 1 else aPar ε (v.path.length + 1) v.x.length

end AvgPHETH.Supplement


