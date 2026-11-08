-- Prove2me | Definitions.Def_MaxCompForest_encIn
-- name    : MaxCompForest_encIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:37:30.546877+00:00
-- url     : https://prove2.me/theorems/730a193a-3930-48ab-8461-df766a8b30da
-- title:
--   Input of the forest algorithm
-- statement:
--   The input word of the forest algorithm: the graph, followed by $q$, $\gamma$, $\varepsilon$ and $k$, all in binary. Its length is the total binary input length $L$ of Theorem 3.1.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), Theorem 3.1, p.15

import Mathlib
import Definitions.Def_MaxCompForest_encWords
import Definitions.Def_MaxCompForest_graphWords
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encRat
open OnlineCRS.Combine (Sym encNat encRat)

namespace MaxCompForest

/-- **The input word of the algorithm of Theorem 3.1**: the graph, then `q`, `γ`, `ε`, `k` in binary. Its
length is the `L` of (3.4).
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), Theorem 3.1, p.15. -/
def encIn (I : RInst) (q : ℕ) (γ ε : ℚ) (k : ℕ) : List Sym :=
  encWords (graphWords I ++ [encNat q, encRat γ, encRat ε, encNat k])

end MaxCompForest


