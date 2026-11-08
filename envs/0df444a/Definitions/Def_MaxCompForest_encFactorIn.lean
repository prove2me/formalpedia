-- Prove2me | Definitions.Def_MaxCompForest_encFactorIn
-- name    : MaxCompForest_encFactorIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:37:42.105102+00:00
-- url     : https://prove2.me/theorems/cc5a92d6-cab8-4b77-831a-7a48a567e91e
-- title:
--   Input of the slow-response factor algorithm
-- statement:
--   The input word of the slow-response factor algorithm: the graph, followed by $q$, $\gamma$, $\theta$, in binary. Its length $L$ contains the bits of $\theta$.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), Theorem F.1, p.42

import Mathlib
import Definitions.Def_MaxCompForest_encWords
import Definitions.Def_MaxCompForest_graphWords
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encRat
open OnlineCRS.Combine (Sym encNat encRat)

namespace MaxCompForest

/-- **The input word of Theorem F.1**: the graph, then `q`, `γ`, `θ` in binary.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), Theorem F.1, p.42. -/
def encFactorIn (I : RInst) (q : ℕ) (γ θ : ℚ) : List Sym :=
  encWords (graphWords I ++ [encNat q, encRat γ, encRat θ])

end MaxCompForest


