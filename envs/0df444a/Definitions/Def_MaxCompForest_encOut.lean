-- Prove2me | Definitions.Def_MaxCompForest_encOut
-- name    : MaxCompForest_encOut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:36:26.020535+00:00
-- url     : https://prove2.me/theorems/ff77960f-7f4d-4ced-a11b-c12d3a09183d
-- title:
--   Output of the forest algorithm
-- statement:
--   The output word of the forest algorithm: the exact rational score of the forest, followed by its labels in binary.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), pp.14–15

import Mathlib
import Definitions.Def_MaxCompForest_encWords
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encRat
open OnlineCRS.Combine (Sym encNat encRat)

namespace MaxCompForest

/-- **The output word of the algorithm of Theorem 3.1**: the exact rational score, then the selected labels.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), pp.14–15: "return a forest of labelled original edges together with its exact rational
score". -/
def encOut {m : ℕ} (F : List (Fin m)) (score : ℚ) : List Sym :=
  encWords (encRat score :: F.map fun e : Fin m => encNat e.val)

end MaxCompForest


