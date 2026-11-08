-- Prove2me | Definitions.Def_MaxCompForest_encFactorOut
-- name    : MaxCompForest_encFactorOut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:36:34.216776+00:00
-- url     : https://prove2.me/theorems/322ff373-a444-44dc-b0c1-d11250225028
-- title:
--   Output of the slow-response factor algorithm
-- statement:
--   The output word of the slow-response factor algorithm: the rational cutoff $c$, the retained rank $r$, and the rational factor $\mathbf F$ in binary. For $r=0$ the factor is empty.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), Theorem F.1, p.42

import Mathlib
import Definitions.Def_MaxCompForest_encWords
import Definitions.Def_MaxCompForest_matWords
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encRat
open OnlineCRS.Combine (Sym encNat encRat)

namespace MaxCompForest

/-- **The output word of Theorem F.1**: the cutoff `c`, the rank `r`, the factor `𝐅`. -/
def encFactorOut {n : ℕ} (c : ℚ) (r : ℕ) (F : Fin r → Fin n → ℚ) : List Sym :=
  encWords ([encRat c, encNat r] ++ matWords F)

end MaxCompForest


