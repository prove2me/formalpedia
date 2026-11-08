-- Prove2me | Definitions.Def_MaxCompForest_encRowIn
-- name    : MaxCompForest_encRowIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:36:40.469791+00:00
-- url     : https://prove2.me/theorems/f0035285-7e67-4b1d-ad2d-156489426358
-- title:
--   Input of the row-facility algorithm
-- statement:
--   The input word of the row-facility algorithm: $n$, the dimension $p$, the budget $s$, the weights and the rational rows, all in binary.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), Lemma C.1, p.36

import Mathlib
import Definitions.Def_MaxCompForest_encWords
import Definitions.Def_MaxCompForest_matWords
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encRat
open OnlineCRS.Combine (Sym encNat encRat)

namespace MaxCompForest

/-- **The input word of Lemma C.1**: `n`, `p`, `s`, the weights, and the rows, in binary. Its length is the
"total explicit binary input length". Rows are stored as columns of the `p × n` matrix `x`.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), Lemma C.1, p.36. -/
def encRowIn {n p : ℕ} (x : Fin p → Fin n → ℚ) (w : Fin n → ℚ) (s : ℕ) : List Sym :=
  encWords ([encNat n, encNat p, encNat s] ++ (List.finRange n).map (fun v => encRat (w v)) ++
    matWords x)

end MaxCompForest


