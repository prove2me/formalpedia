-- Prove2me | Definitions.Def_MaxCompForest_matWords
-- name    : MaxCompForest_matWords
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:47.418767+00:00
-- url     : https://prove2.me/theorems/b0357a8b-989d-40eb-9df0-f0fe0fa79520
-- title:
--   Binary encoding of a rational matrix
-- statement:
--   The entries of a rational $r\times n$ matrix as binary words, row by row.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), Theorem F.1, p.42

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encRat
open OnlineCRS.Combine (Sym encNat encRat)

namespace MaxCompForest

/-- **The words of a rational `r × n` matrix**, row by row. -/
def matWords {r n : ℕ} (F : Fin r → Fin n → ℚ) : List (List Sym) :=
  (List.finRange r).flatMap fun i => (List.finRange n).map fun v => encRat (F i v)

end MaxCompForest


