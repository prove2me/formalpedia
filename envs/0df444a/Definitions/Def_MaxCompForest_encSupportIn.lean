-- Prove2me | Definitions.Def_MaxCompForest_encSupportIn
-- name    : MaxCompForest_encSupportIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:36:52.098128+00:00
-- url     : https://prove2.me/theorems/b47936c9-67b6-42ae-891b-102310077385
-- title:
--   Input of the mass-support algorithm
-- statement:
--   The input word of the mass-support algorithm: $m$, $\eta$, $N$, and the items $(p_x,d_{x,i})$ in binary. The columns $a_i$ are not part of the input, because only item moments enter the construction.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), Lemma 3.4, p.20

import Mathlib
import Definitions.Def_MaxCompForest_encWords
import Definitions.Def_MaxCompForest_itemWords
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encRat
open OnlineCRS.Combine (Sym encNat encRat)

namespace MaxCompForest

/-- **The input word of Lemma 3.4**: `m`, `η`, `N`, then the items. The columns `a_i` are not read: "Only item
moments enter the construction".
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), Lemma 3.4, p.20. -/
def encSupportIn {N m : ℕ} (η : ℚ) (p : Fin N → ℚ) (d : Fin N → Fin m → ℚ) : List Sym :=
  encWords ([encNat m, encRat η, encNat N] ++
    (List.finRange N).flatMap fun x => itemWords (p x) (d x))

end MaxCompForest


