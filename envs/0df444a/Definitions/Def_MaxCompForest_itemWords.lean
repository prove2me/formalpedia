-- Prove2me | Definitions.Def_MaxCompForest_itemWords
-- name    : MaxCompForest_itemWords
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:54.391134+00:00
-- url     : https://prove2.me/theorems/86409a8d-dfcb-47d0-8496-5f352a8dcd53
-- title:
--   Binary encoding of one item
-- statement:
--   One item of the mass-support lemma: its scalar $p_x$ and its masses $d_{x,i}$, in binary. The columns $a_i$ are not part of it.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), Lemma 3.4, p.20

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encRat
open OnlineCRS.Combine (Sym encNat encRat)

namespace MaxCompForest

/-- **The words of one item** of Lemma 3.4: `p_x`, then its masses, in binary. -/
def itemWords {m : ℕ} (p : ℚ) (d : Fin m → ℚ) : List (List Sym) :=
  encRat p :: (List.finRange m).map fun i => encRat (d i)

end MaxCompForest


