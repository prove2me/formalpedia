-- Prove2me | Definitions.Def_MaxCompForest_encIndices
-- name    : MaxCompForest_encIndices
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:36:38.39845+00:00
-- url     : https://prove2.me/theorems/1f0c6e26-ddee-40f6-af05-7e4812108c01
-- title:
--   Output: a list of indices
-- statement:
--   A list of labels, row indices or item indices, preceded by its length, written in binary and separated by the symbol $3$.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), Lemma C.1 p.36, Lemma 3.4 p.20, Lemma 3.5 p.22

import Mathlib
import Definitions.Def_MaxCompForest_encWords
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
open OnlineCRS.Combine (Sym encNat)

namespace MaxCompForest

/-- **A list of labels or row indices**, in binary and preceded by its length: the output word of Lemmas C.1,
3.4 and 3.5. The length makes the encoding injective, since the binary word of the number `0` is empty. -/
def encIndices {n : ℕ} (l : List (Fin n)) : List Sym :=
  encWords (encNat l.length :: l.map fun i : Fin n => encNat i.val)

end MaxCompForest


