-- Prove2me | Definitions.Def_MaxCompForest_itemBits
-- name    : MaxCompForest_itemBits
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:36:48.626197+00:00
-- url     : https://prove2.me/theorems/189876f6-c1c4-46e8-a6b1-91124ea85040
-- title:
--   The item-length bound $B_{\mathrm{item}}$
-- statement:
--   $B_{\mathrm{item}}$ of Lemma 3.4, the length of the longest encoded item.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), Lemma 3.4, p.20

import Mathlib
import Definitions.Def_MaxCompForest_encWords
import Definitions.Def_MaxCompForest_itemWords

namespace MaxCompForest

/-- **The bound `B_item`** on the encoded item data of Lemma 3.4: the longest encoded item. -/
def itemBits {N m : ℕ} (p : Fin N → ℚ) (d : Fin N → Fin m → ℚ) : ℕ :=
  Finset.univ.sup fun x => (encWords (itemWords (p x) (d x))).length

end MaxCompForest


