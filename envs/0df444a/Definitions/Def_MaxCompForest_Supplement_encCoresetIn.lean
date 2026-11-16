-- Prove2me | Definitions.Def_MaxCompForest_Supplement_encCoresetIn
-- name    : MaxCompForest_Supplement_encCoresetIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:15:19.324337+00:00
-- url     : https://prove2.me/theorems/32c2504e-3cdc-4e87-933c-b6dc6c327620
-- title:
--   Input word of the enumeration of Theorem 4.2
-- statement:
--   The binary input of the exact enumeration of Theorem 4.2: the dimension $m$, the budget $k$, the rationals $a$ and $\varepsilon$, and the rational $m\times m$ matrix $K$, all in binary. Its length is the total binary input length $L$.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), Theorem 4.2, p.26 (PDF p.28)

import Mathlib
import Definitions.Def_MaxCompForest_encWords
import Definitions.Def_MaxCompForest_matWords
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encRat
open OnlineCRS.Combine (Sym encNat encRat)
set_option autoImplicit false

namespace MaxCompForest.Supplement

/-- **The input word of the enumeration of Theorem 4.2**: `m`, `k`, `a`, `ε` and the rational `m × m` matrix `K`,
in binary; its length is the total binary input length `L`.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), Theorem 4.2 ("for rational K, a, and ε … L is the total binary input length"), p.26. -/
def encCoresetIn {m : ℕ} (K : Fin m → Fin m → ℚ) (a ε : ℚ) (k : ℕ) : List Sym :=
  MaxCompForest.encWords ([encNat m, encNat k, encRat a, encRat ε] ++ MaxCompForest.matWords K)

end MaxCompForest.Supplement


