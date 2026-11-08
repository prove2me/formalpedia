-- Prove2me | Definitions.Def_MaxCompForest_encWords
-- name    : MaxCompForest_encWords
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:22.490406+00:00
-- url     : https://prove2.me/theorems/60a4029e-24d4-47f9-844d-7d55a2c78ebf
-- title:
--   Words separated by the symbol $3$
-- statement:
--   A list of words over the four-symbol alphabet $\{0,1,2,3\}$, joined by the separator symbol $3$. Numbers are written in binary, with $2$ inside a rational, so a word never contains $3$ and the list can be read back.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), p.14

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
open OnlineCRS.Combine (Sym)

namespace MaxCompForest

/-- **A list of words joined by the separator symbol `3`.** No encoded number contains `3`.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), p.14 (binary input of total encoding length `L`). -/
def encWords (ws : List (List Sym)) : List Sym := List.intercalate [3] ws

end MaxCompForest


