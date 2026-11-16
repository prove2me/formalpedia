-- Prove2me | Definitions.Def_MaxCompForest_Supplement_binCode
-- name    : MaxCompForest_Supplement_binCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:18:10.22046+00:00
-- url     : https://prove2.me/theorems/6b90b734-8742-49e4-b6c6-1b25ec514329
-- title:
--   Self-delimiting binary code of a natural number
-- statement:
--   A self-delimiting binary code of a natural number $t$: each binary digit, least significant first, is preceded by a $1$, and a $0$ ends the word. Its length is $2\lceil\log_2(t+1)\rceil+1$. Thresholds of the decision version (spanning-tree counts) and the numerator and denominator of the accuracy $\eta$ are written this way, so the encoding size $N$ is polynomial in the graph size.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), Theorem I.2, p.49 (PDF p.51)

import Mathlib
set_option autoImplicit false

namespace MaxCompForest.Supplement

/-- **A self-delimiting binary code of a natural number**: each binary digit (least significant first) is
preceded by `true`, and `false` ends the word. Its length is `2⌈log₂(t+1)⌉ + 1`.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), Theorem I.2 p.49 (thresholds of the decision version are spanning-tree counts, exponential in the size, so
they are written in binary). -/
def binCode (t : ℕ) : List Bool := (Nat.bits t).flatMap (fun b => [true, b]) ++ [false]

end MaxCompForest.Supplement


