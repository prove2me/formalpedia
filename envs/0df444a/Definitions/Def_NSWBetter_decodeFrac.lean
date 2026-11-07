-- Prove2me | Definitions.Def_NSWBetter_decodeFrac
-- name    : NSWBetter_decodeFrac
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:51:57.751553+00:00
-- url     : https://prove2.me/theorems/8841eaaf-9255-4762-99a5-d428d48045da
-- title:
--   Reading a rational $n\times m$ matrix from a list
-- statement:
--   A list of rationals is read as the $n\times m$ matrix whose entry $(i,g)$ (0-based) is the list element at position $i\cdot m+g$, and $0$ if the list is too short.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Corollary 4.15, p.25; Theorems 5.2, 6.1 (fractional allocations as input and output)

import Mathlib
import Definitions.Def_NSWBetter_Inst

namespace NSWBetter

/-- **A rational matrix from a list.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Section 2, p.8: "A fractional allocation x is an n × m matrix".

`decodeFrac I xs i g = xs[i·m + g]` (row-major), with missing entries read as `0`. Every list is read as some matrix; whether it is a fractional allocation is stated separately (`IsFrac`). -/
def decodeFrac (I : Inst) (xs : List ℚ) : Fin I.n → Fin I.m → ℚ :=
  fun i g => xs.getD (i.val * I.m + g.val) 0

end NSWBetter


