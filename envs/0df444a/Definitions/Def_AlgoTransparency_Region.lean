-- Prove2me | Definitions.Def_AlgoTransparency_Region
-- name    : AlgoTransparency_Region
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:48:28.352955+00:00
-- url     : https://prove2.me/theorems/d0a00689-d496-4f57-a245-c1a25cafb025
-- title:
--   Labels of the seven regions of Theorem 1 (corrected)
-- statement:
--   The seven regions of the $(C_H,C_L)$ plane in Theorem 1: the paper's $N_1$, $N_2$, $C_1$, $C_4$, and the corrected regions $C_2'$, $N_3'$, $C_3'$, which replace the paper's $C_2$, $N_3$, $C_3$. Their inequalities are `InRegion`.
-- source:
--   Wang, Huang, Jasin & Singh, Algorithmic Transparency with Strategic Users, arXiv:2008.09283v1, Figure 4, p.21 (PDF 22)

import Mathlib

namespace AlgoTransparency

/-- **Labels of the seven regions of the `(C_H, C_L)` plane** in Theorem 1 of Wang, Huang,
Jasin & Singh, arXiv:2008.09283v1, Figure 4, p.21 (PDF 22), with the mission's correction:

* `N1`, `N2`, `C1`, `C4` — the paper's regions;
* `C2'`, `N3'`, `C3'` — the corrected versions of the paper's `C2`, `N3`, `C3`, whose shared
  boundaries are moved from the line `C_H = (1 − λ)R` to the ray `λ C_H = (1 − λ) C_L`.

The inequalities are `AlgoTransparency.InRegion`. -/
inductive Region
  | N1
  | N2
  | N3'
  | C1
  | C2'
  | C3'
  | C4
  deriving DecidableEq, Repr

end AlgoTransparency


