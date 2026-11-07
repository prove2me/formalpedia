-- Prove2me | Definitions.Def_AvgPHETH_Inst3DNF_N
-- name    : AvgPHETH_Inst3DNF_N
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:26:27.833092+00:00
-- url     : https://prove2.me/theorems/8fccb124-e87d-4250-8bfe-d90f3b15dd5f
-- title:
--   The number $N$ of variables of $\varphi$
-- statement:
--   The number $N=|y|+|z|$ of variables of the formula $\varphi(y,z)$.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §1.1, p.2 (PDF 4)

import Mathlib
import Definitions.Def_AvgPHETH_Inst3DNF

namespace AvgPHETH

/-- The number `N` of variables of `φ(y, z)` (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §1.1, p.2 (PDF 4)). -/
def Inst3DNF.N (φ : Inst3DNF) : ℕ := φ.numY + φ.numZ

end AvgPHETH


