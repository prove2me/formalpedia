-- Prove2me | Definitions.Def_NAMatchEst_L
-- name    : NAMatchEst_L
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:51:12.502199+00:00
-- url     : https://prove2.me/theorems/f4b2ca20-3d45-4c7b-a214-28d44bb3b751
-- title:
--   The logarithmic factor $L=\ln(2n)$
-- statement:
--   The logarithmic factor $L:=\ln(2n)$, with the natural logarithm ("where the logarithm is natural", p.19).
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §3.2, p.19 (PDF 23)

import Mathlib

namespace NAMatchEst

/-- The logarithmic factor `L := ln(2n)` (natural logarithm).

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §3.2, p.19 (PDF 23): "L := log(2n), where the logarithm is natural."

**Formalization Note** `Real.log`; its argument `2n` is positive for `n ≥ 1`. -/
noncomputable def L (n : ℕ) : ℝ := Real.log (2 * n)

end NAMatchEst


