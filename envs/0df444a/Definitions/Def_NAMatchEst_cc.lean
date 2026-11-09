-- Prove2me | Definitions.Def_NAMatchEst_cc
-- name    : NAMatchEst_cc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:48:38.216388+00:00
-- url     : https://prove2.me/theorems/db8193d5-ad9e-47e7-a96e-eea57c25cdb7
-- title:
--   The sampling constant $c=10^5$
-- statement:
--   The sampling constant $c:=10^5$, which multiplies the logarithmic factor in every sample size and inclusion probability of Section 3.
--
--   **Formalization Note** Named `cc` in Lean.
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §3.2, p.19 (PDF 23)

import Mathlib

namespace NAMatchEst

/-- The sampling constant `c := 10⁵`.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §3.2, p.19 (PDF 23): "Set C0 := 2^20, c := 10^5, L := log(2n), where the logarithm is
natural."

**Formalization Note** Named `cc` to avoid a clash with the many Lean binders called `c`. -/
def cc : ℝ := 10 ^ 5

end NAMatchEst


