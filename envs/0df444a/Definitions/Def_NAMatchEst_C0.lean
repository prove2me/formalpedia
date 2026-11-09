-- Prove2me | Definitions.Def_NAMatchEst_C0
-- name    : NAMatchEst_C0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:48:23.183071+00:00
-- url     : https://prove2.me/theorems/55115619-5052-44af-a41c-66a7cf29464a
-- title:
--   The constant $C_0=2^{20}$
-- statement:
--   The universal constant $C_0:=2^{20}$ of the gap problem: the tester distinguishes $\mu(G)\ge k$ from $\mu(G)<k/(C_0\alpha)$. The paper states that the constants are chosen for convenience and not optimized.
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §3.2, p.19 (PDF 23)

import Mathlib

namespace NAMatchEst

/-- The universal constant `C₀ := 2²⁰` of the gap problem.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §3.2, p.19 (PDF 23): "Set C0 := 2^20, c := 10^5, L := log(2n), where the logarithm is
natural. These constants are chosen for convenience and are not optimized." -/
def C0 : ℝ := 2 ^ 20

end NAMatchEst


