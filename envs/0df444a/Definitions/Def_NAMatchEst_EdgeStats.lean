-- Prove2me | Definitions.Def_NAMatchEst_EdgeStats
-- name    : NAMatchEst_EdgeStats
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:51:39.918139+00:00
-- url     : https://prove2.me/theorems/45129428-baf2-4b4f-be5d-1ff9d9873c42
-- title:
--   Statistics of the certified-edge test
-- statement:
--   The record of one run of the certified-edge test for a fixed set $H$: the two Bernoulli samples $S^L$, $S^R$, the retained sets $S^L_3$, $S^R_3$ of display (16), and the number $Z_E$ of directed incidences of display (18).
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §3.5, displays (16) and (18), pp.24–25 (PDF 28–29)

import Mathlib

namespace NAMatchEst

/-- The statistics of one run of the certified-edge test, for a fixed set `H`: the two Bernoulli
samples `S^L`, `S^R`, the retained sets `S^L_3`, `S^R_3` of display (16), and the count `Z_E` of
directed incidences of display (18).

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §3.5, pp.24–25 (PDF 28–29), displays (16) and (18). -/
structure EdgeStats (n : ℕ) where
  /-- The left sample `S^L`. -/
  SL : Finset (Fin n)
  /-- The right sample `S^R`. -/
  SR : Finset (Fin n)
  /-- The retained left endpoints `S^L_3`. -/
  SL3 : Finset (Fin n)
  /-- The retained right endpoints `S^R_3`. -/
  SR3 : Finset (Fin n)
  /-- The number `Z_E` of directed incidences between `S^L_3` and `S^R_3`. -/
  ZE : ℕ

end NAMatchEst


