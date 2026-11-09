-- Prove2me | Definitions.Def_NAMatchEst_Delta
-- name    : NAMatchEst_Delta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:50:29.767714+00:00
-- url     : https://prove2.me/theorems/7232b4a2-6b4f-4a9d-9af5-681f27735d8f
-- title:
--   The degree cutoff $\Delta=\lfloor 2k/\alpha\rfloor$
-- statement:
--   For a scale $k\in\mathbb N$ and the approximation parameter $\alpha>0$, the degree cutoff of display (3) is
--
--   $$
--   \Delta:=\left\lfloor \frac{2k}{\alpha}\right\rfloor .
--   $$
--
--   It is the number of adjacency-list positions read in a full-row sample.
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §3.2, display (3), p.19 (PDF 23)

import Mathlib

namespace NAMatchEst

/-- The degree cutoff `∆ := ⌊2k/α⌋` of display (3).

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §3.2, p.19 (PDF 23): "To make the number of queried positions an integer, we round down
the cutoff 2k/α used in the overview and set ∆ := ⌊2k/α⌋, V1 := {v ∈ V : deg(v) ⩾ ∆},
U := V \ V1. (3)"

**Formalization Note** `Nat.floor` of the real `2k/α`; named `Delta` (not `∆`). -/
noncomputable def Delta (k : ℕ) (α : ℝ) : ℕ := ⌊2 * (k : ℝ) / α⌋₊

end NAMatchEst


