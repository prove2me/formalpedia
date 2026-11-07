-- Prove2me | Definitions.Def_AvgPHETH_witnessTime
-- name    : AvgPHETH_witnessTime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:29:03.784883+00:00
-- url     : https://prove2.me/theorems/80993c69-937f-4fe4-be6f-9e5807493487
-- title:
--   The time bound $2^{cw/\log^k w}$
-- statement:
--   The number of steps $\lceil 2^{c\,w(n)/(\log_2\max(w(n),2))^k}\rceil$. The maximum only excludes $w\le1$, where the logarithm is not useful.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Theorem 1.2 (i), p.3 (PDF 5); p.30 (PDF 32)

import Mathlib

namespace AvgPHETH

/-- The time bound `2^{c w(n) / (log w(n))^k}`, as a natural-number clock
(Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Theorem 1.2 (i), p.3 (PDF 5); p.30 (PDF 32)).

**Formalization Note** `max(w, 2)` only excludes `w ≤ 1`, where `log₂ w` is `0` or a junk value. -/
noncomputable def witnessTime (c k : ℕ) (w : ℕ → ℕ) (n : ℕ) : ℕ :=
  ⌈(2 : ℝ) ^ ((c : ℝ) * (w n : ℝ) / Real.logb 2 (max (w n : ℝ) 2) ^ k)⌉₊

end AvgPHETH


