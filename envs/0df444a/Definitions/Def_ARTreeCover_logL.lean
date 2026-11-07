-- Prove2me | Definitions.Def_ARTreeCover_logL
-- name    : ARTreeCover_logL
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:52:02.151813+00:00
-- url     : https://prove2.me/theorems/e02c03d7-41fc-455d-836d-0eebb79fca1f
-- title:
--   The logarithm $L(x)=\max(1,\log_2 x)$ of the size bounds
-- statement:
--   $L(x)=\max(1,\log_2 x)$. Every $O(\log n)$ and $O(\log(n/\epsilon))$ of the mission is read with $L$.
--
--   It equals $\log_2 x$ for $x\ge 2$. At $x\le 1$ it keeps a bound at least the constant, which a one-vertex graph needs: one forest must contain its vertex.
-- source:
--   Elkin, Shabat, Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings, STOC 2027 submission (manuscript sha256 8ce8e6be…), §2, p.9 (PDF p.12)

import Mathlib

namespace ARTreeCover

/-- The logarithm used in the size bounds: `L(x) = max(1, log₂ x)`.

Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…), §2, p.9 (PDF p.12): "Unless stated otherwise,
all logarithms are in base 2".

**Formalization Note.** Every `O(log n)` (and `O(log(n/ϵ))`) of the paper is read with
`L(n) = max(1, log₂ n)`. It equals `log₂ n` for `n ≥ 2`; at `n ≤ 1`, where `log₂ n ≤ 0`, it keeps
the bound at least the constant, which a one-vertex graph needs (one forest must contain its
vertex). -/
noncomputable def logL (x : ℝ) : ℝ := max 1 (Real.logb 2 x)

end ARTreeCover


