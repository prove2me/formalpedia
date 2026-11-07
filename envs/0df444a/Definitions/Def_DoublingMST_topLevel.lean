-- Prove2me | Definitions.Def_DoublingMST_topLevel
-- name    : DoublingMST_topLevel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:28:00.80219+00:00
-- url     : https://prove2.me/theorems/ae3f0d60-206c-4ec2-b679-bb31170bc192
-- title:
--   Top level $L=\lceil\log\Delta\rceil+4$
-- statement:
--   With $\Delta=\operatorname{diam}(X)$, the net hierarchy has levels $0,\dots,L$ where $L=\lceil\log_2\Delta\rceil+4$.
--
--   **Formalization Note** The ceiling is taken in $\mathbb N$; under $|X|\ge2$ and minimum distance $>1$ we have $\Delta>1$, so it is the integer ceiling.
-- source:
--   Höckendorff, Hommelsheim, Sohler, Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b39caaedcdac985f11ec23b5833ef4686c045f97ef13a21bdff2fbe759), §2.1, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_DoublingMST_diam

namespace DoublingMST

/-- **The top level L of the net hierarchy.**
Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), §2.1, p.12 (PDF p.14): "assume … that the diameter of X is ∆. Let L = ⌈log ∆⌉ + 4".

**Formalization Note.** `log` is base 2 (`Real.logb 2`), ∆ = `diam d univ`, and the ceiling is
taken in `ℕ`. Under the standing `|X| ≥ 2` and minimum distance `> 1`, ∆ > 1, so `log ∆ > 0` and
the natural ceiling is the integer one. -/
noncomputable def topLevel {n : ℕ} (d : Fin n → Fin n → ℝ) : ℕ :=
  ⌈Real.logb 2 (diam d Finset.univ)⌉₊ + 4

end DoublingMST


