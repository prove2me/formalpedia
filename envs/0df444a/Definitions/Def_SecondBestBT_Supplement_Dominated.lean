-- Prove2me | Definitions.Def_SecondBestBT_Supplement_Dominated
-- name    : SecondBestBT_Supplement_Dominated
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:34:45.524197+00:00
-- url     : https://prove2.me/theorems/22ab8c68-c65b-496b-91a7-0829d28f6090
-- title:
--   Dominance order $\omega\prec\omega'$ (Definition 5.2)
-- statement:
--   Let $\omega=(y;\mathbf r)$ and $\omega'=(y';\mathbf r')$ be states. Then $\omega$ is **dominated** by $\omega'$, written $\omega\prec\omega'$, if either
--
--   1. $\mathbf r'$ is a proper suffix of $\mathbf r$, or
--   2. $\mathbf r=\mathbf r'$ and $y<y'$.
--
--   A dominating state commits more trade and so brings the greedy construction closer to failure; the order is used to propagate failures to shorter inputs.
--
--   **Formalization Note** Ratio lists are compared as lists of values in $[0,\infty]$.
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Definition 5.2, p.18

import Mathlib

open scoped ENNReal

namespace SecondBestBT.Supplement

/-- The **dominance order** `≺` on states (Liu–Qin–Ren–Wang, arXiv:2606.03849, held version sha256 17184930…, Definition 5.2, p.18): for `ω = (y ; r)` and
`ω' = (y' ; r')`, `ω ≺ ω'` (`ω` is dominated by `ω'`) iff either (i) `r'` is a proper suffix of
`r`, or (ii) `r = r'` and `y < y'`.

**Formalization Note** Ratio lists are compared as lists of values in `ℝ≥0∞`; "proper suffix" is
`List.IsSuffix` (`<:+`) together with inequality of the lists. -/
def Dominated (ω ω' : ℝ × List ℝ≥0∞) : Prop :=
  (ω'.2 <:+ ω.2 ∧ ω'.2 ≠ ω.2) ∨ (ω.2 = ω'.2 ∧ ω.1 < ω'.1)

end SecondBestBT.Supplement


