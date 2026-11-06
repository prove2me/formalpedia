-- Prove2me | Definitions.Def_LawLocalComp_expMax
-- name    : LawLocalComp_expMax
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:11:37.966019+00:00
-- url     : https://prove2.me/theorems/c33106c2-88f3-49b7-a9c9-bdf9edc9526b
-- title:
--   Expected maximum $M_Y(k)$ of $k$ iid copies
-- statement:
--   For a law $Y$ and an integer $k$, $M_Y(k)=\mathbb E\max\{Y_1,\dots,Y_k\}$ for iid copies $Y_i$ of $Y$, a finite sum over $k$-tuples of atoms. The empty maximum ($k=0$) is $0$.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), Lemma 2.2, p.4

import Mathlib
import Definitions.Def_LawLocalComp_Law

namespace LawLocalComp

/-- **The expected maximum `M_Y(k)` of `k` iid copies.**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), Lemma 2.2, p.4 ("let MY (k) be the expected maximum of k iid copies").

`expMax Y k = ∑_y (∏_i P(Y = y_i)) · max_i y_i`, the sum over `y : Fin k → supp Y`.

**Formalization Note.** For `k = 0` the empty maximum is `0`; the lemma uses `k ≥ 1`. -/
noncomputable def expMax (Y : Law) (k : ℕ) : ℝ :=
  ∑ y ∈ Fintype.piFinset (fun _ : Fin k => Y.w.support), (∏ i, Y.w (y i)) * ⨆ i, y i

end LawLocalComp


