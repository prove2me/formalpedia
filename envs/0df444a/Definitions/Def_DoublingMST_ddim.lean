-- Prove2me | Definitions.Def_DoublingMST_ddim
-- name    : DoublingMST_ddim
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:26:09.718928+00:00
-- url     : https://prove2.me/theorems/cc146b58-382b-4351-b8b3-d9da80a772d5
-- title:
--   Doubling dimension $\operatorname{ddim}(X)$
-- statement:
--   $\operatorname{ddim}(X)=\operatorname{ddim}(X,d)$, the doubling dimension of the whole space (Definition 2.2 with $S=X$). It is the $\operatorname{ddim}$ in every $2^{O(\operatorname{ddim})}$ bound of the mission; the algorithm is never given it.
-- source:
--   Höckendorff, Hommelsheim, Sohler, Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b39caaedcdac985f11ec23b5833ef4686c045f97ef13a21bdff2fbe759), Definition 2.2, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_DoublingMST_ddimOn
open scoped Classical

namespace DoublingMST

/-- **Doubling dimension of the whole space.**
Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), Definition 2.2, p.12 (PDF p.14): ddim(X), the doubling dimension of (X, d).

**Formalization Note.** `ddim d = ddimOn d univ`; it is the `ddim` of every `2^{O(ddim)}` bound.
The algorithm is never given it. -/
noncomputable def ddim {n : ℕ} (d : Fin n → Fin n → ℝ) : ℝ :=
  ddimOn d Finset.univ

end DoublingMST


