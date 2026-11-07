-- Prove2me | Definitions.Def_DoublingMST_diam
-- name    : DoublingMST_diam
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:25:53.851328+00:00
-- url     : https://prove2.me/theorems/125fe482-0124-4cab-941e-e0c11076c751
-- title:
--   Diameter $\operatorname{diam}(S)$
-- statement:
--   The **diameter** of a finite set $S\subseteq X$ is $\operatorname{diam}(S)=\max_{x,y\in S}d(x,y)$.
--
--   **Formalization Note** The empty set gets diameter $0$.
-- source:
--   Höckendorff, Hommelsheim, Sohler, Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b39caaedcdac985f11ec23b5833ef4686c045f97ef13a21bdff2fbe759), §2, p.11 (PDF p.13)

import Mathlib
open scoped Classical

namespace DoublingMST

/-- **Diameter of a finite set.**
Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), §2, p.11 (PDF p.13): "Denote the diameter of S to be diam(S) := max_{x,y∈S} d(x, y)."

**Formalization Note.** The maximum over the nonempty finite set `S × S`; the empty set gets
diameter `0` (the page's maximum is undefined there). -/
noncomputable def diam {n : ℕ} (d : Fin n → Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  if h : S.Nonempty then (S ×ˢ S).sup' (h.product h) (fun p => d p.1 p.2) else 0

end DoublingMST


