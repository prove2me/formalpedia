-- Prove2me | Definitions.Def_DoublingMST_setDist
-- name    : DoublingMST_setDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:25:55.563588+00:00
-- url     : https://prove2.me/theorems/ab661908-7386-44e7-9670-d2e58af4d271
-- title:
--   Distance $d(A,B)$ between two sets
-- statement:
--   For nonempty $A,B\subseteq X$, $d(A,B)=\min_{x\in A,\,y\in B}d(x,y)$.
--
--   **Formalization Note** If either set is empty the value is $0$; it is only used for nonempty sets.
-- source:
--   Höckendorff, Hommelsheim, Sohler, Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b39caaedcdac985f11ec23b5833ef4686c045f97ef13a21bdff2fbe759), §2, p.12 (PDF p.14)

import Mathlib
open scoped Classical

namespace DoublingMST

/-- **Distance between two finite sets.**
Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), §2, p.12 (PDF p.14): "d(S, T) := min_{x∈S,y∈T} d(x, y) as the distance between two sets S
and T."

**Formalization Note.** The minimum over the nonempty finite set `A × B`; if either set is empty
the value is `0`. It is used only for nonempty sets (Definition 3.1 requires them). -/
noncomputable def setDist {n : ℕ} (d : Fin n → Fin n → ℝ) (A B : Finset (Fin n)) : ℝ :=
  if h : A.Nonempty ∧ B.Nonempty then (A ×ˢ B).inf' (h.1.product h.2) (fun p => d p.1 p.2) else 0

end DoublingMST


