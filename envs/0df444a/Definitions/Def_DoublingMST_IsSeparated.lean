-- Prove2me | Definitions.Def_DoublingMST_IsSeparated
-- name    : DoublingMST_IsSeparated
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:28:21.056938+00:00
-- url     : https://prove2.me/theorems/df18d389-738b-44ee-9637-b577a5dddc35
-- title:
--   $t$-separated pair
-- statement:
--   A pair $(A,B)$ of subsets of $X$ is **$t$-separated** if $d(A,B)>t\cdot\max\{\operatorname{diam}(A),\operatorname{diam}(B)\}$.
-- source:
--   Höckendorff, Hommelsheim, Sohler, Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b39caaedcdac985f11ec23b5833ef4686c045f97ef13a21bdff2fbe759), §3, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_DoublingMST_diam
import Definitions.Def_DoublingMST_setDist

namespace DoublingMST

/-- **t-separated pair.**
Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), §3, p.13 (PDF p.15): "For two subsets A, B ⊆ X, we say a pair (A, B) is t-separated if
d(A, B) > t · max{diam(A), diam(B)}." -/
def IsSeparated {n : ℕ} (d : Fin n → Fin n → ℝ) (A B : Finset (Fin n)) (t : ℝ) : Prop :=
  t * max (diam d A) (diam d B) < setDist d A B

end DoublingMST


