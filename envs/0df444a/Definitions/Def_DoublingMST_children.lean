-- Prove2me | Definitions.Def_DoublingMST_children
-- name    : DoublingMST_children
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:33:09.988227+00:00
-- url     : https://prove2.me/theorems/43f0f7a4-849d-401e-9eb1-67f45edd342c
-- title:
--   Children $C(u)$ (Definition 2.5)
-- statement:
--   $C(u)$ is the finite set of children of the element $u$.
-- source:
--   Höckendorff, Hommelsheim, Sohler, Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b39caaedcdac985f11ec23b5833ef4686c045f97ef13a21bdff2fbe759), Definition 2.5, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_DoublingMST_IsChild
open scoped Classical

namespace DoublingMST

/-- **The children C(u).**
Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), Definition 2.5, p.12 (PDF p.14): "Denote by C(u) the set of children of u."

The finite set of elements `b` with `IsChild H a b`. -/
noncomputable def children {n : ℕ} {d : Fin n → Fin n → ℝ} (H : NetHierarchy d) (a : Fin n × ℕ) :
    Finset (Fin n × ℕ) :=
  ((Finset.univ : Finset (Fin n)) ×ˢ Finset.range (topLevel d + 1)).filter fun b => IsChild H a b

end DoublingMST


