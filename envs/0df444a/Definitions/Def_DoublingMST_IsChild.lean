-- Prove2me | Definitions.Def_DoublingMST_IsChild
-- name    : DoublingMST_IsChild
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:31:33.599212+00:00
-- url     : https://prove2.me/theorems/15ce3d7a-c770-406c-8a43-f90edd582707
-- title:
--   Child relation (Definition 2.5)
-- statement:
--   For elements $u,v$ of the net hierarchy, $v$ is a **child** of $u$ if $\operatorname{lev}(v)=\operatorname{lev}(u)-1$ and $d(u,v)\le2^{\operatorname{lev}(u)+1}$.
-- source:
--   Höckendorff, Hommelsheim, Sohler, Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b39caaedcdac985f11ec23b5833ef4686c045f97ef13a21bdff2fbe759), Definition 2.5, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_DoublingMST_NetHierarchy

namespace DoublingMST

/-- **Child relation.**
Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), Definition 2.5, p.12 (PDF p.14): "Say v is a child of u, if (i) lev(v) = lev(u) − 1 and
(ii) d(u, v) ≤ 2^{lev(u)+1}."

Elements of the hierarchy are pairs `(u, ℓ) : Fin n × ℕ` with `ℓ ≤ L` and `u ∈ N ℓ`, where `ℓ` is
`lev`. `IsChild H a b`: both are elements, `lev b + 1 = lev a`, and `d(a, b) ≤ 2^{lev a + 1}`. -/
def IsChild {n : ℕ} {d : Fin n → Fin n → ℝ} (H : NetHierarchy d) (a b : Fin n × ℕ) : Prop :=
  a.2 ≤ topLevel d ∧ a.1 ∈ H.N a.2 ∧ b.2 ≤ topLevel d ∧ b.1 ∈ H.N b.2 ∧
    b.2 + 1 = a.2 ∧ d a.1 b.1 ≤ (2 : ℝ) ^ (a.2 + 1)

end DoublingMST


