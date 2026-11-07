-- Prove2me | Definitions.Def_DoublingMST_descendants
-- name    : DoublingMST_descendants
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:33:39.511694+00:00
-- url     : https://prove2.me/theorems/26a2314a-32ed-41ba-92cf-160871803992
-- title:
--   Descendants $D_k(u)$ (Definition 2.6)
-- statement:
--   $v$ is a **descendant** of $u$ if $v=u$ or $v$ is a child of a descendant of $u$. $D_k(u)\subseteq N_k$ is the set of descendants of $u$ at level $k$ (as points).
--
--   In particular $D_{\operatorname{lev}(u)}(u)=\{u\}$ and $D_{\operatorname{lev}(u)-1}(u)=C(u)$; for $k>\operatorname{lev}(u)$ the set is empty.
-- source:
--   Höckendorff, Hommelsheim, Sohler, Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b39caaedcdac985f11ec23b5833ef4686c045f97ef13a21bdff2fbe759), Definition 2.6, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_DoublingMST_IsChild
open scoped Classical

namespace DoublingMST

/-- **Descendants at a level, D_k(u).**
Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), Definition 2.6, p.12 (PDF p.14): "Say v is a descendant of u, if either (i) v = u, or
(ii) there exists w, such that w is a descendant of u and v is a child of w. For ℓ ≤ lev(u),
denote by D_ℓ(u) ⊆ N_ℓ the set of descendants of u at level ℓ".

`descendants H a k` is the set of points `v` such that the element `(v, k)` is reached from `a`
by finitely many child steps (`Relation.ReflTransGen (IsChild H)`).

**Formalization Note.** The descendant relation is the reflexive-transitive closure of the child
relation, exactly Definition 2.6. For `k > lev a` the set is empty; `D_{lev u}(u) = {u}` and
`D_{lev u − 1}(u) = C(u)` (as points) for an element `u`. -/
noncomputable def descendants {n : ℕ} {d : Fin n → Fin n → ℝ} (H : NetHierarchy d)
    (a : Fin n × ℕ) (k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun v => Relation.ReflTransGen (IsChild H) a (v, k)

end DoublingMST


