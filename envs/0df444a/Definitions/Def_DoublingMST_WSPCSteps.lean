-- Prove2me | Definitions.Def_DoublingMST_WSPCSteps
-- name    : DoublingMST_WSPCSteps
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:35:28.642872+00:00
-- url     : https://prove2.me/theorems/a409d106-62e2-4a9c-8e6c-d5e8ffc34578
-- title:
--   Runs of Algorithm 1, $\mathrm{WSPC}(u,v)$
-- statement:
--   The recursive procedure **Algorithm 1** on a net hierarchy, with parameter $t$:
--
--   1. assume $\operatorname{lev}(u)\ge\operatorname{lev}(v)$ (exchange otherwise);
--   2. if $\{u,v\}$ is marked, return $\emptyset$; otherwise mark it;
--   3. if $d(u,v)>(2t+2)2^{\operatorname{lev}(u)}$, return $\{(u,v)\}$;
--   4. else if both levels are $0$: return $\emptyset$ if $u=v$ and $\{(u,v)\}$ if $u\ne v$;
--   5. else return $\bigcup_{u'\in C(u)}\mathrm{WSPC}(u',v)$.
--
--   The marks are global. This item is the relation "starting with marks $m$ and a stack of pending calls, a run of the procedure ends with marks $m'$ having returned the set of pairs `out`".
--
--   **Formalization Note** The recursive calls of step 5 are made in **any** order of $C(u)$; because of the marks the output can depend on that order, so every statement about the output quantifies over all runs. Elements are pairs (point, level); marks are unordered pairs of elements; returned pairs are ordered.
-- source:
--   Höckendorff, Hommelsheim, Sohler, Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b39caaedcdac985f11ec23b5833ef4686c045f97ef13a21bdff2fbe759), Algorithm 1, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_DoublingMST_children
open scoped Classical

namespace DoublingMST

/-- **Runs of Algorithm 1, WSPC(u, v).**
Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), Algorithm 1, p.14 (PDF p.16):
```
1  assume lev(u) ≥ lev(v) (exchange u and v otherwise)
2  if {u, v} is marked then
3      return ∅
4  mark {u, v}
5  if d(u, v) > (2t + 2)2^{lev(u)} then
6      return {(u, v)}
7  else if lev(u) = lev(v) = 0 and u = v then
8      return ∅
9  else if lev(u) = lev(v) = 0 and u ≠ v then
10     return {(u, v)}
11 else
12     return ⋃_{u′∈C(u)} WSPC(u′, v)
```
The marks are global to the whole computation.

`WSPCSteps H t m calls m' out` says: starting with the set of marks `m` and the stack of pending
calls `calls` (executed left to right, each call completely before the next), the computation can
end with marks `m'` having returned the pairs `out` (the union of all returned sets).

**Formalization Note.** Line 12 is the constructor `recurse`: the recursive calls `WSPC(u′, v)` for
`u′ ∈ C(u)` are pushed in front of the remaining calls, in the order of **any** duplicate-free list
`l` enumerating `C(u)`. Because of the marks, the returned set can depend on that order, so this is
a relation, and every statement about the output of Algorithm 1 quantifies over every run.
Elements are pairs `(point, level)`; the marks are unordered pairs of elements (`Sym2`); returned
pairs are ordered, with the first entry of the larger level (after Line 1). The comparison in
Line 5 is strict, as printed. -/
inductive WSPCSteps {n : ℕ} {d : Fin n → Fin n → ℝ} (H : NetHierarchy d) (t : ℝ) :
    Finset (Sym2 (Fin n × ℕ)) → List ((Fin n × ℕ) × (Fin n × ℕ)) →
    Finset (Sym2 (Fin n × ℕ)) → Finset ((Fin n × ℕ) × (Fin n × ℕ)) → Prop
  /-- No call pending. -/
  | done (m : Finset (Sym2 (Fin n × ℕ))) : WSPCSteps H t m [] m ∅
  /-- Line 1: exchange `u` and `v`. -/
  | swap {m m' out rest} {u v : Fin n × ℕ} : u.2 < v.2 →
      WSPCSteps H t m ((v, u) :: rest) m' out → WSPCSteps H t m ((u, v) :: rest) m' out
  /-- Lines 2–3: `{u, v}` is marked; return `∅`. -/
  | marked {m m' out rest} {u v : Fin n × ℕ} : v.2 ≤ u.2 → s(u, v) ∈ m →
      WSPCSteps H t m rest m' out → WSPCSteps H t m ((u, v) :: rest) m' out
  /-- Lines 4–6: mark; `d(u, v) > (2t + 2)2^{lev(u)}`; return `{(u, v)}`. -/
  | far {m m' out rest} {u v : Fin n × ℕ} : v.2 ≤ u.2 → s(u, v) ∉ m →
      (2 * t + 2) * (2 : ℝ) ^ u.2 < d u.1 v.1 →
      WSPCSteps H t (insert s(u, v) m) rest m' out →
      WSPCSteps H t m ((u, v) :: rest) m' (insert (u, v) out)
  /-- Lines 4, 7–8: mark; both levels `0` and `u = v`; return `∅`. -/
  | leafSame {m m' out rest} {u v : Fin n × ℕ} : v.2 ≤ u.2 → s(u, v) ∉ m →
      ¬ (2 * t + 2) * (2 : ℝ) ^ u.2 < d u.1 v.1 → u.2 = 0 → v.2 = 0 → u = v →
      WSPCSteps H t (insert s(u, v) m) rest m' out → WSPCSteps H t m ((u, v) :: rest) m' out
  /-- Lines 4, 9–10: mark; both levels `0` and `u ≠ v`; return `{(u, v)}`. -/
  | leafDistinct {m m' out rest} {u v : Fin n × ℕ} : v.2 ≤ u.2 → s(u, v) ∉ m →
      ¬ (2 * t + 2) * (2 : ℝ) ^ u.2 < d u.1 v.1 → u.2 = 0 → v.2 = 0 → u ≠ v →
      WSPCSteps H t (insert s(u, v) m) rest m' out →
      WSPCSteps H t m ((u, v) :: rest) m' (insert (u, v) out)
  /-- Lines 4, 11–12: mark; recurse into `WSPC(u′, v)` for `u′ ∈ C(u)`, in the order of `l`. -/
  | recurse {m m' out rest} {u v : Fin n × ℕ} (l : List (Fin n × ℕ)) : v.2 ≤ u.2 →
      s(u, v) ∉ m → ¬ (2 * t + 2) * (2 : ℝ) ^ u.2 < d u.1 v.1 → ¬ (u.2 = 0 ∧ v.2 = 0) →
      l.Nodup → l.toFinset = children H u →
      WSPCSteps H t (insert s(u, v) m) (l.map (fun u' => (u', v)) ++ rest) m' out →
      WSPCSteps H t m ((u, v) :: rest) m' out

end DoublingMST


