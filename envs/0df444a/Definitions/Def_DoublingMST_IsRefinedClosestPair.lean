-- Prove2me | Definitions.Def_DoublingMST_IsRefinedClosestPair
-- name    : DoublingMST_IsRefinedClosestPair
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:37:04.381717+00:00
-- url     : https://prove2.me/theorems/d516054d-b687-48de-8ed6-39eb5a552832
-- title:
--   Refined closest pair, Lines 9–10 and 13–14 of Algorithm 2
-- statement:
--   For a pair $(u,v)$, a threshold $\theta$ and $K=\log_2(1/\epsilon)$: let $k$ be the largest integer with $0\le k\le\min\{K,\operatorname{lev}(u),\operatorname{lev}(v)\}$ such that $|D_{\operatorname{lev}(u)-k}(u)|\le\theta$ and $|D_{\operatorname{lev}(v)-k}(v)|\le\theta$. Then $(p,q)$ is a closest pair:
--
--   $$(p,q)\in\operatorname{argmin}_{p\in D_{\operatorname{lev}(u)-k}(u),\ q\in D_{\operatorname{lev}(v)-k}(v)}d(p,q).$$
--
--   **Formalization Note** Ties in the argmin are not broken.
-- source:
--   Höckendorff, Hommelsheim, Sohler, Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b39caaedcdac985f11ec23b5833ef4686c045f97ef13a21bdff2fbe759), Algorithm 2, Lines 9–10, 13–14, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_DoublingMST_descendants

namespace DoublingMST

/-- **Lines 9–10 (and 13–14) of Algorithm 2.**
Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), Algorithm 2, Lines 9–10 and 13–14, p.18 (PDF p.20): "let 0 ≤ k ≤ min{log(1/ϵ), lev(u),
lev(v)} be the largest integer, such that |D_{lev(u)−k}(u)|, |D_{lev(v)−k}(v)| ≤ γ; compute
(p, q) = argmin_{p∈D_{lev(u)−k}(u), q∈D_{lev(v)−k}(v)} d(p, q)" (with threshold τ_ℓ at Line 13).

`IsRefinedClosestPair H K θ u v p q`: with `K = log(1/ϵ)` and threshold `θ`, `k` is the largest
integer in `[0, min{K, lev u, lev v}]` with both descendant sets of size at most `θ`, and `(p, q)` is
a closest pair of `D_{lev u − k}(u) × D_{lev v − k}(v)`.

**Formalization Note.** `k ≤ lev u, lev v`, so `lev − k` is a true difference in `ℕ`. Ties in the
argmin are not broken: any closest pair is allowed. -/
def IsRefinedClosestPair {n : ℕ} {d : Fin n → Fin n → ℝ} (H : NetHierarchy d) (K : ℕ) (θ : ℝ)
    (u v : Fin n × ℕ) (p q : Fin n) : Prop :=
  ∃ k : ℕ, IsGreatest {j : ℕ | j ≤ min K (min u.2 v.2) ∧
      ((descendants H u (u.2 - j)).card : ℝ) ≤ θ ∧ ((descendants H v (v.2 - j)).card : ℝ) ≤ θ} k ∧
    p ∈ descendants H u (u.2 - k) ∧ q ∈ descendants H v (v.2 - k) ∧
    ∀ p' ∈ descendants H u (u.2 - k), ∀ q' ∈ descendants H v (v.2 - k), d p q ≤ d p' q'

end DoublingMST


