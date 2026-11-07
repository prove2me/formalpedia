-- Prove2me | Definitions.Def_DoublingMST_IsMetric
-- name    : DoublingMST_IsMetric
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:24:18.540194+00:00
-- url     : https://prove2.me/theorems/f9f27479-bfcb-4ddf-98de-4481193d3646
-- title:
--   Metric on $n$ points
-- statement:
--   A function $d:\{0,\dots,n-1\}^2\to\mathbb R$ is a **metric** if $d(x,y)=0$ exactly when $x=y$, $d(x,y)=d(y,x)$, and $d(x,z)\le d(x,y)+d(y,z)$ for all points. Nonnegativity follows.
--
--   This is the input metric space $(X,d)$ of the paper, with the points numbered.
--
--   **Formalization Note** The points are `Fin n` and $d$ is a plain function (Lean's own metric on `Fin n` is unrelated). The paper's standing assumption $|X|\ge2$ is a separate hypothesis of each theorem.
-- source:
--   Höckendorff, Hommelsheim, Sohler, Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b39caaedcdac985f11ec23b5833ef4686c045f97ef13a21bdff2fbe759), §2, p.11 (PDF p.13)

import Mathlib
open scoped Classical

namespace DoublingMST

/-- **A metric on `n` points.**
Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), §2, p.11 (PDF p.13): "Consider a metric space (X, d) with |X| ≥ 2."

`IsMetric d` says that `d : Fin n → Fin n → ℝ` vanishes exactly on the diagonal, is symmetric and
satisfies the triangle inequality; nonnegativity follows.

**Formalization Note.** The points are `Fin n`; `d` is a plain function, not a `MetricSpace`
instance (the instance on `Fin n` is already the discrete metric). The standing `|X| ≥ 2` is a
separate hypothesis `2 ≤ n` of every statement. -/
def IsMetric {n : ℕ} (d : Fin n → Fin n → ℝ) : Prop :=
  (∀ x y, d x y = 0 ↔ x = y) ∧ (∀ x y, d x y = d y x) ∧ (∀ x y z, d x z ≤ d x y + d y z)

end DoublingMST


