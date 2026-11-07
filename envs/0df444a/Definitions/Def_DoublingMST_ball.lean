-- Prove2me | Definitions.Def_DoublingMST_ball
-- name    : DoublingMST_ball
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:24:13.521809+00:00
-- url     : https://prove2.me/theorems/1e05eef2-409e-4261-8257-bd1955e8978b
-- title:
--   Closed ball $B(x,r)$
-- statement:
--   For a point $x$ and a real $r$, the **ball** is $B(x,r)=\{y\in X: d(x,y)\le r\}$ (closed).
-- source:
--   Höckendorff, Hommelsheim, Sohler, Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b39caaedcdac985f11ec23b5833ef4686c045f97ef13a21bdff2fbe759), §2, p.11 (PDF p.13)

import Mathlib
open scoped Classical

namespace DoublingMST

/-- **Closed ball.**
Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), §2, p.11 (PDF p.13): "For a point x ∈ X and r > 0, define the ball centered at x with
radius r to be B(x, r) := {y ∈ X : d(x, y) ≤ r}."

**Formalization Note.** A `Finset` of `Fin n`; defined for every real `r` (statements use `r > 0`). -/
noncomputable def ball {n : ℕ} (d : Fin n → Fin n → ℝ) (x : Fin n) (r : ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun y => d x y ≤ r

end DoublingMST


