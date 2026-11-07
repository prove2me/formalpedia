-- Prove2me | Definitions.Def_DoublingMST_MinDistGtOne
-- name    : DoublingMST_MinDistGtOne
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:27:14.354352+00:00
-- url     : https://prove2.me/theorems/40626297-d73e-4a7d-b3ab-0994c24cce62
-- title:
--   Minimum interpoint distance greater than 1
-- statement:
--   The **minimum interpoint distance of $X$ is greater than $1$**: $d(x,y)>1$ for all distinct $x,y$. This is the standing assumption of §2.1, kept through §§3–4.
-- source:
--   Höckendorff, Hommelsheim, Sohler, Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b39caaedcdac985f11ec23b5833ef4686c045f97ef13a21bdff2fbe759), §2.1, p.12 (PDF p.14)

import Mathlib
open scoped Classical

namespace DoublingMST

/-- **Minimum interpoint distance greater than 1.**
Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), §2.1, p.12 (PDF p.14): "Without loss of generality, assume the minimum interpoint distance
of X is greater than 1". A standing assumption of §2.1 and of §§3–4. -/
def MinDistGtOne {n : ℕ} (d : Fin n → Fin n → ℝ) : Prop :=
  ∀ x y, x ≠ y → 1 < d x y

end DoublingMST


