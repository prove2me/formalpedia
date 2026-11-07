-- Prove2me | Definitions.Def_OnlineCAP_zvec
-- name    : OnlineCAP_zvec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:23:45.156566+00:00
-- url     : https://prove2.me/theorems/48d667b8-3d3b-4266-b72b-2071eb9ae7a2
-- title:
--   The thresholded doubled vector z, eq. (2)
-- statement:
--   For a fractional vector $x$ on a point set $P$ with $n=|P|$,
--   $$z_p=\begin{cases}0,& x_p<1/(2n),\\ \min\{1,2x_p\},& x_p\ge1/(2n).\end{cases}$$
--   This is eq. (2), applied to $x^t$ at every time step of Algorithm 2.
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), §4.1.2, eq. (2), p.16; Algorithm 2, p.18

import Mathlib

namespace OnlineCAP

/-- **The thresholded doubled vector `z`.** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), §4.1.2, eq. (2), p.16 (PDF p.16), and
Algorithm 2, line 5, p.18:
`z_p = 0` if `x_p < 1/(2n)`, and `z_p = min{1, 2 x_p}` if `x_p ≥ 1/(2n)`, where `n = |P|`.

**Formalization Note.** `x` is a vector on the points of `P` (the paper's `x^t`); the time index
is dropped because `z^t` depends only on `x^t`. -/
noncomputable def zvec (P : Finset (ℝ × ℝ)) (x : ↥P → ℝ) (p : ↥P) : ℝ :=
  if x p < 1 / (2 * (P.card : ℝ)) then 0 else min 1 (2 * x p)

end OnlineCAP


