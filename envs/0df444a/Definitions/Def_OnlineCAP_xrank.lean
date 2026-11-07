-- Prove2me | Definitions.Def_OnlineCAP_xrank
-- name    : OnlineCAP_xrank
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:23:43.296202+00:00
-- url     : https://prove2.me/theorems/236cdc46-b366-4908-b91e-2d76c44a01e7
-- title:
--   x-rank of a coordinate
-- statement:
--   Let $x_{(0)}<x_{(1)}<\dots<x_{(m-1)}$ be the distinct x-coordinates of the points of $P$. The **x-rank** of a real $u$ is the number of these coordinates smaller than $u$; the rank of $x_{(i)}$ is $i$. Ranks index the leaves of the range tree.
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), §4.1.2, p.17

import Mathlib

namespace OnlineCAP

/-- **x-rank in the range tree.** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), §4.1.2, p.17 (PDF p.17): "We first start with the sorted
list of points … Consider the entire point set P projected to the x-axis and construct a range
tree on this set of points."

`xrank P u` is the number of distinct x-coordinates of points of `P` that are smaller than `u`;
on the x-coordinates `x₍₀₎ < ⋯ < x₍m−1₎` of `P` it is the position `i` of `x₍ᵢ₎`. -/
noncomputable def xrank (P : Finset (ℝ × ℝ)) (u : ℝ) : ℕ := by
  classical
  exact ((P.image Prod.fst).filter (fun v => v < u)).card

end OnlineCAP


