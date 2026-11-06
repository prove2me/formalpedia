-- Prove2me | Definitions.Def_BinaryQueryLB_AdvState
-- name    : BinaryQueryLB_AdvState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:43:09.384612+00:00
-- url     : https://prove2.me/theorems/b0bae723-def8-4cf7-9cbc-2d99f4c8a85e
-- title:
--   State of the adversary
-- statement:
--   The adversary of §3.1 keeps a set $P_i\subseteq\tau\mathbb B_m$ of possible values for each row $w_i$, and a committed index $j(y)\in[m]$ for every point $y$ queried so far. A state is the pair (row sets, committed indices), with "no index" for points not yet queried.
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), §3.1, p.16

import Mathlib

namespace BinaryQueryLB

/-- **State of the adversary.** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), §3.1, p.16: "The adversary keeps a set `P_i ⊆ τB_m` of possible
values for each row `w_i` … In addition, the adversary records a committed index `j(y) ∈ [m]` for
every point `y` queried so far".

A state is a pair: the row sets `P : Fin m → Set ℝ^m` and the committed indices
`J : ℝ^d → Option (Fin m)` (`none` for points not yet queried), with `m = d / 2`. -/
abbrev AdvState (d : ℕ) : Type :=
  (Fin (d / 2) → Set (EuclideanSpace ℝ (Fin (d / 2)))) × (EuclideanSpace ℝ (Fin d) → Option (Fin (d / 2)))

end BinaryQueryLB


