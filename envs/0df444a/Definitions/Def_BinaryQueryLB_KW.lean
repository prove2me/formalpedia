-- Prove2me | Definitions.Def_BinaryQueryLB_KW
-- name    : BinaryQueryLB_KW
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:45:33.867197+00:00
-- url     : https://prove2.me/theorems/419487c9-7ded-4548-b4aa-02fe68e76d1d
-- title:
--   The hull $K_W$ of the slopes
-- statement:
--   For a matrix $W$, $K_W=\operatorname{conv}\{v_1(W),\dots,v_m(W)\}\subseteq\mathbb R^{2m}$, the convex hull of the slopes.
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), §2.3, p.13

import Mathlib
import Definitions.Def_BinaryQueryLB_slope

namespace BinaryQueryLB

/-- **The hull `K_W = conv{v_1(W), …, v_m(W)}`.** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), §2.3, p.13: "let
`K_W = conv{v_1(W), . . . , v_m(W)}`". -/
def KW {m : ℕ} (W : Fin m → EuclideanSpace ℝ (Fin m)) : Set (PtSpace m) :=
  convexHull ℝ (Set.range fun i => slope i (W i))

end BinaryQueryLB


