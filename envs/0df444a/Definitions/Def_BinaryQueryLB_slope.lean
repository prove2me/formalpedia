-- Prove2me | Definitions.Def_BinaryQueryLB_slope
-- name    : BinaryQueryLB_slope
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:31.665544+00:00
-- url     : https://prove2.me/theorems/05eddddc-42c4-4bbf-829d-566093e8c2f0
-- title:
--   The slope $v_i(W)=(ae_i,w_i)$
-- statement:
--   For an index $i\in[m]$ and a row $w\in\mathbb R^m$, the slope is $(a e_i,w)\in\mathbb R^{2m}$, where $e_i$ is the $i$-th standard basis vector and $a=\tfrac12$. For a matrix $W$ with rows $w_1,\dots,w_m$, the slope of piece $i$ is $v_i(W)=(ae_i,w_i)$.
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), Definition 2.4, p.12

import Mathlib
import Definitions.Def_VRAccelCLT_stack
import Definitions.Def_BinaryQueryLB_aConst
import Definitions.Def_BinaryQueryLB_PtSpace

namespace BinaryQueryLB

/-- **The slope `v_i(W) = (a e_i, w_i)` (Definition 2.4).** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), Definition 2.4, p.12: "define
the slopes `v_i(W) = (a e_i, w_i) ∈ R^{2m}`".

`slope i w = (a e_i, w)`; the slope of piece `i` of the matrix `W` is `slope i (W i)`.

**Formalization Note.** The pair is the platform's `VRAccelCLT.stack` (first block `Sum.inl`). -/
noncomputable def slope {m : ℕ} (i : Fin m) (w : EuclideanSpace ℝ (Fin m)) : PtSpace m :=
  VRAccelCLT.stack (WithLp.toLp 2 fun k => if k = i then aConst else 0) w

end BinaryQueryLB


