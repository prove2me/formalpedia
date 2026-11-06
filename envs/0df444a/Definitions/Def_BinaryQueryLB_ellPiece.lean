-- Prove2me | Definitions.Def_BinaryQueryLB_ellPiece
-- name    : BinaryQueryLB_ellPiece
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:34.514249+00:00
-- url     : https://prove2.me/theorems/e8def844-c188-4ab3-8cf5-52eeced02683
-- title:
--   Value $\ell_i(w)$ of piece $i$ with row $w$
-- statement:
--   For $q=(x,z)\in\mathbb R^{2m}$, $i\in[m]$ and $w\in\mathbb R^m$, $\ell_i(w)=a x_i+\langle w,z\rangle$ is the value of piece $i$ at $q$ when its row is $w$. It is an affine function of the unknown row.
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), §3.1, p.16

import Mathlib
import Definitions.Def_BinaryQueryLB_xPart
import Definitions.Def_BinaryQueryLB_zPart
import Definitions.Def_BinaryQueryLB_aConst

namespace BinaryQueryLB

/-- **The value `ℓ_i(w)` of piece `i` at `q` with row `w`.** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), §3.1, p.16: "For `i ∈ [m]` let
`ℓ_i(w) = a x_i + ⟨w, z⟩` be the value of piece `i` at `q` when its row is `w`." -/
noncomputable def ellPiece {m : ℕ} (q : PtSpace m) (i : Fin m) (w : EuclideanSpace ℝ (Fin m)) : ℝ :=
  aConst * xPart q i + inner ℝ w (zPart q)

end BinaryQueryLB


