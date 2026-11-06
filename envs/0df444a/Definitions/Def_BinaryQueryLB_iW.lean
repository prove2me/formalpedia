-- Prove2me | Definitions.Def_BinaryQueryLB_iW
-- name    : BinaryQueryLB_iW
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:45:49.209986+00:00
-- url     : https://prove2.me/theorems/8427bf27-4b27-4c82-8d9c-23f06c01323f
-- title:
--   The least active index $i_W$
-- statement:
--   For $q=(x,z)\in\mathbb R^{2m}$, the least active index is
--   $$
--   i_W(q)=\min\{i\in[m]:\ a x_i+\langle w_i,z\rangle=f_W(q)\}.
--   $$
--   For $y\in X$ the paper writes $i_W(y)$ for $i_W(\bar y/R)$.
--
--   **Formalization Note** The value is an optional index: it is undefined only when no piece is active, which happens only for $m=0$. Indices are ordered naturally from $0$.
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), §2.3, p.12

import Mathlib
import Definitions.Def_BinaryQueryLB_fW
open Classical

namespace BinaryQueryLB

/-- **The least active index `i_W`.** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), §2.3, p.12: "let
`i_W(y) = min{i ∈ [m] : a x_i + ⟨w_i, z⟩ = f_W(q)}`", where `q = (x, z) = ȳ/R`.

`iW W q` is `some i` for the least index `i` whose piece attains `f_W(q)`, and `none` if no piece
does (which happens only for `m = 0`).

**Formalization Note.** Stated as a function of `q`; the paper's `i_W(y)` is
`iW W (R⁻¹ • ybar d y)`. Indices are `Fin m` (from `0`) with their natural order. -/
noncomputable def iW {m : ℕ} (W : Fin m → EuclideanSpace ℝ (Fin m)) (q : PtSpace m) :
    Option (Fin m) :=
  if h : (Finset.univ.filter fun i => aConst * xPart q i + inner ℝ (W i) (zPart q) = fW W q).Nonempty
  then some (Finset.min' _ h) else none

end BinaryQueryLB


