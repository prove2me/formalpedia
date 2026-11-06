-- Prove2me | Definitions.Def_BinaryQueryLB_PhiW
-- name    : BinaryQueryLB_PhiW
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:45:56.07141+00:00
-- url     : https://prove2.me/theorems/8575d687-2d65-4a45-99eb-47964c23e699
-- title:
--   The radially extended function $\Phi_W$
-- statement:
--   For $W$ and $q\in\mathbb R^{2m}$,
--   $$
--   \Phi_W(q)=f_W(q)+b\,(\|q\|_2-1)_+,
--   $$
--   with $b=2a/\sqrt m$ and $(t)_+=\max\{t,0\}$. The radial term extends $f_W$ from the unit ball to the box without changing the minimum.
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), Definition 2.4, p.12

import Mathlib
import Definitions.Def_BinaryQueryLB_fW
import Definitions.Def_BinaryQueryLB_bConst

namespace BinaryQueryLB

/-- **The radially extended function `Φ_W` (Definition 2.4).** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), Definition 2.4, p.12:
"`Φ_W(q) = f_W(q) + b(∥q∥₂ − 1)_+`".

**Formalization Note.** `‖q‖` is the Euclidean norm of ℝ^{2m} (see `PtSpace`). -/
noncomputable def PhiW {m : ℕ} (W : Fin m → EuclideanSpace ℝ (Fin m)) (q : PtSpace m) : ℝ :=
  fW W q + bConst m * max (‖q‖ - 1) 0

end BinaryQueryLB


