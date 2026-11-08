-- Prove2me | Definitions.Def_SampleRemoval_ols
-- name    : SampleRemoval_ols
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:06:58.646124+00:00
-- url     : https://prove2.me/theorems/a2627a31-d17e-46c6-9ff8-a731dedd08c9
-- title:
--   Weighted least-squares estimate $\beta(w)=G(w)^{-1}g(w)$
-- statement:
--   For observations $(x_i,y_i)\in\mathbb R^d\times\mathbb R$ and a weight vector $w$ with positive definite Gram matrix $G(w)\succ0$, the **weighted least-squares estimate** is
--
--   $$
--   \beta(w)=G(w)^{-1}g(w),\qquad G(w)=\sum_i w_i x_ix_i^{\top},\quad g(w)=\sum_i w_ix_iy_i .
--   $$
--
--   For a set $S$ of observations, $\beta(S)=\beta(\mathbf 1_S)$ is the ordinary least-squares fit on $S$; $\beta([n])$ is the fit on the full sample. Sample-removal audits ask how a linear functional of $\beta$ moves as weight is removed.
--
--   **Formalization Note** Mathlib's matrix inverse is total and returns $0$ on a singular matrix, so the Lean value is $0$ when $G(w)$ is singular. The paper defines $\beta(w)$ only when $G(w)\succ0$, and every statement of the mission that uses the estimate assumes or derives positive definiteness (the feasible set contains it).
-- source:
--   Xu, Gao, Hu, Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares, STOC 2027 submission (manuscript sha256 dcd33acebc1ccdc626c7ee41bfabc29795abe2e1cd9267d8cbd66d98f81c4b26), §2, Weighted least squares, p.3 (PDF p.5)

import Mathlib
import Definitions.Def_SampleRemoval_gram
import Definitions.Def_SampleRemoval_moment

set_option autoImplicit false

open Matrix

namespace SampleRemoval

/-- The weighted least-squares estimate `β(w) = G(w)⁻¹ g(w)` (Xu, Gao, Hu, *Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares*, STOC 2027 submission (manuscript sha256 dcd33ace…), §2, "Weighted least
squares", p.3).

**Formalization Note** Mathlib's matrix inverse is total: it returns `0` on a singular matrix,
so `ols x y w = 0` when `G(w)` is singular. The paper defines `β(w)` only "whenever
`G(w) ≻ 0`"; every statement of the mission that uses `ols x y w` assumes or derives
`(gram x w).PosDef` (in particular the feasible set `feasible` contains it). -/
noncomputable def ols {n d : ℕ} (x : Fin n → Fin d → ℝ) (y : Fin n → ℝ) (w : Fin n → ℝ) :
    Fin d → ℝ :=
  (gram x w)⁻¹ *ᵥ moment x y w

end SampleRemoval


