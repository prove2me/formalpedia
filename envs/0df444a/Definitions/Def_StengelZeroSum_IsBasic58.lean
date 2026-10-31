-- Prove2me | Definitions.Def_StengelZeroSum_IsBasic58
-- name    : StengelZeroSum_IsBasic58
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:03:40.517239+00:00
-- url     : https://prove2.me/theorems/fecfd6d6-50ce-4968-887e-445fe0a9d827
-- title:
--   Basic solutions of the inequality system (58)
-- statement:
--   Following the paper's convention for inequality systems ("A basic feasible solution to inequalities $Ax\le b$ (and $x\ge0$) is meant to be a basic feasible solution to the system $Ax+p=b$ (and $x,p\ge0$)"), a pair $(z,w)$ is **basic for (58)** if $(z,w,p)$ is basic for the equality system
--
--   $$
--   \begin{bmatrix} C & -\mathbf 1 & I\\ d^\top & -1 & \end{bmatrix}
--   \begin{pmatrix} z\\ w\\ p\end{pmatrix}
--   =\begin{pmatrix} d\\ 0\end{pmatrix},
--   $$
--
--   where $p=(d-Cz+\mathbf 1w,\ w-d^\top z)$ is the slack vector and the slack columns form the $(k+1)\times(k+1)$ identity.
--
--   **Formalization Note** Rows are indexed by $\iota\oplus\mathrm{Unit}$; columns by the $z$-columns, the $w$-column, and then the slack columns.
-- source:
--   von Stengel, Zero-Sum Games and Linear Programming Duality, arXiv:2205.11196v6, p.20 (convention for inequalities) and Theorem 8, eq. (58), p.21

import Mathlib
import Definitions.Def_StengelZeroSum_IsBasic

open Matrix

namespace StengelZeroSum

/-- `(z, w)` is **basic for the system (58)** in the paper's sense for inequalities,
von Stengel, *Zero-Sum Games and Linear Programming Duality*, arXiv:2205.11196v6, p.20:
"A basic feasible solution to inequalities Ax ≤ b (and x ≥ 0) is meant to be a basic feasible
solution to the system Ax + p = b (and x, p ≥ 0), which has full row rank."
For (58), `Cz − 1w ≤ d, d⊤z − w ≤ 0`, the equality system is
```
[ C   −1   I ] (z, w, p) = [ d ]
[ d⊤  −1     ]             [ 0 ]
```
with slack `p = (d − Cz + 1w, w − d⊤z)`, and `(z, w)` is basic when `(z, w, p)` is basic for
this matrix (`IsBasic`).

**Formalization Note** The `k + 1` rows are indexed by `ι ⊕ Unit`; the columns by
`(ι ⊕ Unit) ⊕ (ι ⊕ Unit)`: first the `z`-columns and the `w`-column, then the identity block of
slack columns. Equality of row indices is decided classically. -/
noncomputable def IsBasic58 {ι : Type*} [Fintype ι] (C : Matrix ι ι ℝ) (d : ι → ℝ) (z : ι → ℝ) (w : ℝ) :
    Prop :=
  IsBasic
    (Matrix.of fun (r : ι ⊕ Unit) (s : (ι ⊕ Unit) ⊕ (ι ⊕ Unit)) =>
      match r, s with
      | .inl i, .inl (.inl j) => C i j
      | .inl _, .inl (.inr _) => -1
      | .inr _, .inl (.inl j) => d j
      | .inr _, .inl (.inr _) => -1
      | r, .inr r' => haveI := Classical.decEq ι; if r = r' then 1 else 0 : Matrix (ι ⊕ Unit) ((ι ⊕ Unit) ⊕ (ι ⊕ Unit)) ℝ)
    (Sum.elim (Sum.elim z fun _ => w)
      (Sum.elim (fun i => d i - (C *ᵥ z) i + w) fun _ => w - d ⬝ᵥ z))

end StengelZeroSum


