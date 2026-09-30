-- Prove2me | Definitions.Def_NonconvexSplitting_ADMMKL_AugLagProd
-- name    : NonconvexSplitting_ADMMKL_AugLagProd
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T18:06:25.382979+00:00
-- url     : https://prove2.me/theorems/04dcaee3-3867-434c-a5ba-066e4b09875b
-- title:
--   $L_\beta$ as a function on the triple space $\mathbb R^n\times\mathbb R^m\times\mathbb R^m$
-- statement:
--   Let $\mathcal X:=\mathbb R^n\times\mathbb R^m\times\mathbb R^m$ with the Euclidean inner product
--   $$
--   \langle (x,y,z),(x',y',z')\rangle=\langle x,x'\rangle+\langle y,y'\rangle+\langle z,z'\rangle,\qquad \|(x,y,z)\|=\bigl(\|x\|^2+\|y\|^2+\|z\|^2\bigr)^{1/2}.
--   $$
--   The augmented Lagrangian is regarded as one function $L_\beta:\mathcal X\to(-\infty,+\infty]$, $(x,y,z)\mapsto L_\beta(x,y,z)$; its limiting subdifferential $\partial L_\beta(x,y,z)\subseteq\mathcal X$ is the one appearing in (35) and (40). The module also fixes the coordinate identification of $\mathbb R^{n+m+m}$ with $\mathcal X$ (first $n$ coordinates $x$, next $m$ coordinates $y$, last $m$ coordinates $z$), used to speak of $L_\beta$ being semi-algebraic.
--
--   **Formalization Note** $\mathcal X$ is the nested $L^2$ product `WithLp 2 (ℝⁿ × WithLp 2 (ℝᵐ × ℝᵐ))`, whose inner product is the sum of the three block inner products; `pack x y z` is the point $(x,y,z)$ and `augLagX h P M β (pack x y z)` is definitionally `augLag h P M β x y z`.
-- source:
--   Li & Pong, Global Convergence of Splitting Methods for Nonconvex Composite Optimization, arXiv:1407.0753v6, p. 5 (L_β); p. 14, (35) and (40), where L_β is treated as a function of (x, y, z)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_IsProxADMMSeq
open NonconvexSplitting.Shared

namespace NonconvexSplitting.ADMMKL

/-- The space of triples `(x, y, z) ∈ ℝⁿ × ℝᵐ × ℝᵐ` with the Euclidean inner product
`⟪(x, y, z), (x', y', z')⟫ = ⟪x, x'⟫ + ⟪y, y'⟫ + ⟪z, z'⟫`, hence the norm
`‖(x, y, z)‖ = (‖x‖² + ‖y‖² + ‖z‖²)^{1/2}`. It is built as nested `L²` products. -/
abbrev XYZ (n m : ℕ) : Type :=
  WithLp 2 (EuclideanSpace ℝ (Fin n) × WithLp 2 (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)))

/-- The triple `(x, y, z)` as a point of `XYZ n m`. -/
def pack {n m : ℕ} (x : EuclideanSpace ℝ (Fin n)) (y z : EuclideanSpace ℝ (Fin m)) : XYZ n m :=
  WithLp.toLp 2 (x, WithLp.toLp 2 (y, z))

/-- The augmented Lagrangian `L_β` of Li–Pong (p. 5) as a single function of the triple
`(x, y, z) ∈ XYZ n m`: `augLagX h P M β (pack x y z) = augLag h P M β x y z`. -/
noncomputable def augLagX {n m : ℕ} (h : EuclideanSpace ℝ (Fin n) → ℝ)
    (P : EuclideanSpace ℝ (Fin m) → EReal)
    (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (β : ℝ)
    (w : XYZ n m) : EReal :=
  augLag h P M β (WithLp.ofLp w).1 (WithLp.ofLp (WithLp.ofLp w).2).1
    (WithLp.ofLp (WithLp.ofLp w).2).2

/-- The coordinate identification of `ℝ^{n+m+m}` with `XYZ n m`: the first `n` coordinates of
`v` give `x`, the next `m` give `y`, and the last `m` give `z`. -/
def xyzOfCoords {n m : ℕ} (v : EuclideanSpace ℝ (Fin (n + m + m))) : XYZ n m :=
  pack (WithLp.toLp 2 fun i : Fin n => WithLp.ofLp v (Fin.castAdd m (Fin.castAdd m i)))
    (WithLp.toLp 2 fun j : Fin m => WithLp.ofLp v (Fin.castAdd m (Fin.natAdd n j)))
    (WithLp.toLp 2 fun j : Fin m => WithLp.ofLp v (Fin.natAdd (n + m) j))

end NonconvexSplitting.ADMMKL


