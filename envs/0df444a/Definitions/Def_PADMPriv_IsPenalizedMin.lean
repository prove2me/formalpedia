-- Prove2me | Definitions.Def_PADMPriv_IsPenalizedMin
-- name    : PADMPriv_IsPenalizedMin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:07:08.330698+00:00
-- url     : https://prove2.me/theorems/876cb911-be73-492c-9425-cb7529982a15
-- title:
--   Minimizer of the penalized problem (16)
-- statement:
--   For $F$, $g$, $A$, $B$, $c$ as in model (1) and $\beta>0$, a pair $(\hat x,\hat y)$ minimizes the **penalized problem** (16) if
--   $$
--   (\hat x,\hat y)\in \operatorname*{arg\,min}_{(x,y)\in\mathbb R^p\times\mathbb R^l}\Big\{F(x)+g(y)+\frac{\beta}{4}\|Ax+By-c\|_2^2\Big\}.
--   $$
--   By Theorem 3.1 such minimizers correspond to the fixed points $u_\star = (A\hat x-B\hat y+c)/2$ of $T_F$; note the factor $\beta/4$ (not $\beta/2$).
-- source:
--   Li–Lai–Weng, Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization, STOC 2027 submission (manuscript sha256 d58edbe0…0f3d), Eq. (16), p.7

import Mathlib

namespace PADMPriv

/-- `(x, y)` minimizes the penalized problem (16) of Li–Lai–Weng, *Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization*, STOC 2027 submission manuscript (sha256 d58edbe0…0f3d), p.7:
`(x, y) ∈ argmin_{(x, y) ∈ ℝᵖ × ℝˡ} {F(x) + g(y) + (β/4)‖Ax + By − c‖₂²}`. -/
def IsPenalizedMin {m p l : ℕ} (β : ℝ) (F : EuclideanSpace ℝ (Fin p) → ℝ)
    (g : EuclideanSpace ℝ (Fin l) → ℝ) (A : Matrix (Fin m) (Fin p) ℝ)
    (B : Matrix (Fin m) (Fin l) ℝ) (c : EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin p)) (y : EuclideanSpace ℝ (Fin l)) : Prop :=
  ∀ (x' : EuclideanSpace ℝ (Fin p)) (y' : EuclideanSpace ℝ (Fin l)),
    F x + g y + β / 4 * ‖Matrix.toEuclideanLin A x + Matrix.toEuclideanLin B y - c‖ ^ 2 ≤
      F x' + g y' + β / 4 * ‖Matrix.toEuclideanLin A x' + Matrix.toEuclideanLin B y' - c‖ ^ 2

end PADMPriv


