-- Prove2me | Definitions.Def_PADMPriv_IsOptimal
-- name    : PADMPriv_IsOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:06:57.564768+00:00
-- url     : https://prove2.me/theorems/59ece666-f0fe-4a21-b7f3-e29abfad736f
-- title:
--   Optimal solution of model (1)
-- statement:
--   For $F:\mathbb R^p\to\mathbb R$, $g:\mathbb R^l\to\mathbb R$, $A\in\mathbb R^{m\times p}$, $B\in\mathbb R^{m\times l}$, $c\in\mathbb R^m$, consider the linearly constrained composite problem
--   $$
--   \min_{x\in\mathbb R^p,\ y\in\mathbb R^l}\ F(x)+g(y)\quad\text{s.t.}\quad Ax+By=c. \tag{1}
--   $$
--   A pair $(x,y)$ is an **optimal solution** of (1) if $Ax+By=c$ and $F(x)+g(y)\le F(x')+g(y')$ for every feasible pair $(x',y')$.
-- source:
--   Li–Lai–Weng, Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization, STOC 2027 submission (manuscript sha256 d58edbe0…0f3d), model (1), p.2

import Mathlib

namespace PADMPriv

/-- `(x, y)` is an optimal solution of model (1) of Li–Lai–Weng, *Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization*, STOC 2027 submission manuscript (sha256 d58edbe0…0f3d), p.2:
`min_{x ∈ ℝᵖ, y ∈ ℝˡ} F(x) + g(y)` subject to `Ax + By = c`. That is, `(x, y)` is feasible and
no feasible pair has a smaller objective value. -/
def IsOptimal {m p l : ℕ} (F : EuclideanSpace ℝ (Fin p) → ℝ) (g : EuclideanSpace ℝ (Fin l) → ℝ)
    (A : Matrix (Fin m) (Fin p) ℝ) (B : Matrix (Fin m) (Fin l) ℝ) (c : EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin p)) (y : EuclideanSpace ℝ (Fin l)) : Prop :=
  Matrix.toEuclideanLin A x + Matrix.toEuclideanLin B y = c ∧
    ∀ (x' : EuclideanSpace ℝ (Fin p)) (y' : EuclideanSpace ℝ (Fin l)),
      Matrix.toEuclideanLin A x' + Matrix.toEuclideanLin B y' = c → F x + g y ≤ F x' + g y'

end PADMPriv


