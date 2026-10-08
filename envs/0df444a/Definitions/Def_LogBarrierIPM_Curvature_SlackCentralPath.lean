-- Prove2me | Definitions.Def_LogBarrierIPM_Curvature_SlackCentralPath
-- name    : LogBarrierIPM_Curvature_SlackCentralPath
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T01:12:22.105992+00:00
-- url     : https://prove2.me/theorems/146ef602-a593-4fb9-aabf-6ef644735f6d
-- title:
--   The central path of the dual pair $\mathrm{LP}(A,b,c)$, $\mathrm{DualLP}(A,b,c)$ in slack form, system (1)
-- statement:
--   Let $A$ be a real $m\times n$ matrix, $b\in\mathbb R^m$, $c\in\mathbb R^n$, and $N:=n+m$. The dual pair of linear programs in slack form is
--   $$\mathrm{LP}(A,b,c):\ \text{minimize }\langle c,x\rangle\ \text{ subject to } Ax+w=b,\ (x,w)\in\mathbb R^{n+m}_+,$$
--   $$\mathrm{DualLP}(A,b,c):\ \text{constraints } s-A^\top y=c,\ (s,y)\in\mathbb R^{n+m}_+ .$$
--   A primal-dual point is $z=(x,w,s,y)$ with $x,s\in\mathbb R^n$, $w,y\in\mathbb R^m$. For $\mu>0$, $z$ is the **point of the central path with parameter $\mu$** when it solves system (1):
--   $$Ax+w=b,\qquad s-A^\top y=c,\qquad \begin{pmatrix}xs\\ wy\end{pmatrix}=\mu e,\qquad x,w,y,s>0,$$
--   where $xs$, $wy$ are coordinatewise products and $e$ is the all-ones vector of $\mathbb R^N$. The **central path** is $\mu\mapsto(x^\mu,w^\mu,s^\mu,y^\mu)\in\mathbb R^{2N}$, and the **primal central path** is its projection $\mu\mapsto(x^\mu,w^\mu)\in\mathbb R^N$.
--
--   This module also fixes how a primal-dual point is read as a point of Euclidean space: the primal part as $(x,w)\in\mathbb R^N$ and the whole point as $(x,w,s,y)\in\mathbb R^{2N}$, in this order of blocks.
--
--   **Formalization Note** System (1) is the published definition `VanderbeiLP.CentralPath.IsCentralPathPoint A b (-c) μ x w y s` (Vanderbei's (17.6) for the max-form program with objective $-c$): its equation $A^\top y - z = -c$ with $z:=s$ is exactly $s-A^\top y=c$, and its products $x_jz_j=\mu$, $y_iw_i=\mu$ and positivity conditions are those of (1). Vanderbei's argument order is $(x,w,y,z)$; the paper's is $(x,w,s,y)$. Points of $\mathbb R^N$ and $\mathbb R^{2N}$ are `EuclideanSpace` vectors built by `Fin.append`, so angles and curvature use the Euclidean norm.
-- source:
--   Allamigeon, Benchimol, Gaubert, Joswig, Log-Barrier Interior Point Methods Are Not Strongly Polynomial, arXiv:1708.01544v2, p. 4, §2, LP(A,b,c), DualLP(A,b,c), system (1), central path and primal central path

import Mathlib
import Definitions.Def_VanderbeiLP_CentralPath_BarrierProblem

open Matrix

namespace LogBarrierIPM.Curvature

/-- A primal-dual point `z = (x, w, s, y) ∈ ℝ^n × ℝ^m × ℝ^n × ℝ^m` of the dual pair
`LP(A, b, c)`, `DualLP(A, b, c)` in slack form (§2, p. 4). -/
abbrev SlackPoint (n m : ℕ) := (Fin n → ℝ) × (Fin m → ℝ) × (Fin n → ℝ) × (Fin m → ℝ)

/-- `z = (x, w, s, y)` is the point of the central path with parameter `μ` of the dual pair
`LP(A, b, c)`: minimize `⟨c, x⟩` s.t. `Ax + w = b`, `(x, w) ≥ 0`, and `DualLP(A, b, c)`:
maximize `⟨b, y⟩` s.t. `s − Aᵀy = c`, `(s, y) ≥ 0`, i.e. `z` solves system (1) (p. 4):
`Ax + w = b`, `s − Aᵀy = c`, `xs = μe`, `wy = μe`, `x, w, y, s > 0`.
This is Vanderbei's system (17.6) for the max-form LP with objective `−c`, dual variables `y`
and dual slacks `z := s`. -/
def IsSlackCentralPathPoint {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (μ : ℝ) (z : SlackPoint n m) : Prop :=
  VanderbeiLP.CentralPath.IsCentralPathPoint A b (-c) μ z.1 z.2.1 z.2.2.2 z.2.2.1

/-- The primal part `(x, w) ∈ ℝ^N`, `N = n + m`, of a primal-dual point, as a point of Euclidean
space (the primal central path is the projection of the central path onto `(x, w)`, p. 4). -/
noncomputable def primalPoint {n m : ℕ} (z : SlackPoint n m) : EuclideanSpace ℝ (Fin (n + m)) :=
  WithLp.toLp 2 (Fin.append z.1 z.2.1)

/-- The whole primal-dual point `(x, w, s, y) ∈ ℝ^{2N}` as a point of Euclidean space. -/
noncomputable def primalDualPoint {n m : ℕ} (z : SlackPoint n m) :
    EuclideanSpace ℝ (Fin ((n + m) + (n + m))) :=
  WithLp.toLp 2 (Fin.append (Fin.append z.1 z.2.1) (Fin.append z.2.2.1 z.2.2.2))

end LogBarrierIPM.Curvature


