-- Prove2me | Definitions.Def_PoursoltaniRegret_Objective_Model
-- name    : PoursoltaniRegret_Objective_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:55:51.052759+00:00
-- url     : https://prove2.me/theorems/cdd1586b-a0a9-426a-afc3-c866ea43455d
-- title:
--   Objective uncertainty: primitive data and feasible decisions
-- statement:
--   Let $n_x,n_y,n_\zeta,m,r,s$ be finite dimensions. The primitive real matrices are $W\in\mathbb R^{r\times n_x}$, $P\in\mathbb R^{s\times n_\zeta}$, $A\in\mathbb R^{m\times n_x}$, $B\in\mathbb R^{m\times n_y}$ and $D\in\mathbb R^{n_y\times n_\zeta}$; their associated real vectors are $v,q,\psi,c,d$ of dimensions $r,s,m,n_x,n_y$. Define
--   $$X=\{x:Wx\le v\},\qquad U=\{\zeta:P\zeta\le q\},\qquad Y(x)=\{y:Ax+By\le\psi\},$$
--   and $d(\zeta)=D\zeta+d$. The profit of a feasible decision pair is $c^Tx+d(\zeta)^Ty$. The first-stage decision $x$ precedes observation of $\zeta$; recourse $y$ follows it. Variables are unrestricted real vectors except for these componentwise inequalities. No feasibility, boundedness, rank, or sign hypothesis is stored in the data.
--
--   This is the objective-uncertainty model underlying the regret problem. It builds on the published unrestricted-variable LP feasibility predicate: $Wx\le v$ is represented by $(-W)x\ge-v$, and $Ax+By\le\psi$ by $(-B)y\ge Ax-\psi$.
--
--   **Formalization Note** Vectors have type $\mathrm{Fin}(n)\to\mathbb R$; this indexes coordinates, not a finite set of scenarios. Zero-dimensional vector spaces are allowed, and nonempty feasible sets are required separately by the source assumptions.
-- source:
--   Poursoltani and Delage (2022), Adjustable Robust Optimization Reformulations of Two-Stage Worst-Case Regret Minimization Problems, Operations Research, https://doi.org/10.1287/opre.2021.2159; supplied source.pdf (dated July 10, 2020; printed page = PDF page); §3.2, Eqs. (8)–(10), p. 7; Assumption 1, p. 5

import Definitions.Def_ModernConvex_LPDuality_LinearProgram

open Matrix

namespace PoursoltaniRegret.Objective

structure Model (nx ny nz m r s : ℕ) where
  W : Matrix (Fin r) (Fin nx) ℝ
  v : Fin r → ℝ
  P : Matrix (Fin s) (Fin nz) ℝ
  q : Fin s → ℝ
  A : Matrix (Fin m) (Fin nx) ℝ
  B : Matrix (Fin m) (Fin ny) ℝ
  psi : Fin m → ℝ
  c : Fin nx → ℝ
  D : Matrix (Fin ny) (Fin nz) ℝ
  d : Fin ny → ℝ

variable {nx ny nz m r s : ℕ} (M : Model nx ny nz m r s)

noncomputable def Model.firstStage : Set (Fin nx → ℝ) :=
  {x | ModernConvex.LPDuality.PrimalFeasible (-M.W) (-M.v) x}

noncomputable def Model.uncertainty : Set (Fin nz → ℝ) :=
  {z | ModernConvex.LPDuality.PrimalFeasible (-M.P) (-M.q) z}

noncomputable def Model.recourse (x : Fin nx → ℝ) : Set (Fin ny → ℝ) :=
  {y | ModernConvex.LPDuality.PrimalFeasible (-M.B) (M.A *ᵥ x - M.psi) y}

noncomputable def Model.recourseCost (z : Fin nz → ℝ) : Fin ny → ℝ :=
  M.D *ᵥ z + M.d

noncomputable def Model.profit (x : Fin nx → ℝ) (z : Fin nz → ℝ)
    (y : Fin ny → ℝ) : ℝ :=
  M.c ⬝ᵥ x + M.recourseCost z ⬝ᵥ y

end PoursoltaniRegret.Objective


