-- Prove2me | Definitions.Def_BirkhoffGlobalSection_MovingFrameAlgebra
-- name    : BirkhoffGlobalSection_MovingFrameAlgebra
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-29T17:02:14.366421+00:00
-- url     : https://prove2.me/theorems/dc0c79ad-2e4f-4e73-94e2-116dfe266e81
-- title:
--   Complex-linear determinant and symplectic matrix conventions
-- statement:
--   For a real linear map on $\mathbb R^4\simeq\mathbb C^2$, write $g(z)=A_gz+C_g\bar z$. This module fixes the matrices $A_g$, $C_g$, their conjugates, and the complex-linear determinant
--
--   $$d(g)=\det_{\mathbb C} A_g.$$
--
--   It also fixes the symplectic matrix $\Omega=\operatorname{diag}(J_0,J_0)$ with $J_0=\begin{pmatrix}0&1\\-1&0\end{pmatrix}$, the squared complex Euclidean norm on $\mathbb C^2$, and, for a real $2\times2$ matrix $m$, the scalar $p(m)=(m_{00}+m_{11}+i(m_{10}-m_{01}))/2$.
--
--   These are conventions used to transport graph determinant angles through a periodic symplectic frame. The formulas are extracted from Mazecto's accepted proof of homogeneous graph-angle transport; this module contains only definitions.
-- source:
--   Definitions extracted from Mazecto, accepted Prove2Me submission 893234ef-5ec2-4f4b-b415-f79ec1030002 for HryniewiczCriterion.homogeneous_graph_angle_transport (f880a9bf-1521-4b02-a828-1c90ceda0bb1), https://prove2.me/theorems/f880a9bf-1521-4b02-a828-1c90ceda0bb1. Context: HWZ, Ann. Math.148(1998), equations (3.35)-(3.39), https://doi.org/10.2307/120994.

import Definitions.Def_HryniewiczCriterion_GraphAngle
import Mathlib.Analysis.Complex.Polynomial.Basic

open Complex

namespace HryniewiczCriterion

noncomputable section

def omegaMat : Matrix (Fin 4) (Fin 4) ℝ := !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0]


def cA (g : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![⟨(g 0 0 + g 1 1) / 2, (g 1 0 - g 0 1) / 2⟩, ⟨(g 0 2 + g 1 3) / 2, (g 1 2 - g 0 3) / 2⟩;
     ⟨(g 2 0 + g 3 1) / 2, (g 3 0 - g 2 1) / 2⟩, ⟨(g 2 2 + g 3 3) / 2, (g 3 2 - g 2 3) / 2⟩]

/-- The anti-linear part `C` (`g z = A z + C z̄`). -/

def cC (g : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![⟨(g 0 0 - g 1 1) / 2, (g 1 0 + g 0 1) / 2⟩, ⟨(g 0 2 - g 1 3) / 2, (g 1 2 + g 0 3) / 2⟩;
     ⟨(g 2 0 - g 3 1) / 2, (g 3 0 + g 2 1) / 2⟩, ⟨(g 2 2 - g 3 3) / 2, (g 3 2 + g 2 3) / 2⟩]

/-- The complex conjugate `C̄` of the anti-linear part. -/

def cCb (g : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![⟨(g 0 0 - g 1 1) / 2, -((g 1 0 + g 0 1) / 2)⟩, ⟨(g 0 2 - g 1 3) / 2, -((g 1 2 + g 0 3) / 2)⟩;
     ⟨(g 2 0 - g 3 1) / 2, -((g 3 0 + g 2 1) / 2)⟩, ⟨(g 2 2 - g 3 3) / 2, -((g 3 2 + g 2 3) / 2)⟩]

/-- `d(g) = det_ℂ (cA g)`. -/

def cdet (g : Matrix (Fin 4) (Fin 4) ℝ) : ℂ := (cA g).det


def nsq (v : Fin 2 → ℂ) : ℝ := normSq (v 0) + normSq (v 1)


def polarC (m : Matrix (Fin 2) (Fin 2) ℝ) : ℂ := ⟨(m 0 0 + m 1 1) / 2, (m 1 0 - m 0 1) / 2⟩


end

end HryniewiczCriterion


