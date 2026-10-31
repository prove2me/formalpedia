-- Prove2me | Definitions.Def_ParamSDPTraj_Pfeas
-- name    : ParamSDPTraj_Pfeas
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:13:19.393653+00:00
-- url     : https://prove2.me/theorems/a988e8c6-719f-405e-a7bd-f23039e57394
-- title:
--   Primal feasible set-valued map $\mathcal P(t)$
-- statement:
--   The **primal feasible set-valued map** sends $t$ to
--
--   $$\mathcal P(t)=\{X\in\mathbb S^n\mid \mathcal A(t)[X]=b(t),\ X\succeq 0\}.$$
--
--   **Formalization Note** Positive semidefiniteness in Lean includes symmetry, so $X\in\mathbb S^n$ needs no separate clause.
-- source:
--   Bellon, Henrion, Kungurtsev, Mareček, Parametric Semidefinite Programming: Geometry of the Trajectory of Solutions, arXiv:2104.05445v3, §2.2, p.7

import Mathlib
import Definitions.Def_ParamSDPTraj_opA

namespace ParamSDPTraj

/-- **Primal feasible set-valued map 𝒫.**
Bellon, Henrion, Kungurtsev, Mareček, *Parametric Semidefinite Programming: Geometry of the
Trajectory of Solutions*, arXiv:2104.05445v3, §2.2, p.7: "P(t) = {X ∈ Sn | A(t)[X] = b(t), X ⪰ 0}".

**Formalization Note** `Matrix.PosSemidef` includes symmetry (over ℝ, Hermitian = symmetric), so
X ∈ Sⁿ needs no separate clause. -/
def Pfeas {n m : ℕ} (A : Fin m → ℝ → Matrix (Fin n) (Fin n) ℝ) (b : ℝ → Fin m → ℝ) (t : ℝ) :
    Set (Matrix (Fin n) (Fin n) ℝ) :=
  {X | opA A t X = b t ∧ X.PosSemidef}

end ParamSDPTraj


