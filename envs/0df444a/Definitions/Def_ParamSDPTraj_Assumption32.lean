-- Prove2me | Definitions.Def_ParamSDPTraj_Assumption32
-- name    : ParamSDPTraj_Assumption32
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:13:17.999285+00:00
-- url     : https://prove2.me/theorems/6ecb641a-23c6-4da4-be69-038dc3e9b668
-- title:
--   Assumption 3.2 (strict feasibility)
-- statement:
--   **Assumption 3.2** on $T$: for every $t\in T$ both problems are strictly feasible. There is a matrix $X\succ 0$ with $\mathcal A(t)[X]=b(t)$, and there are $y\in\mathbb R^m$ and a matrix $Z\succ 0$ with $\mathcal A^*(t)[y]+Z=C(t)$.
-- source:
--   Bellon, Henrion, Kungurtsev, Mareček, Parametric Semidefinite Programming: Geometry of the Trajectory of Solutions, arXiv:2104.05445v3, Assumption 3.2, p.12, with Definition 2.3, p.5

import Mathlib
import Definitions.Def_ParamSDPTraj_opA
import Definitions.Def_ParamSDPTraj_adjA

namespace ParamSDPTraj

/-- **Assumption 3.2 (strict feasibility).**
Bellon, Henrion, Kungurtsev, Mareček, *Parametric Semidefinite Programming: Geometry of the
Trajectory of Solutions*, arXiv:2104.05445v3, Assumption 3.2, p.12: "For every t ∈ T, problem (Pt) and its dual (Dt) are strictly
feasible", with Definition 2.3, p.5: "there exists a matrix X ≻ 0 satisfying A[X] = b … there
exist y ∈ Rm and a matrix Z ≻ 0 satisfying A∗[y] + Z = C". -/
def Assumption32 {n m : ℕ} (T : Set ℝ) (A : Fin m → ℝ → Matrix (Fin n) (Fin n) ℝ)
    (b : ℝ → Fin m → ℝ) (C : ℝ → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ t ∈ T,
    (∃ X : Matrix (Fin n) (Fin n) ℝ, opA A t X = b t ∧ X.PosDef) ∧
    (∃ (y : Fin m → ℝ) (Z : Matrix (Fin n) (Fin n) ℝ), adjA A t y + Z = C t ∧ Z.PosDef)

end ParamSDPTraj


