-- Prove2me | Definitions.Def_ParamSDPTraj_Dfeas
-- name    : ParamSDPTraj_Dfeas
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:12:33.500104+00:00
-- url     : https://prove2.me/theorems/fb859675-4feb-44f2-a4e1-e9ac6e9aa064
-- title:
--   Dual feasible set-valued map $\mathcal D(t)$
-- statement:
--   The **dual feasible set-valued map** sends $t$ to the set of matrices
--
--   $$\mathcal D(t)=\{Z\in\mathbb S^n\mid \exists y\in\mathbb R^m,\ \mathcal A^*(t)[y]+Z=C(t),\ Z\succeq 0\}.$$
--
--   The page prints $\mathcal A^*(t)[X]$ here, a slip for $\mathcal A^*(t)[y]$. As in Remark 2.1 of the paper, a dual point is referred to simply as a matrix $Z$.
-- source:
--   Bellon, Henrion, Kungurtsev, Mareček, Parametric Semidefinite Programming: Geometry of the Trajectory of Solutions, arXiv:2104.05445v3, §2.2, p.7; Remark 2.1, p.5

import Mathlib
import Definitions.Def_ParamSDPTraj_adjA

namespace ParamSDPTraj

/-- **Dual feasible set-valued map 𝒟.**
Bellon, Henrion, Kungurtsev, Mareček, *Parametric Semidefinite Programming: Geometry of the
Trajectory of Solutions*, arXiv:2104.05445v3, §2.2, p.7: "D(t) = {Z ∈ Sn | A∗(t)[X] + Z = C(t), y ∈ Rm, Z ⪰ 0}".

**Formalization Note** The printed `A∗(t)[X]` is a slip for `A∗(t)[y]`; the set consists of the
matrices Z for which some y ∈ ℝᵐ satisfies 𝒜*(t)[y] + Z = C(t) (Remark 2.1, p.5: a dual point is
referred to simply as a matrix Z). -/
def Dfeas {n m : ℕ} (A : Fin m → ℝ → Matrix (Fin n) (Fin n) ℝ) (C : ℝ → Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    Set (Matrix (Fin n) (Fin n) ℝ) :=
  {Z | (∃ y : Fin m → ℝ, adjA A t y + Z = C t) ∧ Z.PosSemidef}

end ParamSDPTraj


