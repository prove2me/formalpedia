-- Prove2me | Definitions.Def_ParamSDPTraj_LICQ
-- name    : ParamSDPTraj_LICQ
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:11:45.837103+00:00
-- url     : https://prove2.me/theorems/b899b256-3972-4102-a8b5-3144ae1f8618
-- title:
--   Linear independence constraint qualification
-- statement:
--   **LICQ** holds on $T$ if the $m$ matrices $A_1(t),\dots,A_m(t)$ are linearly independent for every $t\in T$. For symmetric matrices this makes $\mathcal A(t)$ surjective onto $\mathbb R^m$.
-- source:
--   Bellon, Henrion, Kungurtsev, Mareček, Parametric Semidefinite Programming: Geometry of the Trajectory of Solutions, arXiv:2104.05445v3, Assumption 3.1, p.12

import Mathlib

namespace ParamSDPTraj

/-- **LICQ.**
Bellon, Henrion, Kungurtsev, Mareček, *Parametric Semidefinite Programming: Geometry of the
Trajectory of Solutions*, arXiv:2104.05445v3, Assumption 3.1, p.12: "The m matrices {Ai(t)}i=1,...,m are linearly independent in Sn for
every t ∈ T, so that the linear operator A(t) is surjective for every t ∈ T". -/
def LICQ {n m : ℕ} (T : Set ℝ) (A : Fin m → ℝ → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ t ∈ T, LinearIndependent ℝ (fun i => A i t)

end ParamSDPTraj


