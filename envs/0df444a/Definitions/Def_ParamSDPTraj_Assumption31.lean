-- Prove2me | Definitions.Def_ParamSDPTraj_Assumption31
-- name    : ParamSDPTraj_Assumption31
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:15:41.710848+00:00
-- url     : https://prove2.me/theorems/bda74159-66a3-45d2-a5c4-657f7f20de05
-- title:
--   Assumption 3.1 (LICQ and uniform boundedness of $\mathcal A$)
-- statement:
--   **Assumption 3.1** on $T$: LICQ holds, and $\mathcal A(t)$ and its pseudo-inverse have uniformly bounded norm.
-- source:
--   Bellon, Henrion, Kungurtsev, Mareček, Parametric Semidefinite Programming: Geometry of the Trajectory of Solutions, arXiv:2104.05445v3, Assumption 3.1, p.12

import Mathlib
import Definitions.Def_ParamSDPTraj_LICQ
import Definitions.Def_ParamSDPTraj_UniformBound

namespace ParamSDPTraj

/-- **Assumption 3.1 (LICQ and uniform boundedness of 𝒜).**
Bellon, Henrion, Kungurtsev, Mareček, *Parametric Semidefinite Programming: Geometry of the
Trajectory of Solutions*, arXiv:2104.05445v3, Assumption 3.1, p.12. -/
def Assumption31 {n m : ℕ} (T : Set ℝ) (A : Fin m → ℝ → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  LICQ T A ∧ UniformBound T A

end ParamSDPTraj


