-- Prove2me | Definitions.Def_GeomDRSub_Alg1Run_draws
-- name    : GeomDRSub_Alg1Run_draws
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:11:21.152415+00:00
-- url     : https://prove2.me/theorems/892ffca1-abfd-4f63-821a-bbf57a2d489a
-- title:
--   One round's draws $(I_t,S_t,U_t)$
-- statement:
--   For a run and a round $t$, the triple $(I_t,S_t,U_t)$ of the coordinate draw, the uniform draw and the branch coin.
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Algorithm 1, step 2, p.20; Eq. (49), p.17

import Mathlib
import Definitions.Def_GeomDRSub_Alg1Run

namespace GeomDRSub

/-- **One round's draws `(I_t, S_t, U_t)`** of a run of Algorithm 1 (Aggarwal–Lu,
arXiv:2610.00545, step 2 of Algorithm 1, p.20, and Eq. (49), p.17). -/
def Alg1Run.draws {d : ℕ} {Ω : Type*} (R : Alg1Run d Ω) (t : ℕ) (ω : Ω) : Fin d × ℝ × ℝ :=
  (R.I t ω, R.S t ω, R.U t ω)

end GeomDRSub


