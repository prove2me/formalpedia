-- Prove2me | Definitions.Def_GeomDRSub_Alg1Run_Y
-- name    : GeomDRSub_Alg1Run_Y
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:15:56.710215+00:00
-- url     : https://prove2.me/theorems/7d3de175-746e-4290-b568-1ad6b884accc
-- title:
--   Query point $Y_t$ of a run
-- statement:
--   For a run and a round $t$, the query point $Y_t$ is the point $u_{I_t,S_t}$ if $U_t<[h_\zeta(x_t)]_{I_t}$ and $\ell_{I_t,S_t}$ otherwise, where the path points are built from the current state $x_t$.
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Algorithm 1, step 2, p.20; Eq. (49), p.17

import Mathlib
import Definitions.Def_GeomDRSub_Alg1Run
import Definitions.Def_GeomDRSub_queryPt

namespace GeomDRSub

/-- **The query point `Y_t`** of a run of Algorithm 1 (Aggarwal–Lu, arXiv:2610.00545, step 2 of
Algorithm 1, p.20, and Eq. (49), p.17): `Y_t = queryPt ζ x_t I_t S_t U_t`, the point `u_{I_t,S_t}`
or `ℓ_{I_t,S_t}` built from the state `x_t`. -/
noncomputable def Alg1Run.Y {d : ℕ} {Ω : Type*} (R : Alg1Run d Ω) (ζ : ℝ) (t : ℕ) (ω : Ω) :
    EuclideanSpace ℝ (Fin d) :=
  queryPt ζ (R.x t ω) (R.I t ω) (R.S t ω) (R.U t ω)

end GeomDRSub


