-- Prove2me | Definitions.Def_DRSub4633_S0path
-- name    : DRSub4633_S0path
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:05:42.702141+00:00
-- url     : https://prove2.me/theorems/ba872e32-c524-41b2-9a39-551f3edc42c7
-- title:
--   The path $S_0(t)=F(a(t),\mathbf 0_L)$
-- statement:
--   $$S_0(t)=F(a(t),\mathbf 0_L).$$
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 4.1, Eq. (15), p.10

import Mathlib
import Definitions.Def_DRSub4633_resid
import Definitions.Def_DRSub4633_mergePt
import Definitions.Def_DRSub4633_aPath

namespace DRSub4633

/-- **The path `S₀(t) = F(a(t), 0_L)`.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 4.1, Eq. (15), p.10. -/
noncomputable def S0path {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (t : ℝ) : ℝ :=
  resid f x (mergePt x (aPath x t) 0)

end DRSub4633


