-- Prove2me | Definitions.Def_DRSub4633_Ypath
-- name    : DRSub4633_Ypath
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:05:36.361127+00:00
-- url     : https://prove2.me/theorems/a6f708c8-20f9-478f-8903-310dddac0c52
-- title:
--   The prefix paths $Y_i(t)=F(a(t),P_i^+)$
-- statement:
--   $$Y_i(t)=F(a(t),P_i^+),\qquad 0\le i\le m,$$
--   with $E(t)=Y_0(t)$ and $y(t)=Y_m(t)$.
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 4.1, Eq. (15), p.10

import Mathlib
import Definitions.Def_DRSub4633_resid
import Definitions.Def_DRSub4633_mergePt
import Definitions.Def_DRSub4633_aPath
import Definitions.Def_DRSub4633_Pplus

namespace DRSub4633

/-- **The prefix paths `Yᵢ(t) = F(a(t), P⁺ᵢ)`.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 4.1, Eq. (15), p.10; `E(t) =
Y₀(t)` and `y(t) = Y_m(t)`. -/
noncomputable def Ypath {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (i : ℕ) (t : ℝ) : ℝ :=
  resid f x (mergePt x (aPath x t) (Pplus x i))

end DRSub4633


