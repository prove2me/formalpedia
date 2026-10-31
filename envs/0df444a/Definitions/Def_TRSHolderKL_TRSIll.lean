-- Prove2me | Definitions.Def_TRSHolderKL_TRSIll
-- name    : TRSHolderKL_TRSIll
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:52:27.29511+00:00
-- url     : https://prove2.me/theorems/422b62a9-96f0-4b63-8c1d-3495e1cb9dc5
-- title:
--   The TRS-ill case (24)
-- statement:
--   The TRS is in the **TRS-ill case** if
--   $$
--   \lambda_1\le0,\qquad b\in\mathrm{Range}(A-\lambda_1I),\qquad \|(A-\lambda_1I)^\dagger b\|=1 .
--   $$
--   This is exactly the situation in which the Hölderian error bound modulus is $1/4$ and the KL exponent is $3/4$; in every other instance they are $1/2$.
-- source:
--   Jiang and Li, Hölderian error bounds and Kurdyka-Łojasiewicz inequality for the trust region subproblem, arXiv:1911.11955v2, display (24), p.14

import Mathlib
import Definitions.Def_RBMSensitivity_E
import Definitions.Def_TRSHolderKL_lam1
import Definitions.Def_TRSHolderKL_shiftLin
import Definitions.Def_TRSHolderKL_xbar
open RBMSensitivity (E)

namespace TRSHolderKL

/-- The TRS-ill case, Jiang and Li, arXiv:1911.11955v2, display (24), p.14:
`λ₁ ≤ 0`, `b ∈ Range(A − λ₁I)` and `‖(A − λ₁I)†b‖ = 1`. -/
def TRSIll {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : E n) : Prop :=
  lam1 A ≤ 0 ∧ b ∈ LinearMap.range (shiftLin A) ∧ ‖xbar A b‖ = 1

end TRSHolderKL


