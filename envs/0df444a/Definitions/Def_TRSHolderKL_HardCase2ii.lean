-- Prove2me | Definitions.Def_TRSHolderKL_HardCase2ii
-- name    : TRSHolderKL_HardCase2ii
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:52:30.090992+00:00
-- url     : https://prove2.me/theorems/dc14c793-1b20-4b8d-bc86-823a5d7b09c5
-- title:
--   Hard case 2 (ii) of the nonconvex TRS
-- statement:
--   **Hard case 2 (ii)** (Table 1): $\lambda_1<0$, $b\perp\mathrm{Null}(A-\lambda_1I)$, $\lambda^*=-\lambda_1$ and $\|(A-\lambda_1I)^\dagger b\|<1$.
--
--   **Formalization Note** $\lambda^*$ is encoded as in hard case 1: the multiplier of some optimal solution.
-- source:
--   Jiang and Li, Hölderian error bounds and Kurdyka-Łojasiewicz inequality for the trust region subproblem, arXiv:1911.11955v2, Table 1, p.4

import Mathlib
import Definitions.Def_RBMSensitivity_E
import Definitions.Def_TRSHolderKL_S0
import Definitions.Def_TRSHolderKL_lam1
import Definitions.Def_TRSHolderKL_shiftLin
import Definitions.Def_TRSHolderKL_xbar
import Definitions.Def_TRSHolderKL_IsKKT
open RBMSensitivity (E)

namespace TRSHolderKL

/-- Hard case 2 (ii), Jiang and Li, arXiv:1911.11955v2, Table 1, p.4: `λ₁ < 0`,
`b ⊥ Null(A − λ₁I)`, `λ* = −λ₁` and `‖(A − λ₁I)†b‖ < 1`. `λ*` as in `HardCase1`. -/
def HardCase2ii {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : E n) : Prop :=
  lam1 A < 0 ∧ b ∈ (LinearMap.ker (shiftLin A))ᗮ ∧
  (∃ x ∈ S0 A b, ∃ lam : ℝ, IsKKT A b x lam ∧ lam = -lam1 A) ∧ ‖xbar A b‖ < 1

end TRSHolderKL


