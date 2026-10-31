-- Prove2me | Definitions.Def_TRSHolderKL_HardCase1
-- name    : TRSHolderKL_HardCase1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:51:51.468135+00:00
-- url     : https://prove2.me/theorems/f047e24f-fdf2-4a31-a31b-29888da4a9b9
-- title:
--   Hard case 1 of the nonconvex TRS
-- statement:
--   **Hard case 1** (Table 1): $\lambda_1<0$, $b\perp\mathrm{Null}(A-\lambda_1I)$ and $\lambda^*>-\lambda_1$, where $\lambda^*$ is the Lagrange multiplier of an optimal solution.
--
--   **Formalization Note** "$\lambda^*$" is encoded as: some $x^*\in S_0$ and $\lambda^*$ satisfy the KKT conditions. For $\lambda_1<0$ every optimal solution has norm one and $A+\lambda^*I\succeq0$ forces $\lambda^*\ge-\lambda_1>0$; the multiplier is the same for all optimal solutions, so "some" and "every" agree.
-- source:
--   Jiang and Li, Hölderian error bounds and Kurdyka-Łojasiewicz inequality for the trust region subproblem, arXiv:1911.11955v2, Table 1, p.4

import Mathlib
import Definitions.Def_RBMSensitivity_E
import Definitions.Def_TRSHolderKL_S0
import Definitions.Def_TRSHolderKL_lam1
import Definitions.Def_TRSHolderKL_shiftLin
import Definitions.Def_TRSHolderKL_IsKKT
open RBMSensitivity (E)

namespace TRSHolderKL

/-- Hard case 1, Jiang and Li, arXiv:1911.11955v2, Table 1, p.4: `λ₁ < 0`,
`b ⊥ Null(A − λ₁I)` and `λ* > −λ₁`.

**Formalization Note.** `λ*` is the Lagrange multiplier of an optimal solution: some
`x* ∈ S₀` and `λ*` satisfy the KKT conditions. For `λ₁ < 0` the multiplier is the same for
every optimal solution, so "some" and "every" agree. -/
def HardCase1 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : E n) : Prop :=
  lam1 A < 0 ∧ b ∈ (LinearMap.ker (shiftLin A))ᗮ ∧
  ∃ x ∈ S0 A b, ∃ lam : ℝ, IsKKT A b x lam ∧ -lam1 A < lam

end TRSHolderKL


