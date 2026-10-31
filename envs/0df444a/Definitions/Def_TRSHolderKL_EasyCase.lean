-- Prove2me | Definitions.Def_TRSHolderKL_EasyCase
-- name    : TRSHolderKL_EasyCase
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:51:22.984348+00:00
-- url     : https://prove2.me/theorems/f82930c4-a22a-4d31-82e5-7cc5a95f9841
-- title:
--   The easy case of the nonconvex TRS
-- statement:
--   The **easy case** (Table 1): $\lambda_1<0$ and $b\not\perp\mathrm{Null}(A-\lambda_1I)$.
--
--   **Formalization Note** Table 1 is "for the nonconvex TRS, i.e., $\lambda_1<0$" (footnote 1: the categories are used only in the nonconvex case), so $\lambda_1<0$ is part of the definition. The table's parenthetical "(implies $\lambda^*>-\lambda_1$)" is a consequence, not a condition.
-- source:
--   Jiang and Li, Hölderian error bounds and Kurdyka-Łojasiewicz inequality for the trust region subproblem, arXiv:1911.11955v2, Table 1, p.4

import Mathlib
import Definitions.Def_RBMSensitivity_E
import Definitions.Def_TRSHolderKL_lam1
import Definitions.Def_TRSHolderKL_shiftLin
open RBMSensitivity (E)

namespace TRSHolderKL

/-- The easy case of the nonconvex TRS, Jiang and Li, arXiv:1911.11955v2, Table 1, p.4:
`λ₁ < 0` and `b ̸⊥ Null(A − λ₁I)`.

**Formalization Note.** The table is "for the nonconvex TRS, i.e., λ₁ < 0" (footnote 1: the
categories are used only in the nonconvex case), so `λ₁ < 0` is part of the definition. The
table's parenthetical "(implies λ* > −λ₁)" is a remark, not a condition. -/
def EasyCase {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : E n) : Prop :=
  lam1 A < 0 ∧ b ∉ (LinearMap.ker (shiftLin A))ᗮ

end TRSHolderKL


