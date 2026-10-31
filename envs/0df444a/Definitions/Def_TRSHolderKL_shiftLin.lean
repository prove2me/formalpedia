-- Prove2me | Definitions.Def_TRSHolderKL_shiftLin
-- name    : TRSHolderKL_shiftLin
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:50:37.439018+00:00
-- url     : https://prove2.me/theorems/a989cc63-f5c7-41b9-9adb-84a670d5f93c
-- title:
--   The shifted matrix $A-\lambda_1 I$ as a linear map
-- statement:
--   The linear map $x\mapsto(A-\lambda_1I)x$ on $\mathbb R^n$. $\mathrm{Null}(A-\lambda_1I)$ is its kernel (the eigenspace of the smallest eigenvalue) and $\mathrm{Range}(A-\lambda_1I)$ its range; both enter the case distinctions of Table 1 and the TRS-ill condition (24).
-- source:
--   Jiang and Li, Hölderian error bounds and Kurdyka-Łojasiewicz inequality for the trust region subproblem, arXiv:1911.11955v2, pp.3–4

import Mathlib
import Definitions.Def_RBMSensitivity_E
import Definitions.Def_TRSHolderKL_lam1
open RBMSensitivity (E)

namespace TRSHolderKL

/-- The linear map `x ↦ (A − λ₁I)x` on `ℝⁿ`, Jiang and Li, arXiv:1911.11955v2, pp.3–4.
`Null(A − λ₁I)` is its kernel and `Range(A − λ₁I)` its range. -/
noncomputable def shiftLin {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : E n →ₗ[ℝ] E n :=
  Matrix.toEuclideanLin (A - lam1 A • (1 : Matrix (Fin n) (Fin n) ℝ))

end TRSHolderKL


