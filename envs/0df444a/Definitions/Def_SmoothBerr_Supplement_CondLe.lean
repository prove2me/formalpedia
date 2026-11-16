-- Prove2me | Definitions.Def_SmoothBerr_Supplement_CondLe
-- name    : SmoothBerr_Supplement_CondLe
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:51:40.730256+00:00
-- url     : https://prove2.me/theorems/25cbb16e-7dd1-44a9-8062-cf528a3fed50
-- title:
--   Condition number at most $\kappa$: $\mathrm{cond}(A)\le\kappa$
-- statement:
--   The **condition number** of a square matrix $A$ is $\mathrm{cond}(A):=\sigma_{\max}(A)/\sigma_{\min}(A)$, the ratio of its largest and smallest singular values. The statement $\mathrm{cond}(A)\le\kappa$ means that $A$ is invertible and
--   $$
--   \sigma_{\max}(A)\le\kappa\,\sigma_{\min}(A).
--   $$
--   It defines the class of inputs of Theorem 4.3.
--
--   **Formalization Note** $\sigma_{\max}=\|A\|_2$ is the published `GaussianMatrix.specNorm` and $\sigma_{\min}$ the published `GaussianMatrix.sMin`. Invertibility is part of the predicate, because $\sigma_{\min}$ of a singular matrix is $0$ and the inequality alone would admit $A=0$.
-- source:
--   Dereziński, Mahoney, Meyer, Musco, From smoothed analysis to backward error: The power of adaptive perturbations (manuscript of 3 Nov 2026, STOC 2027 submission; sha256 9575cd20bc2c854eb092a4950988f7fbef8715adda344a1ba39489bc28b4e58d), §3, p.4 (cond(A) := σ_max(A)/σ_min(A))

import Mathlib
import Definitions.Def_GaussianMatrix_basic

open Matrix GaussianMatrix

namespace SmoothBerr.Supplement

/-- **Condition number at most `κ`** (Dereziński, Mahoney, Meyer, Musco, *From smoothed analysis
to backward error: The power of adaptive perturbations*, manuscript of 3 Nov 2026, sha256
9575cd20…, §3, p.4: `cond(A) := σ_max(A)/σ_min(A)`): `cond(A) ≤ κ` means `A` is invertible and
`σ_max(A) ≤ κ σ_min(A)`.

**Formalization Note** `σ_max = ‖A‖₂` is the published `GaussianMatrix.specNorm` and `σ_min` the
published `GaussianMatrix.sMin`. Invertibility is part of the predicate: `sMin` of a singular
matrix is `0`, so without it the singular matrix `A = 0` would satisfy `‖A‖₂ ≤ κ σ_min(A)`. -/
def CondLe {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (κ : ℝ) : Prop :=
  IsUnit A.det ∧ specNorm A ≤ κ * sMin A

end SmoothBerr.Supplement


