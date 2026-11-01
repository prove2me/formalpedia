-- Prove2me | Definitions.Def_LowRankMEG_InitCond31
-- name    : LowRankMEG_InitCond31
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:50:19.341203+00:00
-- url     : https://prove2.me/theorems/08f57f6f-f506-4976-a376-2d04f5887d3a
-- title:
--   The initialization condition (31)
-- statement:
--   For a compact-form eigen-decomposition $V_X\Lambda_XV_X^\top$ of $X$, with $r^*=\operatorname{rank}(X^*)$, condition (31) reads
--   $$
--   \operatorname{Tr}\bigl(X^*\log(X^*)-X^*V_X\log(\Lambda_X)V_X^\top\bigr)+\frac{2\lambda_1(X^*)}{\lambda_{r^*}(X^*)^2}\log\Bigl(\frac n\varepsilon\Bigr)\|X^*-X\|_F^2+4\varepsilon\le R^2.
--   $$
--   It replaces (30) when $\operatorname{rank}(X)=\operatorname{rank}(X^*)$.
-- source:
--   Garber & Kaplan, On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for Low-Rank Matrix Optimization, arXiv:2012.10469v2, Lemma 4, Eq. (31), p.17

import Mathlib
import Definitions.Def_LowRankMEG_lam
import Definitions.Def_LowRankMEG_mlog
import Definitions.Def_LowRankMEG_frobNorm
import Definitions.Def_LowRankMEG_IsCompactEigen
open Matrix

namespace LowRankMEG

/-- **The initialization condition (31)**:
`Tr(X* log(X*) − X* V_X log(Λ_X) V_Xᵀ) + (2λ₁(X*)/λ_{r*}(X*)²) log(n/ε) ‖X* − X‖²_F + 4ε ≤ R²`,
for a compact-form eigen-decomposition `V_X Λ_X V_Xᵀ` of `X`.
Garber & Kaplan, *On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for
Low-Rank Matrix Optimization*, arXiv:2012.10469v2, Lemma 4, Eq. (31), p.17.

**Formalization Note.** As in `InitCond`, the left side does not depend on the decomposition, and `X`
may be singular. -/
def InitCond31 {n : ℕ} (Xs X : Matrix (Fin n) (Fin n) ℝ) (ε R : ℝ) : Prop :=
  ∃ (VX : Matrix (Fin n) (Fin X.rank) ℝ) (ΛX : Fin X.rank → ℝ),
    IsCompactEigen X VX ΛX ∧
    (Xs * mlog Xs - Xs * (VX * diagonal (fun i => Real.log (ΛX i)) * VXᵀ)).trace
        + 2 * lam Xs 1 / lam Xs Xs.rank ^ 2 * Real.log ((n : ℝ) / ε) * frobNorm (Xs - X) ^ 2
        + 4 * ε ≤ R ^ 2

end LowRankMEG


