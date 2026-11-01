-- Prove2me | Definitions.Def_LowRankMEG_InitCond
-- name    : LowRankMEG_InitCond
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:50:27.208872+00:00
-- url     : https://prove2.me/theorems/bbbe876c-d672-4228-83b7-f81cf6b9d435
-- title:
--   The initialization condition (30)
-- statement:
--   For compact-form eigen-decompositions $V_X\Lambda_XV_X^\top$ of $X$ and $V_{X^*}\Lambda_{X^*}V_{X^*}^\top$ of $X^*$, with $r^*=\operatorname{rank}(X^*)$, condition (30) reads
--   $$
--   \operatorname{Tr}\bigl(X^*\log(X^*)-X^*V_X\log(\Lambda_X)V_X^\top\bigr)+\lambda_1(X^*)\log\Bigl(\frac n\varepsilon\Bigr)\bigl(r^*-\|V_{X^*}^\top V_X\|_F^2\bigr)+4\varepsilon\le R^2.
--   $$
--   It certifies a warm start from a possibly singular $X$.
--
--   **Formalization Note** The left side does not depend on the decompositions, and for $X,X^*\succeq0$ they exist, so stating the condition with $\exists$ loses nothing.
-- source:
--   Garber & Kaplan, On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for Low-Rank Matrix Optimization, arXiv:2012.10469v2, Lemma 4, Eq. (30), p.17

import Mathlib
import Definitions.Def_LowRankMEG_lam
import Definitions.Def_LowRankMEG_mlog
import Definitions.Def_LowRankMEG_frobNorm
import Definitions.Def_LowRankMEG_IsCompactEigen
open Matrix

namespace LowRankMEG

/-- **The initialization condition (30)**:
`Tr(X* log(X*) − X* V_X log(Λ_X) V_Xᵀ) + λ₁(X*) log(n/ε) (r* − ‖V_{X*}ᵀ V_X‖²_F) + 4ε ≤ R²`,
for compact-form eigen-decompositions `V_X Λ_X V_Xᵀ` of `X` and `V_{X*} Λ_{X*} V_{X*}ᵀ` of `X*`.
Garber & Kaplan, *On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for
Low-Rank Matrix Optimization*, arXiv:2012.10469v2, Lemma 4, Eq. (30), p.17.

**Formalization Note.** The left side does not depend on the decompositions, and for `X, X* ⪰ 0` such
decompositions exist, so `∃` and `∀` agree here. `X` may be singular: this is not `bregman`, whose
second argument is positive definite. `log (Λ_X i)` is the compact logarithm. -/
def InitCond {n : ℕ} (Xs X : Matrix (Fin n) (Fin n) ℝ) (ε R : ℝ) : Prop :=
  ∃ (VX : Matrix (Fin n) (Fin X.rank) ℝ) (ΛX : Fin X.rank → ℝ)
    (VXs : Matrix (Fin n) (Fin Xs.rank) ℝ) (ΛXs : Fin Xs.rank → ℝ),
    IsCompactEigen X VX ΛX ∧ IsCompactEigen Xs VXs ΛXs ∧
    (Xs * mlog Xs - Xs * (VX * diagonal (fun i => Real.log (ΛX i)) * VXᵀ)).trace
        + lam Xs 1 * Real.log ((n : ℝ) / ε) * ((Xs.rank : ℝ) - frobNorm (VXsᵀ * VX) ^ 2)
        + 4 * ε ≤ R ^ 2

end LowRankMEG


