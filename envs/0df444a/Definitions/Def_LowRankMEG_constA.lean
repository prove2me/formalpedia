-- Prove2me | Definitions.Def_LowRankMEG_constA
-- name    : LowRankMEG_constA
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:50:24.308912+00:00
-- url     : https://prove2.me/theorems/2beb374c-e0e3-4044-bac3-f68234810694
-- title:
--   The constant $2\beta+(1+2\sqrt{2r^*}/\lambda_{r^*}(X^*))G$
-- statement:
--   With $r^*=\operatorname{rank}(X^*)$, this is the constant
--   $$
--   2\beta+\Bigl(1+\frac{2\sqrt{2r^*}}{\lambda_{r^*}(X^*)}\Bigr)G
--   $$
--   that appears in condition (19) and in the radius $R_0$ of Theorem 5.
-- source:
--   Garber & Kaplan, On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for Low-Rank Matrix Optimization, arXiv:2012.10469v2, Eq. (19), p.15; Theorem 5, p.23

import Mathlib
import Definitions.Def_LowRankMEG_lam

namespace LowRankMEG

/-- **The constant** `2β + (1 + 2√(2r*)/λ_{r*}(X*)) G`, with `r* = rank(X*)`.
Garber & Kaplan, *On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for
Low-Rank Matrix Optimization*, arXiv:2012.10469v2, Eq. (19), p.15, and Theorem 5, p.23. The square root covers `2r*`. -/
noncomputable def constA {n : ℕ} (β G : ℝ) (Xs : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  2 * β + (1 + 2 * Real.sqrt (2 * (Xs.rank : ℝ)) / lam Xs Xs.rank) * G

end LowRankMEG


