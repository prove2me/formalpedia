-- Prove2me | Definitions.Def_LowRankMEG_gammaConst
-- name    : LowRankMEG_gammaConst
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:50:26.991037+00:00
-- url     : https://prove2.me/theorems/11f72b08-d5ae-45ab-a012-986f8d9b2c3b
-- title:
--   The constant $\gamma$ of Lemma 6
-- statement:
--   With $r^*=\operatorname{rank}(X^*)$,
--   $$
--   \gamma=\sqrt2\Bigl(2\beta+\frac{2\sqrt{2r^*}}{\lambda_{r^*}(X^*)}G\Bigr).
--   $$
-- source:
--   Garber & Kaplan, On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for Low-Rank Matrix Optimization, arXiv:2012.10469v2, Lemma 6, p.21

import Mathlib
import Definitions.Def_LowRankMEG_lam

namespace LowRankMEG

/-- **The constant** `γ = √2 (2β + (2√(2r*)/λ_{r*}(X*)) G)`, with `r* = rank(X*)`.
Garber & Kaplan, *On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for
Low-Rank Matrix Optimization*, arXiv:2012.10469v2, Lemma 6, p.21. -/
noncomputable def gammaConst {n : ℕ} (β G : ℝ) (Xs : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Real.sqrt 2 * (2 * β + (2 * Real.sqrt (2 * (Xs.rank : ℝ)) / lam Xs Xs.rank) * G)

end LowRankMEG


