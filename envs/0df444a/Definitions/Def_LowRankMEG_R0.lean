-- Prove2me | Definitions.Def_LowRankMEG_R0
-- name    : LowRankMEG_R0
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:51:19.330481+00:00
-- url     : https://prove2.me/theorems/08d575c3-a29f-4785-9ac9-6577e9264d55
-- title:
--   The radius $R_0$ of Theorem 5
-- statement:
--   The radius of the warm-start ball in Theorem 5 is
--   $$
--   R_0:=\min\Bigl\{\frac14\Bigl[2\beta+\Bigl(1+\frac{2\sqrt{2r^*}}{\lambda_{r^*}(X^*)}\Bigr)G\Bigr]^{-1}\delta,\ \frac G\beta\Bigr\}.
--   $$
-- source:
--   Garber & Kaplan, On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for Low-Rank Matrix Optimization, arXiv:2012.10469v2, Theorem 5, p.23

import Mathlib
import Definitions.Def_LowRankMEG_constA

namespace LowRankMEG

/-- **The radius of Theorem 5**, `R₀ := min{ (1/4) [2β + (1 + 2√(2r*)/λ_{r*}(X*)) G]⁻¹ δ, G/β }`.
Garber & Kaplan, *On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for
Low-Rank Matrix Optimization*, arXiv:2012.10469v2, Theorem 5, p.23. -/
noncomputable def R0 {n : ℕ} (β G δ : ℝ) (Xs : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  min (1 / 4 * (constA β G Xs)⁻¹ * δ) (G / β)

end LowRankMEG


