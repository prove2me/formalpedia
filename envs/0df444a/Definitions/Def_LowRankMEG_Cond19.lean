-- Prove2me | Definitions.Def_LowRankMEG_Cond19
-- name    : LowRankMEG_Cond19
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:51:38.722611+00:00
-- url     : https://prove2.me/theorems/7fe86ec1-9df6-4f59-ab05-b6db0fb8ed7a
-- title:
--   Condition (19)
-- statement:
--   Condition (19) reads
--   $$
--   \sqrt{B(X^*,X)}\le\frac1{\sqrt2}\Bigl[2\beta+\Bigl(1+\frac{2\sqrt{2r^*}}{\lambda_{r^*}(X^*)}\Bigr)G\Bigr]^{-1}\Bigl(\delta-\frac1\eta\log\frac{\varepsilon_-}{\varepsilon}+\frac{2\varepsilon}{\eta}-2\xi\Bigr).
--   $$
--   It says how close to $X^*$ the point $X$ must be for one low-rank step to approximate the exact step within $2\varepsilon$.
-- source:
--   Garber & Kaplan, On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for Low-Rank Matrix Optimization, arXiv:2012.10469v2, Eq. (19), p.15

import Mathlib
import Definitions.Def_LowRankMEG_bregman
import Definitions.Def_LowRankMEG_constA

namespace LowRankMEG

/-- **Condition (19)**:
`√B(X*, X) ≤ (1/√2) [2β + (1 + 2√(2r*)/λ_{r*}(X*)) G]⁻¹ (δ − (1/η) log(ε₋/ε) + 2ε/η − 2ξ)`.
Garber & Kaplan, *On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for
Low-Rank Matrix Optimization*, arXiv:2012.10469v2, Eq. (19), p.15.

**Formalization Note.** `εm` is `ε₋`. Every statement has `0 < η`, `0 < ε`, `0 < εm`, and a positive
definite `X`. -/
def Cond19 {n : ℕ} (β G δ : ℝ) (Xs : Matrix (Fin n) (Fin n) ℝ) (η εm ε ξ : ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Real.sqrt (bregman Xs X) ≤
    1 / Real.sqrt 2 * (constA β G Xs)⁻¹ *
      (δ - 1 / η * Real.log (εm / ε) + 2 * ε / η - 2 * ξ)

end LowRankMEG


