-- Prove2me | Definitions.Def_QiFixedDesign_Concentration_Hat
-- name    : QiFixedDesign_Concentration_Hat
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:59:05.86959+00:00
-- url     : https://prove2.me/theorems/8e326438-fa56-466b-8f95-7f0503001320
-- title:
--   Hat matrix and leverage scores
-- statement:
--   The hat matrix of a real $N\times p$ matrix $X$ is $H=X(X^T X)^{-1}X^T$. Its diagonal entries are the leverage scores. Statements using its projection properties assume the Gram matrix is nonsingular; the definition does not assume the diagonal bounds or the trace identity.
-- source:
--   Qi, Cao and Shen (2021), Distributionally Robust Conditional Quantile Prediction with Fixed Design, DOI 10.1287/mnsc.2020.3903, supplied source.pdf, (19), PDF/printed p. 13

import Mathlib

open MeasureTheory Matrix Filter Topology
open scoped ENNReal

namespace QiFixedDesign.Concentration

noncomputable def hat {N p : ℕ} (X : Matrix (Fin N) (Fin p) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  X * (X.transpose * X)⁻¹ * X.transpose

end QiFixedDesign.Concentration


