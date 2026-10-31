-- Prove2me | Definitions.Def_QiFixedDesign_Concentration_Response
-- name    : QiFixedDesign_Concentration_Response
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:59:06.881678+00:00
-- url     : https://prove2.me/theorems/8e353e76-98a9-4916-931d-d22ba7a35f4c
-- title:
--   Fixed-design linear responses
-- statement:
--   Given a fixed design sequence $x$, a true coefficient $\beta_0\in\mathbb R^p$ and a training innovation vector $\omega\in\mathbb R^N$, set $Y_i=\beta_0^T x_i+\omega_i$. The feature rows are the first $N$ rows of the same sequence, indexed from zero. The training vector is sampled from the product of the innovation law in the theorem statements.
-- source:
--   Qi, Cao and Shen (2021), Distributionally Robust Conditional Quantile Prediction with Fixed Design, DOI 10.1287/mnsc.2020.3903, supplied source.pdf, (2), PDF/printed p. 8

import Mathlib

open MeasureTheory Matrix Filter Topology
open scoped ENNReal

namespace QiFixedDesign.Concentration

def response {p N : ℕ} (x : ℕ → Fin p → ℝ) (β₀ : Fin p → ℝ)
    (ω : Fin N → ℝ) : Fin N → ℝ :=
  fun i => β₀ ⬝ᵥ x i.val + ω i

end QiFixedDesign.Concentration


