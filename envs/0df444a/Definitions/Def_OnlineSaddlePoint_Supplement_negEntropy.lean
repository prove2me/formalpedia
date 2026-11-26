-- Prove2me | Definitions.Def_OnlineSaddlePoint_Supplement_negEntropy
-- name    : OnlineSaddlePoint_Supplement_negEntropy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T21:50:56.883689+00:00
-- url     : https://prove2.me/theorems/84fb2148-d90f-4c75-8509-5377e7cc4933
-- title:
--   Negative entropy $R(x)=\sum_{i=1}^d x_i\ln x_i$
-- statement:
--   For $x\in\mathbb R^d$ the **negative entropy** is
--
--   $$
--   R(x)=\sum_{i=1}^d x_i\ln(x_i).
--   $$
--
--   On the probability simplex it is the negative of the Shannon entropy of the distribution $x$. It is the regularizer of OMG-RFTL up to an additive constant, and Lemma 4 gives its Lipschitz constant on the restricted simplex.
--
--   **Formalization Note** `ln` is `Real.log`; the function is only used on restricted simplexes $\Delta_\theta$ with $\theta>0$, where all coordinates are positive.
-- source:
--   Rivera Cardoso, Wang, Xu, The Online Saddle Point Problem and Online Convex Optimization with Knapsacks, arXiv:1806.08301v3, Lemma 4, p.16; §5, p.16

import Mathlib

namespace OnlineSaddlePoint.Supplement

/-- **Negative entropy** `R(x) = ∑_{i=1}^d x_i ln(x_i)`. Rivera Cardoso, Wang, Xu,
arXiv:1806.08301v3, Lemma 4, p.16: "The function `R(x) ≜ ∑_{i=1}^d x_i ln(x_i)` …".

**Formalization Note.** Points are in `PiLp 1 (fun _ : Fin d => ℝ)` (`ℝ^d` with the `ℓ₁` norm);
`ln` is the natural logarithm `Real.log`. The function is only evaluated on restricted simplexes
`Δ_θ` with `θ > 0`, where every coordinate is positive and `Real.log` agrees with `ln`. -/
noncomputable def negEntropy {d : ℕ} (x : PiLp 1 (fun _ : Fin d => ℝ)) : ℝ :=
  ∑ i, x i * Real.log (x i)

end OnlineSaddlePoint.Supplement


