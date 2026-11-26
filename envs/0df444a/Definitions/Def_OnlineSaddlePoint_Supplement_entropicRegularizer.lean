-- Prove2me | Definitions.Def_OnlineSaddlePoint_Supplement_entropicRegularizer
-- name    : OnlineSaddlePoint_Supplement_entropicRegularizer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T21:51:16.44321+00:00
-- url     : https://prove2.me/theorems/8c0447bf-6b53-5bdb-a279-486d3b5a021e
-- title:
--   Entropic regularizers $R_X(x)=\sum_i x_i\ln x_i+\ln d_1$, $R_Y(y)=\sum_i y_i\ln y_i+\ln d_2$
-- statement:
--   For dimension $d$ the **entropic regularizer** is
--
--   $$
--   R(x)=\sum_{i=1}^{d}x_i\ln(x_i)+\ln(d),
--   $$
--
--   the negative entropy shifted by $\ln d$. OMG-RFTL uses $R_X$ with $d=d_1$ for the row player and $R_Y$ with $d=d_2$ for the column player. The shift makes $R$ nonnegative on the probability simplex (the entropy of a distribution on $d$ points is at most $\ln d$), which is the nonnegativity that Theorem 2 requires of its regularizers.
--
--   **Formalization Note** `ln` is `Real.log`; points are in `PiLp 1 (fun _ : Fin d => ℝ)`.
-- source:
--   Rivera Cardoso, Wang, Xu, The Online Saddle Point Problem and Online Convex Optimization with Knapsacks, arXiv:1806.08301v3, §5, p.16

import Mathlib
import Definitions.Def_OnlineSaddlePoint_Supplement_negEntropy

namespace OnlineSaddlePoint.Supplement

/-- **Entropic regularizer** of OMG-RFTL. Rivera Cardoso, Wang, Xu, arXiv:1806.08301v3, §5, p.16:
"`R_X(x) ≜ ∑_{i=1}^{d₁} x_i ln(x_i) + ln(d₁)`, `R_Y(y) ≜ ∑_{i=1}^{d₂} y_i ln(y_i) + ln(d₂)`", where
"the extra logarithmic terms ensure `R_X`, `R_Y` are nonnegative everywhere in their respective
simplexes". `R_X` is `entropicRegularizer d₁` and `R_Y` is `entropicRegularizer d₂`.

**Formalization Note.** The negative entropy `∑ x_i ln x_i` is `negEntropy`; `ln` is `Real.log`.
Points are in `PiLp 1 (fun _ : Fin d => ℝ)`. -/
noncomputable def entropicRegularizer (d : ℕ) (x : PiLp 1 (fun _ : Fin d => ℝ)) : ℝ :=
  negEntropy x + Real.log d

end OnlineSaddlePoint.Supplement


