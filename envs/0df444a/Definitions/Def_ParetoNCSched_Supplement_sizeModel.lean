-- Prove2me | Definitions.Def_ParetoNCSched_Supplement_sizeModel
-- name    : ParetoNCSched_Supplement_sizeModel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:25:26.82532+00:00
-- url     : https://prove2.me/theorems/a0bd218f-a179-4d17-b65b-bc8811a368aa
-- title:
--   The predicted-size model
-- statement:
--   In the **predicted-size model** a prediction for $n$ jobs is a vector $y=(y_1,\dots,y_n)$; the allowed predictions are those with $y\in(0,\infty)^n$, and $y$ is correct for the sizes $p$ if $y=p$. The algorithm knows $n$ and $y$.
--
--   This is the model of the randomized algorithm $\mathrm{RT}_\rho$ (Theorem 1.3) and the other model of the lower bound (Theorem E.2).
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix E, Predicted sizes, p.31; Appendix H, p.39

import Mathlib
import Definitions.Def_ParetoNCSched_Supplement_PredModel

namespace ParetoNCSched.Supplement

/-- **The predicted-size model.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix E, "Predicted sizes", p.31: "In this model the
prediction is a vector y ∈ (0, ∞)ⁿ, correct if y = p. The algorithm knows n and y".

**Formalization Note.** A prediction is a real vector `y : Fin n → ℝ`; the allowed ones are
those with every `y j > 0`, and `y` is correct for `p` iff `y = p`. -/
def sizeModel : PredModel where
  Pred n := Fin n → ℝ
  Adm y := ∀ j, 0 < y j
  Correct p y := y = p

end ParetoNCSched.Supplement


