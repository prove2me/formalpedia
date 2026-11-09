-- Prove2me | Definitions.Def_TranspositionIID_Main_Perturbation
-- name    : TranspositionIID_Main_Perturbation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:23:53.317076+00:00
-- url     : https://prove2.me/theorems/b4d0384a-1276-4709-81fe-dc393b21cfb4
-- title:
--   The exponentially small positive request perturbation
-- statement:
--   For $n\ge2$ and any probability vector $p$, set
--   $$q_i=\frac{p_i+e^{-n}}{1+ne^{-n}}.$$
--   The kernel, cost, optimum and stationary distribution of $q$ are then computed by the same definitions applied to this vector. No coupling property or desired inequality is included as data. This is the perturbation used to handle zero and extremely small request probabilities.
-- source:
--   Clayton Mizgerd, Transposition achieves OPT+O(1) in polynomial time for IID list update, STOC 2027 submission #668 (October 2026), supplied canonical submission artifact; citation basis published (not acceptance). Lemma 4.3, printed p.10 = PDF p.10

import Definitions.Def_TranspositionIID_Main_Stationary

noncomputable section

namespace TranspositionIID.Main

/-- Positive perturbation from Lemma 4.3, equation (4.5), p.10. -/
def perturb {n : ℕ} (p : Fin n → ℝ) (i : Fin n) : ℝ :=
  (p i + Real.exp (-(n : ℝ))) / (1 + (n : ℝ) * Real.exp (-(n : ℝ)))

end TranspositionIID.Main


