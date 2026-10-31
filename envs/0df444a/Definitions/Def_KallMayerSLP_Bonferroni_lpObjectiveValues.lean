-- Prove2me | Definitions.Def_KallMayerSLP_Bonferroni_lpObjectiveValues
-- name    : KallMayerSLP_Bonferroni_lpObjectiveValues
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:13:48.768851+00:00
-- url     : https://prove2.me/theorems/7f5b9e70-3489-40cf-97ae-8f9c7c5e5e7a
-- title:
--   Objective values of the linear program (3.14)
-- statement:
--   The set of values of the objective $v_1+\dots+v_r$ on the feasible set of (3.14).
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 4, §3.4, eq. (3.14), p.288 (PDF 297)

import Mathlib
import Definitions.Def_KallMayerSLP_Bonferroni_lpFeasible

namespace KallMayerSLP.Bonferroni

/-- The set of objective values `v₁ + ⋯ + v_r` of the feasible points of the linear program (3.14).

Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 4, eq. (3.14), p.288 (PDF 297). -/
def lpObjectiveValues (r : ℕ) (S₁ S₂ : ℝ) : Set ℝ :=
  (fun v : Fin r → ℝ => ∑ i, v i) '' lpFeasible r S₁ S₂

end KallMayerSLP.Bonferroni


