-- Prove2me | Definitions.Def_QMCLeafB_Rq
-- name    : QMCLeafB_Rq
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-08T19:21:44.508124+00:00
-- url     : https://prove2.me/theorems/30a01216-ec37-43e2-9410-0bb0ef250330
-- title:
--   Rational total weight Rq
-- statement:
--   Total weight $R_q(G)=2\sum_e w_e$ as rational, with $R_q\ge0$ and cast to real.
-- source:
--   QMC leaf B, local bricks

import Mathlib
import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEnergy_weightMatrix

open scoped BigOperators

namespace QuantumMaxCutEnergy

/-- Rational total weight Rq = 2 * sum weights (twice total weight) -/
noncomputable def Rq (G : Input) : ℚ := 2 * ∑ e, ((G.weights e : ℚ≥0) : ℚ)

@[simp] lemma Rq_nonneg (G : Input) : 0 ≤ Rq G := by unfold Rq; positivity

lemma Rq_cast (G : Input) : (Rq G : ℝ) = 2 * ∑ e, (G.weights e : ℝ) := by unfold Rq; push_cast; ring

end QuantumMaxCutEnergy


