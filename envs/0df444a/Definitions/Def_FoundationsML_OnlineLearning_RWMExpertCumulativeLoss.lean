-- Prove2me | Definitions.Def_FoundationsML_OnlineLearning_RWMExpertCumulativeLoss
-- name    : FoundationsML_OnlineLearning_RWMExpertCumulativeLoss
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:17:05.322567+00:00
-- url     : https://prove2.me/theorems/55af5fb8-a412-4683-a4b0-aa96fb14468e
-- title:
--   Per-expert total loss L_T,i
-- statement:
--   **p. 183, PDF p. 200.** $L_{T,i} = \sum_{t=1}^T l_{t,i}$.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 183 (PDF p. 200)

import Mathlib

namespace FoundationsML.OnlineLearning

/-- The total loss `L_{T,i} = ∑_{t=1}^T l_{t,i}` incurred by action/expert `i` over `T` rounds
(Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018,
p. 183, PDF p. 200). -/
noncomputable def RWMExpertCumulativeLoss (N : ℕ) (l : ℕ → Fin N → ℝ) (T : ℕ) (i : Fin N) : ℝ :=
  ∑ t ∈ Finset.range T, l t i

end FoundationsML.OnlineLearning


