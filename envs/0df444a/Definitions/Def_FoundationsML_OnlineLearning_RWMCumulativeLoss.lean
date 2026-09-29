-- Prove2me | Definitions.Def_FoundationsML_OnlineLearning_RWMCumulativeLoss
-- name    : FoundationsML_OnlineLearning_RWMCumulativeLoss
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:16:28.146828+00:00
-- url     : https://prove2.me/theorems/2919f8fe-d1bb-498e-b8f2-39a47a3ae0f5
-- title:
--   RWM's total loss L_T
-- statement:
--   **p. 183, PDF p. 200.** $L_T = \sum_{t=1}^T L_t$.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 183 (PDF p. 200)

import Mathlib
import Definitions.Def_FoundationsML_OnlineLearning_RWMRoundLoss

namespace FoundationsML.OnlineLearning

/-- The total loss `L_T = ∑_{t=1}^T L_t` incurred by the Randomized Weighted Majority
algorithm over `T` rounds (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*,
2nd ed., MIT Press 2018, p. 183, PDF p. 200). -/
noncomputable def RWMCumulativeLoss (β : ℝ) (N : ℕ) (l : ℕ → Fin N → ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T, RWMRoundLoss β N l t

end FoundationsML.OnlineLearning


