-- Prove2me | Definitions.Def_FoundationsML_OnlineLearning_RWMRoundLoss
-- name    : FoundationsML_OnlineLearning_RWMRoundLoss
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:15:44.000066+00:00
-- url     : https://prove2.me/theorems/de9f7441-80e4-415c-b632-9477423c6b54
-- title:
--   RWM's expected round loss L_t
-- statement:
--   **p. 183, PDF p. 200.** $L_t = \sum_{i=1}^N p_{t,i}l_{t,i}$.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 183 (PDF p. 200)

import Mathlib
import Definitions.Def_FoundationsML_OnlineLearning_RWMDist

namespace FoundationsML.OnlineLearning

/-- The expected loss `L_t = ∑_{i=1}^N p_{t,i} l_{t,i}` incurred by the Randomized Weighted
Majority algorithm at round `t` (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine
Learning*, 2nd ed., MIT Press 2018, p. 183, PDF p. 200). -/
noncomputable def RWMRoundLoss (β : ℝ) (N : ℕ) (l : ℕ → Fin N → ℝ) (t : ℕ) : ℝ :=
  ∑ i, RWMDist β N l t i * l t i

end FoundationsML.OnlineLearning


