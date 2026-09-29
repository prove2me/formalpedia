-- Prove2me | Definitions.Def_FoundationsML_OnlineLearning_RWMPotential
-- name    : FoundationsML_OnlineLearning_RWMPotential
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:14:26.389023+00:00
-- url     : https://prove2.me/theorems/3b881da4-b6f7-4892-be81-0e3ab0618437
-- title:
--   RWM's potential function W_t
-- statement:
--   **p. 184, PDF p. 201.** $W_t = \sum_{i=1}^N w_{t,i}$.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 184 (PDF p. 201)

import Mathlib
import Definitions.Def_FoundationsML_OnlineLearning_RWMWeight

namespace FoundationsML.OnlineLearning

/-- The Randomized Weighted Majority algorithm's potential `W_t = ∑_{i=1}^N w_{t,i}` at the
start of round `t` (0-indexed, so `RWMPotential β N l 0` is the book's `W_1`) (Mohri,
Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 184,
PDF p. 201). -/
noncomputable def RWMPotential (β : ℝ) (N : ℕ) (l : ℕ → Fin N → ℝ) (t : ℕ) : ℝ :=
  ∑ i, RWMWeight β N l t i

end FoundationsML.OnlineLearning


