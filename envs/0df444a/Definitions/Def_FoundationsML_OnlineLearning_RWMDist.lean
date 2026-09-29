-- Prove2me | Definitions.Def_FoundationsML_OnlineLearning_RWMDist
-- name    : FoundationsML_OnlineLearning_RWMDist
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:15:05.31903+00:00
-- url     : https://prove2.me/theorems/9eaf0593-a83b-4d9b-afd4-64d677448357
-- title:
--   RWM's distribution p_t,i over experts
-- statement:
--   **Figure 8.4 lines 10-12, p. 184, PDF p. 201.** $p_{t,i} = w_{t,i}/W_t$.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, Figure 8.4, p. 184 (PDF p. 201)

import Mathlib
import Definitions.Def_FoundationsML_OnlineLearning_RWMWeight
import Definitions.Def_FoundationsML_OnlineLearning_RWMPotential

namespace FoundationsML.OnlineLearning

/-- The Randomized Weighted Majority algorithm's distribution `p_{t,i} = w_{t,i}/W_t` over
experts at round `t` (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd
ed., MIT Press 2018, Figure 8.4 lines 10-12, p. 184, PDF p. 201). -/
noncomputable def RWMDist (β : ℝ) (N : ℕ) (l : ℕ → Fin N → ℝ) (t : ℕ) (i : Fin N) : ℝ :=
  RWMWeight β N l t i / RWMPotential β N l t

end FoundationsML.OnlineLearning


