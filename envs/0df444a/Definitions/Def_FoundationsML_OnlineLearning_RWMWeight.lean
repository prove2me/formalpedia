-- Prove2me | Definitions.Def_FoundationsML_OnlineLearning_RWMWeight
-- name    : FoundationsML_OnlineLearning_RWMWeight
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:13:39.687145+00:00
-- url     : https://prove2.me/theorems/18807b9b-e3b5-440c-9a87-995476950889
-- title:
--   RWM's per-expert weight w_t,i (Figure 8.4)
-- statement:
--   **Figure 8.4, p. 184, PDF p. 201.** `w_1` uniform (`= 1`); `w_{t+1,i} = β·w_{t,i}` if
--   `l_{t,i} = 1`, else unchanged.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, Figure 8.4, p. 184 (PDF p. 201)

import Mathlib

namespace FoundationsML.OnlineLearning

/-- The Randomized Weighted Majority algorithm's weight `w_{t,i}` of expert `i` at the start
of round `t` (`t = 0` is the initial uniform weight `w_1 = 1` of Figure 8.4 lines 1-2; `t + 1`
is `w_{t+2}`, obtained from `w_{t+1}` by the update of Figure 8.4 lines 6-9 using round `t`'s
loss vector `l t`) (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd
ed., MIT Press 2018, Figure 8.4, p. 184, PDF p. 201). -/
noncomputable def RWMWeight (β : ℝ) (N : ℕ) (l : ℕ → Fin N → ℝ) : ℕ → Fin N → ℝ
  | 0 => fun _ => 1
  | t + 1 => fun i => if l t i = 1 then β * RWMWeight β N l t i else RWMWeight β N l t i

end FoundationsML.OnlineLearning


