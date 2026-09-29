-- Prove2me | Definitions.Def_FoundationsML_OnlineLearning_RWMMinExpertLoss
-- name    : FoundationsML_OnlineLearning_RWMMinExpertLoss
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:17:40.713342+00:00
-- url     : https://prove2.me/theorems/7dfe0400-8311-47be-b1d8-4ad0d2bcfe31
-- title:
--   Best expert's total loss L_T^min
-- statement:
--   **p. 183, PDF p. 200.** $L_T^{\min} = \min_{i\in A} L_{T,i}$.
--
--   **Formalization Note.** `⨅ i, RWMExpertCumulativeLoss N l T i` over the finite index
--   `Fin N`; every consumer carries `0 < N`, under which this is the actual minimum.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 183 (PDF p. 200)

import Mathlib
import Definitions.Def_FoundationsML_OnlineLearning_RWMExpertCumulativeLoss

namespace FoundationsML.OnlineLearning

/-- The minimal total loss `L_T^min = min_{i∈A} L_{T,i}` among all actions/experts over `T`
rounds (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press
2018, p. 183, PDF p. 200).

**Formalization Note.** `⨅ i, RWMExpertCumulativeLoss N l T i` is the real infimum over the
finite index type `Fin N`; every consuming theorem carries `0 < N` (a nonempty set of experts),
under which this coincides with the actual minimum. -/
noncomputable def RWMMinExpertLoss (N : ℕ) (l : ℕ → Fin N → ℝ) (T : ℕ) : ℝ :=
  ⨅ i, RWMExpertCumulativeLoss N l T i

end FoundationsML.OnlineLearning


