-- Prove2me | Definitions.Def_FoundationsML_OnlineLearning_PerceptronNumUpdates
-- name    : FoundationsML_OnlineLearning_PerceptronNumUpdates
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:19:29.46017+00:00
-- url     : https://prove2.me/theorems/30b6d484-1e7b-4cb4-9846-0fd071295bd3
-- title:
--   Perceptron's number of updates M
-- statement:
--   **p. 196, PDF p. 213.** $M = |I|$, Theorem 8.11's own $M$.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 196 (PDF p. 213)

import Mathlib
import Definitions.Def_FoundationsML_OnlineLearning_PerceptronUpdates

namespace FoundationsML.OnlineLearning

/-- The number `M = |I|` of updates made by the Perceptron algorithm while processing
`x_1,…,x_T` with labels `y_1,…,y_T` (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine
Learning*, 2nd ed., MIT Press 2018, p. 196, PDF p. 213, Theorem 8.11's own `M`). -/
noncomputable def PerceptronNumUpdates {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (x : ℕ → V) (y : ℕ → ℝ) (T : ℕ) : ℕ :=
  (PerceptronUpdates x y T).card

end FoundationsML.OnlineLearning


