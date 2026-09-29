-- Prove2me | Definitions.Def_FoundationsML_OnlineLearning_PerceptronUpdates
-- name    : FoundationsML_OnlineLearning_PerceptronUpdates
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:18:47.549993+00:00
-- url     : https://prove2.me/theorems/cc33bc5a-d682-4e7d-9c25-bc1c3f8bdb82
-- title:
--   Perceptron's update-round index set I
-- statement:
--   **p. 196, PDF p. 213.** $I = \{t\in[T] : y_t(w_t\cdot x_t)\le0\}$, Theorem 8.11's own $I$.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 196 (PDF p. 213)

import Mathlib
import Definitions.Def_FoundationsML_OnlineLearning_PerceptronWeight

open Classical

namespace FoundationsML.OnlineLearning

/-- The set `I` of round indices `t ∈ [T]` (here `t < T`, 0-indexed) at which the Perceptron
algorithm makes an update while processing `x_1,…,x_T` with labels `y_1,…,y_T` (Mohri,
Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 196,
PDF p. 213, Theorem 8.11's own `I`). -/
noncomputable def PerceptronUpdates {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (x : ℕ → V) (y : ℕ → ℝ) (T : ℕ) : Finset ℕ :=
  (Finset.range T).filter (fun t => y t * (inner (𝕜 := ℝ) (PerceptronWeight x y t) (x t) : ℝ) ≤ 0)

end FoundationsML.OnlineLearning


