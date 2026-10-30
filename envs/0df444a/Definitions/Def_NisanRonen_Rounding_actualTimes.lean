-- Prove2me | Definitions.Def_NisanRonen_Rounding_actualTimes
-- name    : NisanRonen_Rounding_actualTimes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:18:57.209277+00:00
-- url     : https://prove2.me/theorems/f5ca3d91-140d-499a-a5ef-c3d764fc01af
-- title:
--   Actual times $\tilde t$ of a strategy profile
-- statement:
--   Fix an allocation algorithm $f$ on rounded instances and a grid step $\delta$. Under a strategy profile $s = (s^1, \dots, s^n)$ the mechanism allocates according to the declarations only, $x = x_f(d^1, \dots, d^n)$, and then each task $j$ is performed by the agent $x(j)$ it was allocated to, in time
--
--   $$
--   \tilde t_j = e^{x(j)}(x)_j .
--   $$
--
--   The vector $\tilde t = (\tilde t_1, \dots, \tilde t_k)$ is the vector of actual times known to the mechanism.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001) 166–196, doi:10.1006/game.1999.0790, Definition 20, p. 187 (PDF p. 22): "t̃ = t̃_1, …, t̃_k denotes the actual times that they were performed in"; Definition 18, p. 186: "The decision k of the mechanism must be a function of just the declarations"

import Mathlib
import Definitions.Def_NisanRonen_Rounding_allocOf
import Definitions.Def_NisanRonen_Rounding_Strategy

namespace NisanRonen.Rounding

/-- **The actual times t̃ of a strategy profile** (Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001), Definition 20, p. 187:
"t̃ = t̃_1, …, t̃_k denotes the actual times that they were performed in"). Under the profile
`s`, the allocation is `x = allocOf f δ (fun i => (s i).decl)` (a function of the declarations
only, Definition 18), and task `j` is performed by agent `x j` in time `(s (x j)).exec x j`. -/
noncomputable def actualTimes {n k : ℕ} [NeZero n] (f : List (Fin n → ℕ) → List (Fin n))
    (δ : ℝ) (s : Fin n → Strategy n k) : Fin k → ℝ :=
  let x := allocOf f δ (fun i => (s i).decl)
  fun j => (s (x j)).exec x j

end NisanRonen.Rounding


