-- Prove2me | Definitions.Def_NisanRonen_Rounding_roundedMakespan
-- name    : NisanRonen_Rounding_roundedMakespan
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:16:41.745046+00:00
-- url     : https://prove2.me/theorems/4b7a2a07-09ac-4a57-a737-408c6968b384
-- title:
--   Rounded make-span $\hat g$
-- statement:
--   For a grid step $\delta$, an allocation $x$ and a vector $\tau$ of times, the **rounded make-span** is the make-span of the vector obtained by rounding every entry up to an integer multiple of $\delta$:
--
--   $$
--   \hat g(x, \tau) = g(x, \hat \tau), \qquad \hat\tau_j = \delta \left\lceil \tau_j / \delta \right\rceil .
--   $$
--
--   The rounding mechanism computes its bonus with $\hat g$, and the rounding algorithm minimizes $\hat g$ exactly.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001) 166–196, doi:10.1006/game.1999.0790, p. 192 (PDF p. 27), Notation: "Denote also ĝ(x, t̃) = g(x, t̃̂), where g is the make-span objective function"

import Mathlib
import Definitions.Def_NisanRonen_Rounding_makespan
import Definitions.Def_NisanRonen_Rounding_roundUp

namespace NisanRonen.Rounding

/-- **Rounded make-span** `ĝ` (Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001), Notation, p. 192: "Denote also
`ĝ(x, t̃) = g(x, \hat{t̃})`, where g is the make-span objective function"). Every entry of the
time vector is rounded up to the δ-grid before the make-span is taken. -/
noncomputable def roundedMakespan {n k : ℕ} [NeZero n] (δ : ℝ) (x : Fin k → Fin n)
    (τ : Fin k → ℝ) : ℝ :=
  makespan x (fun j => roundUp δ (τ j))

end NisanRonen.Rounding


