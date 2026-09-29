-- Prove2me | Definitions.Def_FoundationsML_Stability_EpsilonInsensitiveLoss
-- name    : FoundationsML_Stability_EpsilonInsensitiveLoss
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-20T04:23:41.527573+00:00
-- url     : https://prove2.me/theorems/4ea4cf78-ab9b-48b5-8db2-3d53e6a01008
-- title:
--   The epsilon-insensitive loss
-- statement:
--   **Statement ((14.10)), p. 340, PDF p. 357.** The $\epsilon$-insensitive loss used by SVR is
--   $L_\epsilon(y',y) = 0$ if $|y'-y|\le\epsilon$, and $|y'-y|-\epsilon$ otherwise.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, (14.10), p. 340 (PDF p. 357)

import Mathlib

namespace FoundationsML.Stability

/-- The ε-insensitive loss (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*,
2nd ed., MIT Press 2018, (14.10), p. 340, PDF p. 357), used by SVR: `L_ε(y',y) = 0` if
`|y' − y| ≤ ε`, and `|y' − y| − ε` otherwise. -/
noncomputable def EpsilonInsensitiveLoss (ε : ℝ) (y' y : ℝ) : ℝ :=
  if |y' - y| ≤ ε then 0 else |y' - y| - ε

end FoundationsML.Stability


