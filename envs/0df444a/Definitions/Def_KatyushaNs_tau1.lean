-- Prove2me | Definitions.Def_KatyushaNs_tau1
-- name    : KatyushaNs_tau1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:46:29.789863+00:00
-- url     : https://prove2.me/theorems/e5d7e7bc-8f73-4f70-8486-87b32981a86f
-- title:
--   Momentum parameter $\tau_{1,s} = 2/(s+4)$
-- statement:
--   For the epoch index $s = 0, 1, 2, \dots$ of Algorithm 2,
--   $$\tau_{1,s} = \frac{2}{s+4}.$$
--   It decreases from $\tau_{1,0} = 1/2$; the other momentum weight is the constant $\tau_2 = 1/2$.
-- source:
--   Allen-Zhu, Katyusha: The First Direct Acceleration of Stochastic Gradient Methods, arXiv:1603.05953v6, Algorithm 2, line 5, p. 15

import Mathlib

namespace KatyushaNs

/-- **The momentum parameter `τ_{1,s} = 2/(s+4)` (Algorithm 2, line 5).**
Allen-Zhu, *Katyusha: The First Direct Acceleration of Stochastic Gradient Methods*,
arXiv:1603.05953v6, Algorithm 2, line 5, p. 15 (PDF p. 16): "τ_{1,s} ← 2/(s+4)".

`tau1 s = 2 / (s + 4)` for the epoch index `s = 0, 1, 2, …`. -/
noncomputable def tau1 (s : ℕ) : ℝ := 2 / ((s : ℝ) + 4)

end KatyushaNs


