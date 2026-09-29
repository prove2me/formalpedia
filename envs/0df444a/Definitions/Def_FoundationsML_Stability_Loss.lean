-- Prove2me | Definitions.Def_FoundationsML_Stability_Loss
-- name    : FoundationsML_Stability_Loss
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-20T04:19:22.599973+00:00
-- url     : https://prove2.me/theorems/79f42626-d256-4121-8a50-194d014d52b8
-- title:
--   The loss of a hypothesis at a labeled point
-- statement:
--   **Notation, p. 333-334, PDF p. 350-351.** We denote by $z=(x,y)\in X\times Y$ a labeled
--   example. For a loss function $L:Y'\times Y\to\mathbb R_+$, the loss of a hypothesis $h$ at
--   point $z$ is $L_z(h) = L(h(x),y)$.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 333-334 (PDF p. 350-351)

import Mathlib

namespace FoundationsML.Stability

/-- The loss of a hypothesis `h` at a labeled point `z = (x, y)` (Mohri, Rostamizadeh &
Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 333-334, PDF p.
350-351): for a loss function `L : Y' × Y → ℝ_+`, `L_z(h) = L(h(x), y)`. -/
noncomputable def Loss {X Y Y' : Type*} (L : Y' → Y → ℝ) (h : X → Y') (z : X × Y) : ℝ :=
  L (h z.1) z.2

end FoundationsML.Stability


