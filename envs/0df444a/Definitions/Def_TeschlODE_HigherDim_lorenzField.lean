-- Prove2me | Definitions.Def_TeschlODE_HigherDim_lorenzField
-- name    : TeschlODE_HigherDim_lorenzField
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T16:26:13.21048+00:00
-- url     : https://prove2.me/theorems/a8ab9ee2-76f9-4ec9-834b-b72338b30b1c
-- title:
--   The Lorenz vector field (8.13)
-- statement:
--   For parameters $\sigma, r, b$ the **Lorenz equation** is the system on $\mathbb{R}^3 \ni (x, y, z)$
--   $$\dot x = -\sigma(x - y), \qquad \dot y = r x - y - x z, \qquad \dot z = x y - b z. \qquad (8.13)$$
--   `lorenzField σ r b` is its right-hand side. The book assumes $\sigma, r, b > 0$; the definition accepts any real parameters and the theorems state the positivity.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 234, §8.2, Eq. (8.13)

import Mathlib

namespace TeschlODE.HigherDim

/-- Teschl, §8.2, p. 234, (8.13): the Lorenz vector field on `ℝ³ ∋ (x, y, z)`,
`ẋ = -σ(x - y)`, `ẏ = r x - y - x z`, `ż = x y - b z`. -/
noncomputable def lorenzField (σ r b : ℝ) (v : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) :=
  !₂[-σ * (v 0 - v 1), r * v 0 - v 1 - v 0 * v 2, v 0 * v 1 - b * v 2]

end TeschlODE.HigherDim


