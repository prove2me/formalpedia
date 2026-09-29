-- Prove2me | Definitions.Def_FoundationsML_ModelSelection_PhiLossPointwise
-- name    : FoundationsML_ModelSelection_PhiLossPointwise
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:19:20.721906+00:00
-- url     : https://prove2.me/theorems/54ad88a1-ebcc-4673-8a90-84c297882cea
-- title:
--   Pointwise Φ-loss L_Φ(x,u)
-- statement:
--   **p. 75, PDF p. 92.** For a convex non-decreasing surrogate $\Phi:\mathbb R\to\mathbb R$ and
--   conditional label probability $\eta$, the pointwise $\Phi$-loss at $x\in X$ and score
--   $u\in\mathbb R$ is $L_\Phi(x,u) = \eta(x)\Phi(-u) + (1-\eta(x))\Phi(u)$.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 75 (PDF p. 92)

import Mathlib

namespace FoundationsML.ModelSelection

/-- The pointwise Φ-loss `L_Φ(x, u) = η(x) Φ(−u) + (1 − η(x)) Φ(u)` at a point `x ∈ X` and a
score `u ∈ ℝ`, for a conditional label probability `η(x) = P[y = +1 | x]` and a convex
non-decreasing surrogate `Φ : ℝ → ℝ` (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine
Learning*, 2nd ed., MIT Press 2018, p. 75, PDF p. 92). -/
def PhiLossPointwise {X : Type*} (η : X → ℝ) (Φ : ℝ → ℝ) (x : X) (u : ℝ) : ℝ :=
  η x * Φ (-u) + (1 - η x) * Φ u

end FoundationsML.ModelSelection


