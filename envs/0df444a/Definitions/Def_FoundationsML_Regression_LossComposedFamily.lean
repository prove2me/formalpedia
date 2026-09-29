-- Prove2me | Definitions.Def_FoundationsML_Regression_LossComposedFamily
-- name    : FoundationsML_Regression_LossComposedFamily
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-20T04:07:12.023887+00:00
-- url     : https://prove2.me/theorems/b1109088-2396-4735-a655-b4c50134579c
-- title:
--   Loss-composed family G associated to H
-- statement:
--   **p. 269 and p. 271, PDF pp. 286, 288.** $G = \{(x,y)\mapsto L(h(x),y) : h\in H\}$, the
--   family of loss functions associated to a hypothesis set $H$ and loss $L$.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 269 (PDF p. 286)

import Mathlib

namespace FoundationsML.Regression

/-- The family of loss functions `G = {(x,y) ↦ L(h(x),y) : h ∈ H}` associated to a hypothesis
set `H` of real-valued functions and a loss `L : ℝ → ℝ → ℝ` (Mohri, Rostamizadeh & Talwalkar,
*Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 269, PDF p. 286, also used in
Definition 11.4's `G`, p. 271, PDF p. 288). -/
def LossComposedFamily {X : Type*} (L : ℝ → ℝ → ℝ) (H : Set (X → ℝ)) : Set (X × ℝ → ℝ) :=
  {g | ∃ h ∈ H, g = fun p => L (h p.1) p.2}

end FoundationsML.Regression


