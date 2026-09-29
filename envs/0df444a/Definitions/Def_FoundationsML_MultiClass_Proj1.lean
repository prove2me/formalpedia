-- Prove2me | Definitions.Def_FoundationsML_MultiClass_Proj1
-- name    : FoundationsML_MultiClass_Proj1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:29:30.885325+00:00
-- url     : https://prove2.me/theorems/21dcb67f-458d-4402-858f-fdcfeffadd4d
-- title:
--   Projection Π_1(H) onto the first coordinate
-- statement:
--   **p. 217, PDF p. 234.** $\Pi_1(H) = \{x\mapsto h(x,y) : y\in Y, h\in H\}$, the projection
--   of a multi-class hypothesis set $H\subseteq\mathbb R^{X\times Y}$ onto ordinary real-valued
--   functions on $X$; this, not $H$ itself, is what the chapter's Rademacher-complexity terms
--   bound.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 217 (PDF p. 234)

import Mathlib

namespace FoundationsML.MultiClass

/-- The projection `Π_1(H)` of a family `H` of multi-class scoring functions
`h : X × Y → ℝ` onto its first coordinate (Mohri, Rostamizadeh & Talwalkar, *Foundations of
Machine Learning*, 2nd ed., MIT Press 2018, p. 217, PDF p. 234):
`Π_1(H) = {x ↦ h(x,y) : y ∈ Y, h ∈ H}`. -/
def Proj1 {X Y : Type*} (H : Set (X × Y → ℝ)) : Set (X → ℝ) :=
  {g | ∃ h ∈ H, ∃ y : Y, g = fun x => h (x, y)}

end FoundationsML.MultiClass


