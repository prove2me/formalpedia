-- Prove2me | Definitions.Def_FoundationsML_Stability_GeneralizationError
-- name    : FoundationsML_Stability_GeneralizationError
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-20T04:20:38.68499+00:00
-- url     : https://prove2.me/theorems/4feb7dd0-8bc9-47c1-ac28-a830dab05b60
-- title:
--   Generalization error of a hypothesis
-- statement:
--   **Statement, p. 334, PDF p. 351.** The generalization error of $h$, for a distribution $D$
--   on labeled points, is $R(h) = \mathbb E_{z\sim D}[L_z(h)]$.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 334 (PDF p. 351)

import Mathlib
import Definitions.Def_FoundationsML_Stability_Loss

open MeasureTheory

namespace FoundationsML.Stability

/-- The generalization error of a hypothesis `h`, for a loss function `L` and a distribution
`D` on labeled points (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd
ed., MIT Press 2018, p. 334, PDF p. 351): `R(h) = E_{z∼D}[L_z(h)]`. -/
noncomputable def GeneralizationError {X Y Y' : Type*} [MeasurableSpace (X × Y)]
    (D : Measure (X × Y)) (L : Y' → Y → ℝ) (h : X → Y') : ℝ :=
  ∫ z, Loss L h z ∂D

end FoundationsML.Stability


