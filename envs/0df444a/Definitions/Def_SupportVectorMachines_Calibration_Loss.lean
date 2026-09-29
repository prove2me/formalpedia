-- Prove2me | Definitions.Def_SupportVectorMachines_Calibration_Loss
-- name    : SupportVectorMachines_Calibration_Loss
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:24:22.477744+00:00
-- url     : https://prove2.me/theorems/ef29ef75-e7b4-49f9-876d-1346beccc28d
-- title:
--   A loss function (restated locally)
-- statement:
--   A **loss function** on a measurable space $X$ with label set $Y \subset \mathbb R$ closed is
--   a measurable map $L : X \times Y \times \mathbb R \to [0,\infty)$ (Steinwart & Christmann,
--   *Support Vector Machines*, Springer 2008, Definition 2.1, p. 22), restated locally in this
--   sub-namespace per Hard Rule 9 of the captain brief rather than imported from the
--   `LossFunctions` chapter's draft.
--
--   **Formalization Note** Represented as a curried function `X → ℝ → ℝ → ℝ`, exactly as in the
--   `01-loss-functions` mission; nonnegativity and the restriction of the middle argument to a
--   specific label set $Y$ are supplied as hypotheses where a concrete loss is used.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, p. 22, Definition 2.1

import Mathlib

namespace SupportVectorMachines.Calibration

/-- A loss function (Steinwart & Christmann, *Support Vector Machines*, Springer 2008,
Definition 2.1, p. 22, restated locally per Hard Rule 9 rather than imported from the
`LossFunctions` chapter draft): given a measurable space `X` and closed label set `Y ⊂ ℝ`, a loss
is a measurable map `L : X × Y × ℝ → [0,∞)`. Here it is represented as a curried function
`X → ℝ → ℝ → ℝ` (the middle argument ranges over the ambient reals; hypotheses fixing it to the
relevant label set `Y` and its nonnegativity are supplied where a specific loss is used, not
baked into the type). -/
abbrev Loss (X : Type*) : Type _ := X → ℝ → ℝ → ℝ

end SupportVectorMachines.Calibration


