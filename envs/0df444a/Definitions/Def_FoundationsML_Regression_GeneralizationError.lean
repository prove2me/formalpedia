-- Prove2me | Definitions.Def_FoundationsML_Regression_GeneralizationError
-- name    : FoundationsML_Regression_GeneralizationError
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-20T04:05:26.655183+00:00
-- url     : https://prove2.me/theorems/6f6f9a1d-1208-4dcc-9d70-ba061c245c3b
-- title:
--   Generalization error for regression (Eq. 11.1)
-- statement:
--   **Eq. (11.1), p. 268, PDF p. 285.** $R(h) = \mathbb E_{(x,y)\sim D}[L(h(x),y)]$, for a
--   regression hypothesis $h:X\to\mathbb R$, a loss $L$, and a joint distribution $D$ on
--   $X\times\mathbb R$.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, Eq. (11.1), p. 268 (PDF p. 285)

import Mathlib

open MeasureTheory

namespace FoundationsML.Regression

/-- The generalization error of a regression hypothesis `h : X → ℝ` with respect to a loss
function `L : ℝ → ℝ → ℝ` (curried form of `L : Y × Y → ℝ`, `L y y'` standing for `L(y,y')`)
and a joint distribution `D` on `X × ℝ` (Mohri, Rostamizadeh & Talwalkar, *Foundations of
Machine Learning*, 2nd ed., MIT Press 2018, Eq. (11.1), p. 268, PDF p. 285):
`R(h) = E_{(x,y)∼D}[L(h(x),y)]`. -/
noncomputable def GeneralizationError {X : Type*} [MeasurableSpace X]
    (D : Measure (X × ℝ)) (L : ℝ → ℝ → ℝ) (h : X → ℝ) : ℝ :=
  ∫ p, L (h p.1) p.2 ∂D

end FoundationsML.Regression


