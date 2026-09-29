-- Prove2me | Definitions.Def_FoundationsML_OnlineLearning_GeneralizationError
-- name    : FoundationsML_OnlineLearning_GeneralizationError
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:12:56.620396+00:00
-- url     : https://prove2.me/theorems/6e0bffa9-4f2e-4ac3-8ac9-9460878e6264
-- title:
--   Generalization error (restated from chunk 11's Eq. 11.1 convention)
-- statement:
--   **Restated locally, used at p. 202, PDF p. 219.** $R(h) = \mathbb E_{(x,y)\sim D}[L(h(x),y)]$,
--   for a hypothesis $h:X\to\mathbb R$, a loss $L$, and a joint distribution $D$ on
--   $X\times\mathbb R$ — the same convention as chunk `11-regression`'s Eq. (11.1), needed here
--   for Lemma 8.14/Theorem 8.15's on-line-to-batch conversion.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 202 (PDF p. 219)

import Mathlib

open MeasureTheory

namespace FoundationsML.OnlineLearning

/-- The generalization error of a hypothesis `h : X → ℝ` with respect to a loss function
`L : ℝ → ℝ → ℝ` and a joint distribution `D` on `X × ℝ` (Mohri, Rostamizadeh & Talwalkar,
*Foundations of Machine Learning*, 2nd ed., MIT Press 2018, restated locally from chunk
`11-regression`'s Eq. (11.1) convention, used at p. 202, PDF p. 219): `R(h) =
E_{(x,y)∼D}[L(h(x),y)]`. -/
noncomputable def GeneralizationError {X : Type*} [MeasurableSpace X]
    (D : Measure (X × ℝ)) (L : ℝ → ℝ → ℝ) (h : X → ℝ) : ℝ :=
  ∫ p, L (h p.1) p.2 ∂D

end FoundationsML.OnlineLearning


