-- Prove2me | Definitions.Def_FoundationsML_Boosting_RademacherComplexity
-- name    : FoundationsML_Boosting_RademacherComplexity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:09:17.395115+00:00
-- url     : https://prove2.me/theorems/0a740532-b053-4f05-b8a1-e6b0388e16ff
-- title:
--   (Average) Rademacher complexity (Definition 3.2, restated)
-- statement:
--   **Definition 3.2, p. 31, PDF p. 48 (restated locally for this chapter).**
--   $R_m(G) = \mathbb E_{S\sim D^m}[\hat R_S(G)]$.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 31, Definition 3.2 (PDF p. 48)

import Mathlib
import Definitions.Def_FoundationsML_Boosting_EmpiricalRademacherComplexity

open MeasureTheory

namespace FoundationsML.Boosting

/-- The (average) Rademacher complexity of a family `G` of functions `Z → ℝ`, for samples of
size `m` drawn i.i.d. from a distribution `D` on `Z` (Mohri, Rostamizadeh & Talwalkar,
*Foundations of Machine Learning*, 2nd ed., MIT Press 2018, Definition 3.2, p. 31, PDF p. 48,
restated locally for this chapter since drafts cannot import another chunk's draft module):
`R_m(G) = E_{S∼D^m}[R̂_S(G)]`. -/
noncomputable def RademacherComplexity {Z : Type*} [MeasurableSpace Z]
    (D : Measure Z) (G : Set (Z → ℝ)) (m : ℕ) : ℝ :=
  ∫ S, EmpiricalRademacherComplexity G S ∂(Measure.pi (fun _ : Fin m => D))

end FoundationsML.Boosting


