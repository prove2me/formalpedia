-- Prove2me | Definitions.Def_FoundationsML_MaxEnt_RademacherComplexity
-- name    : FoundationsML_MaxEnt_RademacherComplexity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-20T04:17:12.605628+00:00
-- url     : https://prove2.me/theorems/dd811a46-77f6-49cf-bd72-47e4cfb61282
-- title:
--   (Average) Rademacher complexity (Definition 3.2, restated)
-- statement:
--   **Definition 3.2, p. 31, PDF p. 48 (restated locally for this chapter).**
--   $R_m(G) = \mathbb E_{S\sim D^m}[\hat R_S(G)]$.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 31, Definition 3.2 (PDF p. 48)

import Mathlib
import Definitions.Def_FoundationsML_MaxEnt_EmpiricalRademacherComplexity

open MeasureTheory

namespace FoundationsML.MaxEnt

/-- The (average) Rademacher complexity of a family `G` of functions `Z → ℝ`, for samples of
size `m` drawn i.i.d. from a distribution `D` on `Z` (Mohri, Rostamizadeh & Talwalkar,
*Foundations of Machine Learning*, 2nd ed., MIT Press 2018, Definition 3.2, p. 31, PDF p. 48,
restated locally for this chapter since drafts cannot import another chunk's draft module):
`R_m(G) = E_{S∼D^m}[R̂_S(G)]`. -/
noncomputable def RademacherComplexity {Z : Type*} [MeasurableSpace Z]
    (D : Measure Z) (G : Set (Z → ℝ)) (m : ℕ) : ℝ :=
  ∫ S, EmpiricalRademacherComplexity G S ∂(Measure.pi (fun _ : Fin m => D))

end FoundationsML.MaxEnt


