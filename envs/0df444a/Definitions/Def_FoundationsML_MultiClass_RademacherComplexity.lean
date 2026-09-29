-- Prove2me | Definitions.Def_FoundationsML_MultiClass_RademacherComplexity
-- name    : FoundationsML_MultiClass_RademacherComplexity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:30:41.03763+00:00
-- url     : https://prove2.me/theorems/7f7912f0-82b9-4d1b-bf09-e3cce7aa663e
-- title:
--   (Average) Rademacher complexity (Definition 3.2)
-- statement:
--   **Definition 3.2, p. 31, PDF p. 48.** $R_m(G) = \mathbb E_{S\sim D^m}[\hat R_S(G)]$.
--   Restated locally in this chunk's `MultiClass` namespace; this is the $R_m(\Pi_1(H))$
--   appearing in Theorem 9.2.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 31, Definition 3.2 (PDF p. 48)

import Mathlib
import Definitions.Def_FoundationsML_MultiClass_EmpiricalRademacherComplexity

open MeasureTheory

namespace FoundationsML.MultiClass

/-- The (average) Rademacher complexity of a family `G` of functions `Z → ℝ`, for samples of
size `m` drawn i.i.d. from a distribution `D` on `Z` (Mohri, Rostamizadeh & Talwalkar,
*Foundations of Machine Learning*, 2nd ed., MIT Press 2018, Definition 3.2, p. 31, PDF p. 48,
restated locally for this chapter since drafts cannot import another chunk's draft module):
`R_m(G) = E_{S∼D^m}[R̂_S(G)]`, the expectation of the empirical Rademacher complexity over an
i.i.d. sample of size `m`. -/
noncomputable def RademacherComplexity {Z : Type*} [MeasurableSpace Z]
    (D : Measure Z) (G : Set (Z → ℝ)) (m : ℕ) : ℝ :=
  ∫ S, EmpiricalRademacherComplexity G S ∂(Measure.pi (fun _ : Fin m => D))

end FoundationsML.MultiClass


