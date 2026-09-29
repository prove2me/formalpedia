-- Prove2me | Definitions.Def_FoundationsML_SVM_RademacherComplexity
-- name    : FoundationsML_SVM_RademacherComplexity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:29:18.96117+00:00
-- url     : https://prove2.me/theorems/8e34a000-93f2-4e49-bf6a-47a898606915
-- title:
--   (Average) Rademacher complexity (Definition 3.2)
-- statement:
--   **Definition 3.2 (Rademacher complexity), p. 31, PDF p. 48.** For any integer $m\ge1$, the
--   Rademacher complexity of $G$ is $R_m(G) = \mathbb E_{S\sim D^m}[\hat R_S(G)]$.
--
--   **Formalization Note.** Restated locally in `SVM`, byte-identical to chunk `03-rademacher-vc`'s
--   own copy. `RademacherComplexity D G m` is the Bochner integral of
--   `EmpiricalRademacherComplexity G` over the product-measure space
--   `(Fin m → Z, Measure.pi (fun _ => D))`.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 31, Definition 3.2 (PDF p. 48)

import Mathlib
import Definitions.Def_FoundationsML_SVM_EmpiricalRademacherComplexity

open MeasureTheory

namespace FoundationsML.SVM

/-- The (average) Rademacher complexity of a family `G` of functions `Z → ℝ`, for samples of
size `m` drawn i.i.d. from a distribution `D` on `Z` (Mohri, Rostamizadeh & Talwalkar,
*Foundations of Machine Learning*, 2nd ed., MIT Press 2018, Definition 3.2, p. 31, PDF p. 48,
restated locally for this chapter since drafts cannot import another chunk's draft module):
`R_m(G) = E_{S∼D^m}[R̂_S(G)]`, the expectation of the empirical Rademacher complexity over an
i.i.d. sample of size `m`. -/
noncomputable def RademacherComplexity {Z : Type*} [MeasurableSpace Z]
    (D : Measure Z) (G : Set (Z → ℝ)) (m : ℕ) : ℝ :=
  ∫ S, EmpiricalRademacherComplexity G S ∂(Measure.pi (fun _ : Fin m => D))

end FoundationsML.SVM


