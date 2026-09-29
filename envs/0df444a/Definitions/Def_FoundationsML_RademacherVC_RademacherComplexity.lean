-- Prove2me | Definitions.Def_FoundationsML_RademacherVC_RademacherComplexity
-- name    : FoundationsML_RademacherVC_RademacherComplexity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:11:31.262908+00:00
-- url     : https://prove2.me/theorems/bb742650-0f3f-4078-9c01-1fa1c7e9da6a
-- title:
--   (Average) Rademacher complexity (Definition 3.2)
-- statement:
--   **Definition 3.2 (Rademacher complexity), p. 31, PDF p. 48.** For any integer $m\ge1$, the
--   Rademacher complexity of $G$ is $R_m(G) = \mathbb E_{S\sim D^m}[\hat R_S(G)]$, the
--   expectation of the empirical Rademacher complexity over samples of size $m$ drawn
--   according to $D$.
--
--   **Formalization Note.** `RademacherComplexity D G m` is the Bochner integral of
--   `EmpiricalRademacherComplexity G` over the product-measure space
--   `(Fin m → Z, Measure.pi (fun _ => D))`, matching `E_{S∼D^m}[·]` exactly.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 31, Definition 3.2 (PDF p. 48)

import Mathlib
import Definitions.Def_FoundationsML_RademacherVC_EmpiricalRademacherComplexity

open MeasureTheory

namespace FoundationsML.RademacherVC

/-- The (average) Rademacher complexity of a family `G` of functions `Z → ℝ`, for samples of
size `m` drawn i.i.d. from a distribution `D` on `Z` (Mohri, Rostamizadeh & Talwalkar,
*Foundations of Machine Learning*, 2nd ed., MIT Press 2018, Definition 3.2, p. 31, PDF p. 48):
`R_m(G) = E_{S∼D^m}[R̂_S(G)]`, the expectation of the empirical Rademacher complexity over an
i.i.d. sample of size `m`. -/
noncomputable def RademacherComplexity {Z : Type*} [MeasurableSpace Z]
    (D : Measure Z) (G : Set (Z → ℝ)) (m : ℕ) : ℝ :=
  ∫ S, EmpiricalRademacherComplexity G S ∂(Measure.pi (fun _ : Fin m => D))

end FoundationsML.RademacherVC


