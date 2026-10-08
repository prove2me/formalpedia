-- Prove2me | Definitions.Def_FoundationsML_MultiClass_RademacherComplexity_v2
-- name    : FoundationsML_MultiClass_RademacherComplexity_v2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T05:32:09.54841+00:00
-- url     : https://prove2.me/theorems/41153e08-2fbb-4af5-889d-a20183b7d830
-- title:
--   Rademacher complexity (Definition 3.2) — corrected, MultiClass chapter copy
-- statement:
--   **Definition 3.2 (Rademacher complexity), p. 31, PDF p. 48.** Let $D$ denote the distribution according to which samples are drawn. For any integer $m\ge1$, the Rademacher complexity of $G$ is the expectation of the empirical Rademacher complexity over all samples of size $m$ drawn according to $D$:
--   $$R_m(G) = \mathbb E_{S\sim D^m}[\hat R_S(G)].$$
--
--   **Formalization Note.** Corrected re-issue of the retired module of the same name, built on the corrected `EmpiricalRademacherComplexity` (`_v2`, supremum over exactly $G$). The Bochner integral returns `0` for an integrand that is not a.e. strongly measurable; the book's footnote 3 (p. 30) assumes that the supremum in Definition 3.1 is measurable, and every theorem using this definition carries that assumption explicitly as `Measurable (fun S => R̂_S(G))`, which together with Definition 3.1's boundedness of $G$ makes the integrand integrable and the value the book's expectation.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 31, Definition 3.2 (PDF p. 48)

import Mathlib
import Definitions.Def_FoundationsML_MultiClass_EmpiricalRademacherComplexity_v2

open MeasureTheory

namespace FoundationsML.MultiClass

/-- The (average) Rademacher complexity of a family `G` of functions `Z → ℝ`, for samples of
size `m` drawn i.i.d. from a distribution `D` on `Z` (Mohri, Rostamizadeh & Talwalkar,
*Foundations of Machine Learning*, 2nd ed., MIT Press 2018, Definition 3.2, p. 31, PDF p. 48):
`R_m(G) = E_{S∼D^m}[R̂_S(G)]`, the expectation of the empirical Rademacher complexity over an
i.i.d. sample of size `m` (Definition 3.2 states it for `m ≥ 1`).

**Formalization Note.** Built on the corrected `EmpiricalRademacherComplexity` (module
`..._EmpiricalRademacherComplexity_v2`, supremum over exactly `G`). The Bochner integral
returns `0` for an integrand that is not a.e. strongly measurable; the book's footnote 3 (p. 30)
assumes that the supremum in Definition 3.1 is measurable, and every theorem using this
definition carries that assumption explicitly as `Measurable (fun S => R̂_S(G))`, which with
Definition 3.1's boundedness of `G` makes the integrand integrable and the value the book's
expectation. -/
noncomputable def RademacherComplexity {Z : Type*} [MeasurableSpace Z]
    (D : Measure Z) (G : Set (Z → ℝ)) (m : ℕ) : ℝ :=
  ∫ S, EmpiricalRademacherComplexity G S ∂(Measure.pi (fun _ : Fin m => D))

end FoundationsML.MultiClass


