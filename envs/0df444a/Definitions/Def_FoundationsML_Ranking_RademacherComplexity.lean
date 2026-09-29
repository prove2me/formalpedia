-- Prove2me | Definitions.Def_FoundationsML_Ranking_RademacherComplexity
-- name    : FoundationsML_Ranking_RademacherComplexity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:38:10.840577+00:00
-- url     : https://prove2.me/theorems/c205dd17-e06a-4819-a607-c459bd9736dd
-- title:
--   (Average) Rademacher complexity (Definition 3.2), specialized to R_m^{D1}/R_m^{D2}
-- statement:
--   **Definition 3.2, p. 31, PDF p. 48; specialized at p. 241, PDF p. 258.** $R_m(G) =
--   \mathbb E_{S\sim D^m}[\hat R_S(G)]$; applied with $D$ set to a ranking distribution's
--   marginal $D_1$ (`Measure.map Prod.fst D`) or $D_2$ (`Measure.map Prod.snd D`), this gives
--   the chapter's own $R_m^{D_1}(H)$/$R_m^{D_2}(H)$.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 31, Definition 3.2 (PDF p. 48)

import Mathlib
import Definitions.Def_FoundationsML_Ranking_EmpiricalRademacherComplexity

open MeasureTheory

namespace FoundationsML.Ranking

/-- The (average) Rademacher complexity of a family `G` of functions `Z → ℝ`, for samples of
size `m` drawn i.i.d. from a distribution `D` on `Z` (Mohri, Rostamizadeh & Talwalkar,
*Foundations of Machine Learning*, 2nd ed., MIT Press 2018, Definition 3.2, p. 31, PDF p. 48,
restated locally for this chapter since drafts cannot import another chunk's draft module):
`R_m(G) = E_{S∼D^m}[R̂_S(G)]`. Applied with `D` set to the marginal `D1`/`D2` of a ranking
distribution, this gives the chapter's own `R_m^{D1}(H)`/`R_m^{D2}(H)` (p. 241, PDF p. 258). -/
noncomputable def RademacherComplexity {Z : Type*} [MeasurableSpace Z]
    (D : Measure Z) (G : Set (Z → ℝ)) (m : ℕ) : ℝ :=
  ∫ S, EmpiricalRademacherComplexity G S ∂(Measure.pi (fun _ : Fin m => D))

end FoundationsML.Ranking


