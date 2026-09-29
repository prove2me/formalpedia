-- Prove2me | Definitions.Def_FoundationsML_RademacherVC_GeneralizationError
-- name    : FoundationsML_RademacherVC_GeneralizationError
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:10:10.612223+00:00
-- url     : https://prove2.me/theorems/77019136-4583-4ca9-b1b7-de4b07d57619
-- title:
--   Generalization error (risk) of a hypothesis
-- statement:
--   **Definition 2.1 (Generalization error), p. 10, PDF p. 27.** Given a hypothesis
--   $h : X \to Y$, a target concept $c : X \to Y$, and an underlying distribution $D$ on $X$,
--   the generalization error (risk) of $h$ is $R(h) = \Pr_{x\sim D}[h(x) \ne c(x)]$. Restated
--   locally in this chunk's `RademacherVC` namespace (identical to chunk `02-pac`'s own copy)
--   since a draft module cannot import another chunk's draft.
--
--   **Formalization Note.** `GeneralizationError D c h` is `(D {x | h x ≠ c x}).toReal`.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 10, Definition 2.1 (PDF p. 27)

import Mathlib

open MeasureTheory

namespace FoundationsML.RademacherVC

/-- The generalization error (risk) of a hypothesis `h : X → Y` against a target concept
`c : X → Y` and an underlying distribution `D` on `X` (Mohri, Rostamizadeh & Talwalkar,
*Foundations of Machine Learning*, 2nd ed., MIT Press 2018, Definition 2.1, p. 10, PDF p. 27,
restated locally for this chapter since drafts cannot import another chunk's draft module):
`R(h) = P_{x∼D}[h(x) ≠ c(x)]`. -/
noncomputable def GeneralizationError {X Y : Type*} [MeasurableSpace X]
    (D : Measure X) (c h : X → Y) : ℝ :=
  (D {x | h x ≠ c x}).toReal

end FoundationsML.RademacherVC


