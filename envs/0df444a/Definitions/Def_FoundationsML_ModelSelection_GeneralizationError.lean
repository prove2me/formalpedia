-- Prove2me | Definitions.Def_FoundationsML_ModelSelection_GeneralizationError
-- name    : FoundationsML_ModelSelection_GeneralizationError
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:16:34.274621+00:00
-- url     : https://prove2.me/theorems/fcd17f1f-d612-48af-8337-10e16ee32d1b
-- title:
--   Generalization error (risk) of a hypothesis
-- statement:
--   **Definition 2.1 (Generalization error), p. 11, PDF p. 28.** Given a hypothesis
--   $h : X \to Y$, a target concept $c : X \to Y$, and an underlying distribution $D$ on $X$,
--   the generalization error (risk) of $h$ is $R(h) = \Pr_{x\sim D}[h(x) \ne c(x)]$. Restated
--   locally in this chunk's `ModelSelection` namespace since a draft module cannot import
--   another chunk's draft.
--
--   **Formalization Note.** `GeneralizationError D c h` is `(D {x | h x ≠ c x}).toReal`.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 11, Definition 2.1 (PDF p. 28)

import Mathlib

open MeasureTheory

namespace FoundationsML.ModelSelection

/-- The generalization error (risk) of a hypothesis `h : X → Y` against a target concept
`c : X → Y` and an underlying distribution `D` on `X` (Mohri, Rostamizadeh & Talwalkar,
*Foundations of Machine Learning*, 2nd ed., MIT Press 2018, Definition 2.1, p. 11, PDF p. 28,
restated locally for this chapter since drafts cannot import another chunk's draft module):
`R(h) = P_{x∼D}[h(x) ≠ c(x)]`. -/
noncomputable def GeneralizationError {X Y : Type*} [MeasurableSpace X]
    (D : Measure X) (c h : X → Y) : ℝ :=
  (D {x | h x ≠ c x}).toReal

end FoundationsML.ModelSelection


