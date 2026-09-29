-- Prove2me | Definitions.Def_FoundationsML_PAC_GeneralizationError
-- name    : FoundationsML_PAC_GeneralizationError
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:06:46.485229+00:00
-- url     : https://prove2.me/theorems/cf46b1ad-8511-4437-a332-877ef22d9a12
-- title:
--   Generalization error (risk) of a hypothesis
-- statement:
--   **Definition 2.1 (Generalization error), p. 10, PDF p. 27.** Given a hypothesis
--   $h : X \to Y$, a target concept $c : X \to Y$, and an underlying distribution $D$ on $X$,
--   the generalization error (risk) of $h$ is
--   $$R(h) = \Pr_{x\sim D}[h(x) \ne c(x)] = \mathbb{E}_{x\sim D}[\mathbb{1}_{h(x)\ne c(x)}].$$
--   This is the quantity every learning guarantee in the chapter bounds: it is not directly
--   observable by the learner, since both $D$ and $c$ are unknown.
--
--   **Formalization Note.** `GeneralizationError D c h` is `(D {x | h x ≠ c x}).toReal`, the
--   `D`-measure of the disagreement set cast to a real number; `X`, `Y` are left general (the
--   chapter's own running restriction to `Y = Bool` is imposed by the items that need it).
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 10, Definition 2.1 (PDF p. 27)

import Mathlib

open MeasureTheory

namespace FoundationsML.PAC

/-- The generalization error (risk) of a hypothesis `h : X → Y` against a target concept
`c : X → Y` and an underlying distribution `D` on `X` (Mohri, Rostamizadeh & Talwalkar,
*Foundations of Machine Learning*, 2nd ed., MIT Press 2018, Definition 2.1, p. 10, PDF p. 27):
`R(h) = P_{x∼D}[h(x) ≠ c(x)]`. -/
noncomputable def GeneralizationError {X Y : Type*} [MeasurableSpace X]
    (D : Measure X) (c h : X → Y) : ℝ :=
  (D {x | h x ≠ c x}).toReal

end FoundationsML.PAC


