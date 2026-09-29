-- Prove2me | Definitions.Def_SupportVectorMachines_Regression_IsRademacherSequence
-- name    : SupportVectorMachines_Regression_IsRademacherSequence
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:13:25.898001+00:00
-- url     : https://prove2.me/theorems/f56199f7-135c-46ba-af7a-4784bc6d55cd
-- title:
--   A Rademacher sequence
-- statement:
--   A finite family $\varepsilon_1,\dots,\varepsilon_n : \Theta \to \mathbb R$ **is a Rademacher
--   sequence with respect to a distribution $\nu$ on $\Theta$** (Steinwart & Christmann, *Support
--   Vector Machines*, Springer 2008, p. 535, just before Theorem A.8.1) if the $\varepsilon_i$ are
--   independent and each takes the values $1$ and $-1$ with $\nu$-probability $1/2$ each.
--   Rademacher sequences are the randomization device behind the symmetrization technique this
--   mission's goal (Lemma 9.2) and its two milestones are built on.
--
--   **Formalization Note** Independence is Mathlib's `ProbabilityTheory.iIndepFun`; "value $\pm1$
--   with probability $1/2$" is stated directly as `ν {θ | ε i θ = 1} = 1/2 ∧ ν {θ | ε i θ = -1} =
--   1/2` for every `i`, matching the book's `ν(εᵢ=1) = ν(εᵢ=-1) = 1/2` verbatim rather than via a
--   named Mathlib distribution (no ready-made "Rademacher distribution" object was found in this
--   Mathlib revision).
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, p. 535

import Mathlib

open MeasureTheory ProbabilityTheory

namespace SupportVectorMachines.Regression

/-- A finite family `ε : Fin n → Θ → ℝ` **is a Rademacher sequence with respect to `ν`**
(Steinwart & Christmann, *Support Vector Machines*, Springer 2008, p. 535, before Theorem A.8.1,
restated locally per Hard Rule 9): the `εᵢ` are independent, and each `εᵢ` takes the values `1`
and `-1` each with `ν`-probability `1/2`. -/
def IsRademacherSequence {Θ : Type*} [MeasurableSpace Θ] {n : ℕ} (ε : Fin n → Θ → ℝ)
    (ν : Measure Θ) : Prop :=
  (∀ i, Measurable (ε i)) ∧ iIndepFun ε ν ∧
    ∀ i, ν {θ : Θ | ε i θ = 1} = 1 / 2 ∧ ν {θ : Θ | ε i θ = -1} = 1 / 2

end SupportVectorMachines.Regression


