-- Prove2me | Definitions.Def_FoundationsML_MultiClass_MarginFunction
-- name    : FoundationsML_MultiClass_MarginFunction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:27:05.251072+00:00
-- url     : https://prove2.me/theorems/fe7d0362-5e85-4e36-9f15-30b233267ff9
-- title:
--   Margin function ρ_h(x,y)
-- statement:
--   **p. 215, PDF p. 232.** For a multi-class scoring function $h:X\times Y\to\mathbb R$, the
--   margin at a labeled example $(x,y)$ is $\rho_h(x,y) = h(x,y) - \max_{y'\ne y} h(x,y')$; $h$
--   misclassifies $(x,y)$ iff $\rho_h(x,y)\le0$.
--
--   **Formalization Note.** `⨆ y' ∈ {y'|y'≠y}, h(x,y')` is the real supremum over labels other
--   than `y`; for a finite `Y` with `2 ≤ Fintype.card Y` this equals the book's `max_{y'≠y}`.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 215 (PDF p. 232)

import Mathlib

namespace FoundationsML.MultiClass

/-- The margin `ρ_h(x,y)` of a multi-class scoring function `h : X × Y → ℝ` at a labeled
example `(x,y)` (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed.,
MIT Press 2018, p. 215, PDF p. 232): `ρ_h(x,y) = h(x,y) − max_{y'≠y} h(x,y')`. The hypothesis
`h` misclassifies `(x,y)` iff `ρ_h(x,y) ≤ 0`.

**Formalization Note.** `⨆ y' ∈ {y' | y' ≠ y}, h (x, y')` is the real supremum over the
(possibly infinite) set of labels other than `y`; for a finite `Y` with at least two elements
this equals the book's `max_{y'≠y}`, matching trap 5's guard whenever a consuming theorem
supplies `2 ≤ Fintype.card Y` (or an analogous nontriviality hypothesis). -/
noncomputable def MarginFunction {X Y : Type*} (h : X × Y → ℝ) (x : X) (y : Y) : ℝ :=
  h (x, y) - ⨆ y' ∈ {y' : Y | y' ≠ y}, h (x, y')

end FoundationsML.MultiClass


