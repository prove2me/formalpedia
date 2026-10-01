-- Prove2me | Definitions.Def_ChapterA4c
-- name    : ChapterA4c
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T03:17:32.468551+00:00
-- url     : https://prove2.me/theorems/3314cf9d-77af-4610-adf6-d96cb5c7cf9d
-- title:
--   Chapter A4c
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterA4c.lean`): generated def bundle for ChapterA4c. See BookProof/ChapterA4c.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterA4c.lean

import Mathlib


/-!
# Chapter A, §A.4 — Prop 79: the massive little group is `SU(2)`

This file continues work-package **N4** of `FORMALIZATION_ROADMAP.md`
(book §A.4, line 5636), formalizing the concrete **massive little group** of
**Proposition 79**.

The little group `G_l := {T ∈ SL(2,ℂ) | T l̸ = l̸ T}` of a standard 4-momentum
`l` is realized in the `SL(2,ℂ)` covering picture of §A.3 (Note 47, the map
`Υ : SL(2,ℂ) → O(1,3)`, see `ChapterA3h.lean`).  For a **massive** particle the
standard momentum points along the time axis `e₀ = (1,0,0,0)`, and the little
group is exactly the stabiliser of `e₀` under `Υ`.  The book records this as
`i l̸ = iγ⁰ ⇒ G_l = SU(2)`.

Working on the concrete `2×2` Pauli model of `ChapterA3h.lean`, we prove:

* `upsilonC_timeCol` — the time column of the Lorentz matrix `Υ(T)` is
  `Υ(T)^μ_0 = ½ tr(σ^μ T† T)`, because `σ⁰ = 1` (so `T† σ⁰ T = T† T`).
* `fixesTimeAxis_iff_unitary` — `Υ(T)` fixes the time axis `e₀` **iff** `T` is
  unitary (`T† T = 1`).  (This needs no `det T = 1` hypothesis: the reconstruction
  identity for the Pauli basis already forces `T† T = 1`.)
* `massive_little_group` — the headline: the massive little group
  `{T ∈ SL(2,ℂ) | Υ(T) e₀ = e₀}` equals `SU(2) = {T | det T = 1 ∧ T† T = 1}`.
* `upsilon_little_group_lorentz` — each such `Υ(T)` is a genuine Lorentz
  transformation fixing the time axis, i.e. a spatial rotation.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`); no `EXTERNAL` hypothesis is used.
-/

open Matrix
open scoped ComplexConjugate

namespace BookProof.ChapterA3

/-- A real `4×4` matrix **fixes the time axis** `e₀ = (1,0,0,0)`, i.e. its
`0`-th column is `e₀`. -/
def FixesTimeAxis (Λ : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  ∀ μ, Λ μ 0 = if μ = 0 then 1 else 0

/-- `SU(2)`, the special unitary group, as `2×2` complex matrices:
unimodular (`det = 1`) and unitary (`T† T = 1`). -/
def SUtwo : Set (Matrix (Fin 2) (Fin 2) ℂ) :=
  {T | T.det = 1 ∧ Tᴴ * T = 1}













end BookProof.ChapterA3


