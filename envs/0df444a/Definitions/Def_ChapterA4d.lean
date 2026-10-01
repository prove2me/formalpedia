-- Prove2me | Definitions.Def_ChapterA4d
-- name    : ChapterA4d
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T07:51:42.539465+00:00
-- url     : https://prove2.me/theorems/95bfbc64-9c56-49c4-91c5-ada8dc0961fa
-- title:
--   Chapter A4d
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterA4d.lean`): generated def bundle for ChapterA4d. See BookProof/ChapterA4d.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterA4d.lean

import Definitions.Def_ChapterA4c
import Mathlib


/-!
# Chapter A, §A.4 — Prop 79: the massless little group is `SE(2)`

This file continues work-package **N4** of `FORMALIZATION_ROADMAP.md`
(book §A.4, line 5636), formalizing the concrete **massless little group** of
**Proposition 79**, the companion of the massive `SU(2)` case in
`ChapterA4c.lean`.

For a **massless** particle the standard 4-momentum is the null vector
`n = e₀ + e₃ = (1,0,0,1)` (the book's `i l̸ = iγ⁰ + iγ³`), and the little
group `G_l := {T ∈ SL(2,ℂ) | T l̸ = l̸ T}` is exactly the stabiliser of `n`
under the covering map `Υ : SL(2,ℂ) → O(1,3)` of §A.3 (Note 47, see
`ChapterA3h.lean`).  The book records this as `G_l = SE(2)`.

Working on the concrete `2×2` Pauli model of `ChapterA3h.lean`
(`n·σ = σ⁰ + σ³ = diag(2,0)`), we prove:

* `upsilonC_nullCol` — the null-column sum of `Υ(T)` is
  `Υ(T)^μ_0 + Υ(T)^μ_3 = ½ tr(σ^μ T†(σ⁰+σ³)T)`, because `n·σ = σ⁰ + σ³`.
* `fixesNullAxis_iff_conj` — `Υ(T)` fixes `n` **iff** `T†(σ⁰+σ³)T = σ⁰+σ³`.
* `nullConj_iff_form` — that matrix identity holds **iff** `T` is lower
  triangular with unit-modulus top-left entry (`T 0 1 = 0 ∧ |T 0 0| = 1`).
* `massless_little_group` — the headline: the massless little group
  `{T ∈ SL(2,ℂ) | Υ(T) fixes n}` equals `SEtwo`, the lower-triangular
  unimodular subgroup with unit-modulus diagonal — the standard realization of
  (the double cover of) `SE(2) = ℝ² ⋊ SO(2)`.
* `SEtwo_lower_triangular` — the explicit `SE(2)` shape `T = !![a,0;c,a⁻¹]`
  with `|a| = 1` (angle `∈ SO(2)`, translation `c ∈ ℂ ≅ ℝ²`).
* `upsilon_massless_lorentz` — each such `Υ(T)` is a genuine Lorentz
  transformation fixing the null axis.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`); no `EXTERNAL` hypothesis is used.
-/

open Matrix
open scoped ComplexConjugate

namespace BookProof.ChapterA3

/-- A real `4×4` matrix **fixes the null axis** `n = e₀ + e₃ = (1,0,0,1)`,
i.e. the sum of its `0`-th and `3`-rd columns is `n`. -/
def FixesNullAxis (Λ : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  ∀ μ, Λ μ 0 + Λ μ 3 = (if μ = 0 then 1 else 0) + (if μ = 3 then 1 else 0)

/-- `SE(2)`, the massless little group, realized as the lower-triangular
unimodular `2×2` complex matrices with unit-modulus top-left entry.  Together
with `det = 1` this forces `T = !![a,0;c,a⁻¹]` with `|a| = 1`. -/
def SEtwo : Set (Matrix (Fin 2) (Fin 2) ℂ) :=
  {T | T.det = 1 ∧ T 0 1 = 0 ∧ Complex.normSq (T 0 0) = 1}









/-
The matrix identity `T†(σ⁰+σ³)T = σ⁰+σ³` holds iff `T` is lower triangular
with unit-modulus top-left entry.
-/








end BookProof.ChapterA3


