-- Prove2me | Definitions.Def_ChapterSphericalBessel
-- name    : ChapterSphericalBessel
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T06:41:32.007556+00:00
-- url     : https://prove2.me/theorems/944ba8f7-d500-457c-a2b6-e4123c32a01f
-- title:
--   Chapter SphericalBessel
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterSphericalBessel.lean`): generated def bundle for ChapterSphericalBessel. See BookProof/ChapterSphericalBessel.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSphericalBessel.lean

import Mathlib


/-!
# Chapter — Hankel–Majorana transform: the spherical Bessel functions (Rayleigh formula)

Source: `book.tex`, §A.5 subsection *"Hankel–Majorana Transform"* (line ~5805),
Definitions 65–71.  There the author builds the spherical / Hankel–Majorana
transform out of the **spherical Bessel functions of the first kind** `jₗ`,
defined (Definition 67) by the **Rayleigh formula**

`jₗ(r) = rˡ (-(1/r) d/dr)ˡ (sin r / r)`.

These special functions are **not** available in Mathlib, so this file develops
the self-contained analytic core from scratch: the Rayleigh operator, the
generating function `j₀(r) = sin r / r`, and the first closed forms together
with the recurrence that links them and the defining second-order ODE.

Formalized here:

* `rayleighOp` — the Rayleigh differential operator `T f = -(1/r) f'`;
* `sbessel` — the spherical Bessel function via the book's Rayleigh formula
  `jₗ(r) = rˡ (Tˡ (sin r / r))(r)`;
* `sj0` / `sj1` / `sj2` — the classical closed forms
  `j₀ = sin r / r`, `j₁ = sin r / r² − cos r / r`,
  `j₂ = (3/r³ − 1/r) sin r − (3/r²) cos r`;
* `deriv_sbesselBase` — the derivative of the generator `sin r / r`;
* `sbessel_zero` / `sbessel_one_eq` / `sbessel_two_eq` — the Rayleigh formula
  reproduces the three closed forms;
* `rayleigh_raise_01` — the raising relation `j₁ = −(d/dr) j₀`;
* `sj0_satisfies_ode` — `j₀` solves the `l = 0` spherical Bessel ODE
  `r² j'' + 2 r j' + r² j = 0`.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`); no `EXTERNAL` hypothesis, no `axiom`.
-/

namespace BookProof.ChapterSphericalBessel

open scoped Topology

/-- The Rayleigh differential operator `T f (r) = -(1/r) · f'(r)`, used in the
book's Rayleigh formula for the spherical Bessel functions. -/
noncomputable def rayleighOp (f : ℝ → ℝ) : ℝ → ℝ := fun r => -(1 / r) * deriv f r

/-- The generating function `j₀(r) = sin r / r` of the spherical Bessel family. -/
noncomputable def sbesselBase : ℝ → ℝ := fun r => Real.sin r / r

/-- The spherical Bessel function of the first kind, defined by the book's
Rayleigh formula (Definition 67):
`jₗ(r) = rˡ (-(1/r) d/dr)ˡ (sin r / r)`. -/
noncomputable def sbessel (l : ℕ) : ℝ → ℝ :=
  fun r => r ^ l * (rayleighOp^[l] sbesselBase) r

/-- Closed form for `j₀`. -/
noncomputable def sj0 : ℝ → ℝ := fun r => Real.sin r / r

/-- Closed form for `j₁`. -/
noncomputable def sj1 : ℝ → ℝ := fun r => Real.sin r / r ^ 2 - Real.cos r / r

/-- Closed form for `j₂`. -/
noncomputable def sj2 : ℝ → ℝ :=
  fun r => (3 / r ^ 3 - 1 / r) * Real.sin r - 3 / r ^ 2 * Real.cos r













end BookProof.ChapterSphericalBessel


