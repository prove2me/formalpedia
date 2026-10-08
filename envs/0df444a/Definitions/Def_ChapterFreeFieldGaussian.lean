-- Prove2me | Definitions.Def_ChapterFreeFieldGaussian
-- name    : ChapterFreeFieldGaussian
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-04T21:40:56.970766+00:00
-- url     : https://prove2.me/theorems/01127459-7d2d-4667-90fa-f35a227d9bd2
-- title:
--   Chapter FreeFieldGaussian
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterFreeFieldGaussian.lean`): generated def bundle for ChapterFreeFieldGaussian. See BookProof/ChapterFreeFieldGaussian.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFreeFieldGaussian.lean

import Mathlib


/-!
# Chapter "Wave-function parametrization of a probability measure", §5 —
# Free field parametrization: the standard Gaussian prior is rotation-invariant

Source: `book.tex`, chapter *"Wave-function parametrization of a probability
measure"*, section *"5. Free field parametrization in Bayesian inference and
Statistical Mechanics"* (`book.tex` line ~1706).

The book's §5 justifies the **free field parametrization** — a uniform
(Lebesgue-like) prior on an infinite-dimensional sphere — by the classical fact
that, although there is *no* infinite-dimensional Lebesgue measure
(`ChapterNoLebesgue`), one can build a rotation-invariant "uniform" prior out of
the **Gaussian measure** and the Fock space:

> "it is well known since many decades that a uniform (Lebesgue-like) measure of
> an infinite-dimensional sphere can be defined using the Gaussian measure and
> the Fock-space."

The self-contained finite-dimensional mathematical heart of that statement is:
*the standard (centered, unit-variance) Gaussian measure on `ℝⁿ` is invariant
under every orthogonal transformation* — i.e. it is rotationally symmetric, so
that after radial normalization it induces the uniform measure on the sphere.
This file formalizes that fact over `EuclideanSpace ℝ (Fin n)`.

We model the standard `n`-dimensional Gaussian as the product of `n` copies of
the one-dimensional standard normal `gaussianReal 0 1`, transported to the
Euclidean (L²) inner-product space via the measurable identity `WithLp.toLp 2`.

## Main results

* `stdGaussian` — the standard Gaussian measure on `EuclideanSpace ℝ (Fin n)`.
* `instance : IsProbabilityMeasure (stdGaussian n)` — it is a probability
  measure (the Bayesian prior).
* `charFun_stdGaussian` — its characteristic function is the standard Gaussian
  form `t ↦ exp(-‖t‖²/2)`, depending only on the norm `‖t‖` (rotational
  symmetry at the level of the characteristic function).
* **headline** `stdGaussian_map_linearIsometryEquiv` — for every orthogonal map
  `L` (a linear isometry equivalence of `EuclideanSpace ℝ (Fin n)`) the
  pushforward `(stdGaussian n).map L` equals `stdGaussian n`: the standard
  Gaussian prior is rotation-invariant.

Everything is intended to be `sorry`-free and axiom-clean (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open MeasureTheory ProbabilityTheory Complex WithLp
open scoped RealInnerProductSpace ENNReal

namespace BookProof.ChapterFreeFieldGaussian

variable {n : ℕ}

/-- The **standard `n`-dimensional Gaussian measure** on
`EuclideanSpace ℝ (Fin n)`: the product of `n` independent standard normals
`gaussianReal 0 1`, transported to the Euclidean (L²) inner-product structure by
the measurable identity `WithLp.toLp 2`.  This is the book's free-field Gaussian
prior in finite dimension. -/
noncomputable def stdGaussian (n : ℕ) : Measure (EuclideanSpace ℝ (Fin n)) :=
  (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).map (WithLp.toLp 2)

/-- The standard Gaussian is a probability measure — a legitimate Bayesian
prior. -/
instance instIsProbabilityMeasure_stdGaussian (n : ℕ) :
    IsProbabilityMeasure (stdGaussian n) := by
  constructor;
  unfold stdGaussian;
  rw [ Measure.map_apply ];
  · simp ;
  · fun_prop;
  · exact MeasurableSet.univ





end BookProof.ChapterFreeFieldGaussian


