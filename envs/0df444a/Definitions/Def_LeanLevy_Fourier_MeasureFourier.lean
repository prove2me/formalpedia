-- Prove2me | Definitions.Def_LeanLevy_Fourier_MeasureFourier
-- name    : LeanLevy_Fourier_MeasureFourier
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T21:57:57.123303+00:00
-- url     : https://prove2.me/theorems/980e7a26-ea4c-4b1e-9efb-b39e6afb84a5
-- title:
--   LeanLevy source module: Fourier.MeasureFourier
-- statement:
--   Source-faithful definition and structural-lemma bundle for `LeanLevy.Fourier.MeasureFourier`. It preserves the original Lean declarations, namespaces, assumptions and imported definitions. The upstream source is credited below. This is a draft pending Prove2Me compilation.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Fourier/MeasureFourier.lean

/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Fourier Transform of Finite Borel Measures

This file defines the Fourier transform (characteristic function) of a finite
Borel measure on ℝ using the probabilist convention `exp(iξx)`.

## Main definitions

* `MeasureTheory.FiniteMeasure.fourierTransform` — the Fourier transform of a
  finite measure μ, defined as `ξ ↦ ∫ x, exp(iξx) dμ(x)`.

## Main results

* `MeasureTheory.FiniteMeasure.norm_fourierTransform_le` — the Fourier transform
  is bounded by the total mass: `‖μ̂(ξ)‖ ≤ μ.mass`.
* `MeasureTheory.FiniteMeasure.continuous_fourierTransform` — the Fourier
  transform is continuous.
-/

open MeasureTheory Complex

namespace MeasureTheory.FiniteMeasure

variable (μ : FiniteMeasure ℝ)

/-- The Fourier transform of a finite Borel measure on ℝ, using the probabilist
convention: `μ̂(ξ) = ∫ x, exp(iξx) dμ(x)`. -/
noncomputable def fourierTransform (ξ : ℝ) : ℂ :=
  ∫ x : ℝ, exp (↑(ξ * x) * I) ∂(μ : Measure ℝ)







end MeasureTheory.FiniteMeasure


