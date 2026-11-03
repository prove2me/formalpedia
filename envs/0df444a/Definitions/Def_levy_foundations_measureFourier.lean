-- Prove2me | Definitions.Def_levy_foundations_measureFourier
-- name    : levy_foundations_measureFourier
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T14:23:48.17491+00:00
-- url     : https://prove2.me/theorems/91d6fbf2-f823-4fb6-81fa-b943925b7121
-- title:
--   Fourier transform of a finite measure on the real line
-- statement:
--   For a finite Borel measure μ on ℝ, its Fourier transform at ξ is the integral of exp(i ξ x) against μ. This fixes the characteristic-function convention for the mission.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Fourier/MeasureFourier.lean#L36-L40. Fourier transform definition. Independent Prove2Me statement, pending audit and remote compilation.

import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Complex.Trigonometric

open MeasureTheory
namespace LevyFoundations
noncomputable def measureFourier (μ : FiniteMeasure ℝ) (ξ : ℝ) : ℂ :=
  ∫ x : ℝ, Complex.exp (↑(ξ * x) * Complex.I) ∂(μ : Measure ℝ)
end LevyFoundations


