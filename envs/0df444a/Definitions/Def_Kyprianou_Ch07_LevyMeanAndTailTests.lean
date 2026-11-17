-- Prove2me | Definitions.Def_Kyprianou_Ch07_LevyMeanAndTailTests
-- name    : Kyprianou_Ch07_LevyMeanAndTailTests
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-16T14:46:13.739206+00:00
-- url     : https://prove2.me/theorems/ec58db1d-10e8-4384-8568-7379dfd218ed
-- title:
--   Theorem 7.2: extended Lévy means and jump-tail integral tests
-- statement:
--   Defines the positive and negative parts of the time-one Lévy increment's extended expectation. The mean is undefined exactly when both parts are infinite. Introduces the two improper Lévy-measure ratio integrals of Theorem 7.2, with integrated negative and positive jump tails as denominators.
-- source:
--   Kyprianou (2006), Theorem 7.2, printed p.183; Windows Ky.pdf two-page sheet 97 (original p.192).

import Mathlib
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch07

/-- Positive part of the time-one Lévy increment's extended expectation. -/
noncomputable def positiveMeanPart
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (X : NNReal → Omega → Real) : ENNReal :=
  ∫⁻ omega, ENNReal.ofReal (X 1 omega) ∂P

/-- Negative part of the time-one Lévy increment's extended expectation. -/
noncomputable def negativeMeanPart
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (X : NNReal → Omega → Real) : ENNReal :=
  ∫⁻ omega, ENNReal.ofReal (-X 1 omega) ∂P

/-- The time-one mean is undefined precisely when both parts diverge. -/
def HasUndefinedLevyMean
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (X : NNReal → Omega → Real) : Prop :=
  positiveMeanPart P X = ⊤ ∧ negativeMeanPart P X = ⊤

/-- Integral of the negative-jump Lévy-measure tail over (0,u). -/
noncomputable def negativeIntegratedTail
    (Pi : Measure Real) (u : Real) : ENNReal :=
  ∫⁻ y : Real in Set.Ioo 0 u, Pi (Set.Iio (-y)) ∂volume

/-- Integral of the positive-jump Lévy-measure tail over (0,u). -/
noncomputable def positiveIntegratedTail
    (Pi : Measure Real) (u : Real) : ENNReal :=
  ∫⁻ y : Real in Set.Ioo 0 u, Pi (Set.Ioi y) ∂volume

/-- Theorem 7.2(i): large positive jump ratio integral. -/
noncomputable def negativeDriftTailTest (Pi : Measure Real) : ENNReal :=
  ∫⁻ x : Real in Set.Ioi 1,
    (ENNReal.ofReal x) / negativeIntegratedTail Pi x ∂Pi

/-- Theorem 7.2(ii): large negative jump ratio integral. -/
noncomputable def positiveDriftTailTest (Pi : Measure Real) : ENNReal :=
  ∫⁻ x : Real in Set.Iio (-1),
    (ENNReal.ofReal |x|) / positiveIntegratedTail Pi |x| ∂Pi

end Kyprianou.Ch07


