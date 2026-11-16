-- Prove2me | Definitions.Def_Kyprianou_Ch05_WeakPassageObservables
-- name    : Kyprianou_Ch05_WeakPassageObservables
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T09:27:19.600236+00:00
-- url     : https://prove2.me/theorems/633c80de-788c-473d-948f-b6cc6552df27
-- title:
--   Test-function characterisation of two-dimensional weak first-passage laws
-- statement:
--   A test class of bounded continuous functions on bivariate passage states; explicit expectation of joint overshoot/undershoot with finite passage conditioning; corresponding level-normalised expectation; exact alpha*sin(pi*alpha)/pi density and integral for Dynkin-Lamperti weak limits. No asymptotic assertion is assumed.
-- source:
--   Kyprianou (2006), Theorems 5.7 and 5.16, first edition, pp.121, 130-131.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
namespace Kyprianou.Ch05

/-- A bounded continuous test function on the joint overshoot/undershoot state. -/
def IsBoundedContinuousTest (f : Real × Real → Real) : Prop :=
  Continuous f ∧ ∃ M : Real, 0 ≤ M ∧ ∀ z : Real × Real, |f z| ≤ M

/-- Unscaled joint passage test integral: passage at infinity contributes zero. -/
noncomputable def passageTestExpectation
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (Y Yleft : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (x : Real) (f : Real × Real → Real) : Real := by
  classical
  exact ∫ omega : Omega,
    if PassageFinite Y death x omega then
      f (passageOvershoot Y death x omega,
         passageUndershoot Y Yleft death x omega)
    else 0 ∂P

/-- Rescaled joint passage test integral for Dynkin-Lamperti limits. -/
noncomputable def scaledPassageTestExpectation
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (Y Yleft : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (x : Real) (f : Real × Real → Real) : Real := by
  classical
  exact ∫ omega : Omega,
    if PassageFinite Y death x omega then
      f (passageOvershoot Y death x omega / x,
         passageUndershoot Y Yleft death x omega / x)
    else 0 ∂P

/-- The two-dimensional Dynkin-Lamperti limiting density on
overshoot u>0, undershoot fraction 0<=y<1, with alpha in (0,1). -/
noncomputable def dynkinLampertiDensity
    (alpha u y : Real) : Real :=
  (alpha * Real.sin (Real.pi * alpha) / Real.pi) *
     (1-y) ^ (alpha-1) * (y+u) ^ (-alpha-1)

/-- Integrate a test function against the full joint limiting law. -/
noncomputable def dynkinLampertiTestIntegral
    (alpha : Real) (f : Real × Real → Real) : Real :=
  ∫ u in Set.Ioi (0 : Real),
    ∫ y in Set.Ico (0 : Real) 1,
       dynkinLampertiDensity alpha u y * f (u,y) ∂volume ∂volume

end Kyprianou.Ch05


