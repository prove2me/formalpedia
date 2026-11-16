-- Prove2me | Definitions.Def_Kyprianou_Ch05_TailRatioClassL
-- name    : Kyprianou_Ch05_TailRatioClassL
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T09:28:56.005265+00:00
-- url     : https://prove2.me/theorems/35dc57d7-c0d4-4745-b2f7-c502e9db0848
-- title:
--   Class L(alpha) tail ratios and exact conditional overshoot notation
-- statement:
--   Class L(alpha) on finite nonnegative potential measures, explicitly non-lattice with strictly positive tails, all positive shift ratios e^(-alpha*y), plus exact conditional overshoot Laplace numerator and source G-tail expression.
-- source:
--   Kyprianou (2006) Exercise 5.8 pp.137-138.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- The finite renewal/potential measure belongs to the exact class L(alpha):
non-lattice, supported nonnegative, strictly positive tails and every positive
tail-shift ratio converges to exp(-alpha*y). -/
def IsTailRatioClassL (U : Measure Real) (alpha : Real) : Prop :=
  0 ≤ alpha ∧
  U (Set.Iio (0 : Real)) = 0 ∧
  U Set.univ < ⊤ ∧
  NonLatticeMeasure U ∧
  (∀ x : Real, 0 ≤ x → 0 < (U (Set.Ioi x)).toReal) ∧
  ∀ y : Real, 0 < y →
    Tendsto (fun x : Real =>
       (U (Set.Ioi (x+y))).toReal /
         (U (Set.Ioi x)).toReal) atTop
      (nhds (Real.exp (-alpha*y)))

/-- Original class-L asymptotic conditional overshoot tail (5.8). -/
noncomputable def limitingKilledOvershootTail
    (eta alpha : Real) (Phi : Real → Real)
    (Pi : Measure Real) (u : Real) : Real :=
  (Real.exp (-alpha*u) / eta) *
    (Phi (-alpha) +
      ∫ z in Set.Ioi u, (Real.exp (alpha*z) -
                         Real.exp (alpha*u)) ∂Pi)

/-- Finite crossing conditional expectation as an actual ratio. -/
noncomputable def conditionalOvershootTransform
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (beta x : Real) : Real :=
  let p := (P {omega : Omega | PassageFinite Y death x omega}).toReal
  (∫ omega in {omega : Omega | PassageFinite Y death x omega},
     Real.exp (-beta*passageOvershoot Y death x omega) ∂P) / p

end Kyprianou.Ch05


