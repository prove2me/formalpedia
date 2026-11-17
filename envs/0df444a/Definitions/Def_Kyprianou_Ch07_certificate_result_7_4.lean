-- Prove2me | Definitions.Def_Kyprianou_Ch07_certificate_result_7_4
-- name    : Kyprianou_Ch07_certificate_result_7_4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-16T14:47:18.119756+00:00
-- url     : https://prove2.me/theorems/775e53ef-59bb-46da-8c16-03ba50a933f8
-- title:
--   Full quantified certificate for portStoneFourierTransienceCriterion
-- statement:
--   Source-quantified exact proposition of the amended theorem 7.4, including its explicitly documented zero-process exception.
-- source:
--   Kyprianou (2006), first edition, Theorem 7.4, printed p.184; Windows Ky.pdf landscape sheet 97 (original single-page p.193).

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch07_TransienceAndRecurrence
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch07

/-- Source-quantified full proposition of portStoneFourierTransienceCriterion. -/
def certificate_result_7_4 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (Psi : Real → Complex)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X)
    (hExponent : ∀ (t : NNReal) (theta : Real),
      (∫ omega, Complex.exp
        (Complex.I * (theta : Complex) * (X t omega : Complex)) ∂P) =
      Complex.exp (-((t : Real) : Complex) * Psi theta)),
    let finiteFourierOccupation : Prop :=
      ∃ epsilon : Real, 0 < epsilon ∧
        (∀ theta : Real, theta ∈ Set.Ioo (-epsilon) epsilon →
          theta ≠ 0 → Psi theta ≠ 0) ∧
        IntegrableOn (fun theta : Real => (1 / Psi theta).re)
          (Set.Ioo (-epsilon) epsilon) volume
    (IsTransientLevyProcess P X ↔ finiteFourierOccupation) ∧
    (IsRecurrentLevyProcess P X ↔ ¬ finiteFourierOccupation)

end Kyprianou.Ch07


