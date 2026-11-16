-- Prove2me | Definitions.Def_Kyprianou_Ch06_certificate_result_6_19
-- name    : Kyprianou_Ch06_certificate_result_6_19
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T22:24:02.958498+00:00
-- url     : https://prove2.me/theorems/3694e649-46b3-446d-91d9-4af249c14153
-- title:
--   Full quantified certificate for result:6.19
-- statement:
--   Exact fully quantified source theorem/exercise as a Prop, generated from the authoritative live theorem telescope and target with no conclusion weakening.
-- source:
--   Kyprianou (2006), Corollary 6.19, printed p. 167; physical PDF p. 89. Implicit uniqueness-hypothesis issue documented in source_issues_20261115.md.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch06_AdmissibleWienerHopfFactor
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- Closed, full quantified source proposition from uniquenessOfAdmissibleWienerHopfFactors. -/
def certificate_result_6_19 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real) (p : Real)
    (psi : Real → Complex)
    (muPlus muMinus nuPlus nuMinus : Measure (NNReal × Real))
    (hp : 0 < p)
    (hX : IsRealLevyProcess P X)
    (hNonCompound : ¬ IsCompoundPoissonProcess P X)
    (hPsi : ∀ (t : NNReal) (theta : Real),
      (∫ omega,
        Complex.exp (Complex.I *
          (↑(theta * X t omega) : Complex)) ∂P) =
        Complex.exp (-(↑(t : Real) : Complex) * psi theta))
    (hPositive : IsAdmissibleWienerHopfFactor true muPlus)
    (hNegative : IsAdmissibleWienerHopfFactor false muMinus)
    (hPositive' : IsAdmissibleWienerHopfFactor true nuPlus)
    (hNegative' : IsAdmissibleWienerHopfFactor false nuMinus)
    (hFirst : ∀ (vartheta theta : Real),
      (∫ z : NNReal × Real,
        Complex.exp (Complex.I *
          (↑(vartheta * (z.1 : Real) + theta * z.2) : Complex)) ∂muPlus) *
      (∫ z : NNReal × Real,
        Complex.exp (Complex.I *
          (↑(vartheta * (z.1 : Real) + theta * z.2) : Complex)) ∂muMinus) =
        (↑p : Complex) /
          ((↑p : Complex) -
            Complex.I * (↑vartheta : Complex) + psi theta))
    (hSecond : ∀ (vartheta theta : Real),
      (∫ z : NNReal × Real,
        Complex.exp (Complex.I *
          (↑(vartheta * (z.1 : Real) + theta * z.2) : Complex)) ∂nuPlus) *
      (∫ z : NNReal × Real,
        Complex.exp (Complex.I *
          (↑(vartheta * (z.1 : Real) + theta * z.2) : Complex)) ∂nuMinus) =
        (↑p : Complex) /
          ((↑p : Complex) -
            Complex.I * (↑vartheta : Complex) + psi theta)),
    muPlus = nuPlus ∧ muMinus = nuMinus

end Kyprianou.Ch06


