-- Prove2me | Definitions.Def_Kyprianou_Ch06_certificate_exercise_6_5
-- name    : Kyprianou_Ch06_certificate_exercise_6_5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T22:26:21.327204+00:00
-- url     : https://prove2.me/theorems/630f2a30-c43c-46ae-bce4-3fac4157845f
-- title:
--   Full quantified certificate for exercise:6.5
-- statement:
--   Exact fully quantified source theorem/exercise as a Prop, generated from the authoritative live theorem telescope and target with no conclusion weakening.
-- source:
--   Kyprianou (2006), Exercise 6.5(i)–(ii), printed pp. 175–176; physical two-up PDF pp. 93–94.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_LevyKhintchineTriple
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch06_IndexedExcursion
import Definitions.Def_Kyprianou_Ch06_AdmissibleLocalTime
import Definitions.Def_Kyprianou_Ch06_RunningMaximumAndContact
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- Closed, full quantified source proposition from spectrallyNegativeDescendingLadderHeightTriplet. -/
def certificate_exercise_6_5 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (F : NNReal → MeasurableSpace Omega)
    (Ldown : NNReal → Omega → NNReal)
    (b mu : Real) (sigma2 : NNReal) (nu : Measure Real)
    (nuDesc : Measure NNReal)
    (driftDesc killDesc : NNReal)
    (hatKappa : Complex → Complex)
    (hX : IsRealLevyProcess P X)
    (hTriplet : IsLevyKhintchineTriplet P X b sigma2 nu)
    (hNoPositiveJumps : nu (Set.Ioi 0) = 0)
    (hMean : Integrable (X 1) P ∧
      (∫ omega, X 1 omega ∂P) = mu ∧ 0 < mu)
    (hDescLocal : IsAdmissibleLocalTimeAtMaximum P F
      (fun t omega => -X t omega) Ldown)
    (hDescLaw : ∀ (t beta : NNReal),
      (∫ omega,
        let tau := inverseLocalTime Ldown t omega
        if tau = ⊤ then (0 : Real)
        else Real.exp (-(beta : Real) *
          runningMaximum (fun s w => -X s w)
            (tau.untopD 0) omega) ∂P) =
        Real.exp (-(t : Real) *
          (hatKappa (↑(beta : Real) : Complex)).re))
    (hHatTriplet : ∀ beta : NNReal,
      hatKappa (↑(beta : Real) : Complex) =
        (↑((killDesc : Real) +
          (driftDesc : Real) * (beta : Real)) : Complex) +
        ↑((∫⁻ y : NNReal,
          ENNReal.ofReal
            (1 - Real.exp (-(beta : Real) * (y : Real)))
          ∂nuDesc).toReal)),
    -- (i) Integrated negative-tail mass is finite
    ((∫⁻ x in Set.Iio (-1 : Real),
      nu (Set.Iio x) ∂volume) < ⊤) ∧
    -- (ii) Descending Fourier exponent, with its source sign convention
    (∃ c : Real, 0 < c ∧
      (∀ theta : Real,
        hatKappa (Complex.I * (↑theta : Complex)) =
          (↑c : Complex) *
            ((↑mu : Complex) -
              Complex.I * (↑(theta * (sigma2 : Real) / 2) : Complex) +
              ∫ x in Set.Iio (0 : Real),
                (1 - Complex.exp (Complex.I *
                   (↑(theta * x) : Complex))) *
                (↑((nu (Set.Iio x)).toReal) : Complex) ∂volume)) ∧
      -- A positive deterministic rescaling of local time makes the
      -- descending height jump law nu(-infinity,-y)dy and drift sigma2/2
      -- with killing rate mu
      (∀ A : Set NNReal, MeasurableSet A →
        nuDesc A =
          ENNReal.ofReal c *
            (∫⁻ y in A ∩ Set.Ioi (0 : NNReal),
              nu (Set.Iio (-(y : Real))) ∂(Measure.map Real.toNNReal (volume.restrict (Set.Ici (0 : Real)))))) ∧
      (driftDesc : Real) = c * ((sigma2 : Real) / 2) ∧
      (killDesc : Real) = c * mu)

end Kyprianou.Ch06


