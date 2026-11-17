-- Prove2me | Definitions.Def_Kyprianou_Ch07_certificate_result_7_10
-- name    : Kyprianou_Ch07_certificate_result_7_10
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-16T14:52:13.456199+00:00
-- url     : https://prove2.me/theorems/c1f63d8e-2122-48bc-9488-81d5d98f2417
-- title:
--   Full quantified certificate for upwardCreepingLadderDrift
-- statement:
--   Source-exact closed quantified proposition obtained from the canonical parent theorem without dropping any binders or clauses.
-- source:
--   Kyprianou (2006), Lemma 7.10, printed p.197, Windows Ky.pdf two-page sheet 104 (original p.206).

import Mathlib
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch06_AdmissibleLocalTime
import Definitions.Def_Kyprianou_Ch06_IndexedExcursion
import Definitions.Def_Kyprianou_Ch06_RunningMaximumAndContact
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch07

/-- Source-quantified full proposition of upwardCreepingLadderDrift. -/
def certificate_result_7_10 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (F : NNReal → MeasurableSpace Omega)
    (L : NNReal → Omega → NNReal)
    (kappa : Complex → Complex → Complex)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X)
    (hNonCompound : ¬ Kyprianou.Ch06.IsCompoundPoissonProcess P X)
    (hL : Kyprianou.Ch06.IsAdmissibleLocalTimeAtMaximum P F X L)
    (hKappa : ∀ (a b : Complex),
      0 ≤ a.re → 0 ≤ b.re → ∀ t : NNReal,
      (∫ omega,
        let tau := Kyprianou.Ch06.inverseLocalTime L t omega
        if tau = ⊤ then (0 : Complex)
        else Complex.exp
          (-a * (↑((tau.untopD 0 : NNReal) : Real) : Complex) -
            b * (↑(Kyprianou.Ch06.runningMaximum X
                (tau.untopD 0) omega) : Complex)) ∂P) =
        Complex.exp (-((t : Real) : Complex) * kappa a b)),
    ∀ x : Real, 0 < x →
      ((0 < Kyprianou.Ch05.creepingProbability
        P X (fun _ => (⊤ : WithTop NNReal)) x) ↔
        ∃ d : Real, 0 < d ∧
          Tendsto (fun beta : Real =>
            (kappa 0 (beta : Complex)).re / beta)
            atTop (nhds d))

end Kyprianou.Ch07


