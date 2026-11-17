-- Prove2me | Definitions.Def_Kyprianou_Ch07_certificate_exercise_7_2
-- name    : Kyprianou_Ch07_certificate_exercise_7_2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-16T14:58:41.227931+00:00
-- url     : https://prove2.me/theorems/1795aae9-b681-4b40-801d-f630fefab284
-- title:
--   Full quantified certificate for exercise7_2StrongLawAllParts
-- statement:
--   Source-exact closed quantified proposition obtained from the canonical parent theorem without dropping any binders or clauses.
-- source:
--   Kyprianou (2006), Exercise 7.2(i)–(iv), printed p.207; original single-page PDF p.216; Windows Ky.pdf sheet 109.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch07_UnitTimeOscillationObservables
import Definitions.Def_Kyprianou_Ch07_LevyMeanAndTailTests
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch07

/-- Source-quantified full proposition of exercise7_2StrongLawAllParts. -/
def certificate_exercise_7_2 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X),
    ((Integrable (fun omega => |X 1 omega|) P →
      ((∀ n : Nat, Integrable (maximalUnitIncrement X n) P) ∧
       (∀ᵐ omega ∂P,
         Tendsto (fun n : Nat =>
           maximalUnitIncrement X n omega / (n : Real))
           atTop (nhds (0 : Real))) ∧
       (∀ᵐ omega ∂P,
         Tendsto (fun t : NNReal => X t omega / (t : Real))
           atTop (nhds (∫ omega, X 1 omega ∂P))))) ∧
     (positiveMeanPart P X = ⊤ ∧ negativeMeanPart P X < ⊤ →
       (∀ᵐ omega ∂P,
         Tendsto (fun t : NNReal => X t omega / (t : Real))
           atTop atTop)))

end Kyprianou.Ch07


