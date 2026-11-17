-- Prove2me | Definitions.Def_Kyprianou_Ch07_certificate_result_7_5
-- name    : Kyprianou_Ch07_certificate_result_7_5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-16T14:47:43.6604+00:00
-- url     : https://prove2.me/theorems/30b1a255-a24e-4b7d-8613-bc6e04ca3559
-- title:
--   Full quantified certificate for pathwiseTransienceRecurrenceCharacterisation
-- statement:
--   Source-exact closed quantified proposition obtained from the canonical parent theorem without dropping any binders or clauses.
-- source:
--   Kyprianou (2006), first edition, Theorem 7.5(i)–(ii), printed p.184; Windows Ky.pdf landscape sheet 97 (original single-page PDF p.193).

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch07_TransienceAndRecurrence
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch07

/-- Source-quantified full proposition of pathwiseTransienceRecurrenceCharacterisation. -/
def certificate_result_7_5 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X),
    ((IsTransientLevyProcess P X ↔
      ∀ᵐ omega ∂P,
        Tendsto (fun t : NNReal => |X t omega|) atTop atTop) ∧
     (¬ Kyprianou.Ch06.IsCompoundPoissonProcess P X →
      (IsRecurrentLevyProcess P X ↔
        ∀ x : Real, ∀ᵐ omega ∂P,
          ∀ epsilon : Real, 0 < epsilon →
            ∀ T : NNReal, ∃ t : NNReal,
              T ≤ t ∧ |X t omega - x| < epsilon)))

end Kyprianou.Ch07


