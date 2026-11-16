-- Prove2me | Definitions.Def_Kyprianou_Ch06_certificate_result_6_9
-- name    : Kyprianou_Ch06_certificate_result_6_9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T22:20:05.465189+00:00
-- url     : https://prove2.me/theorems/d550cd4e-fd4d-414d-bd02-eb9455d979a2
-- title:
--   Full quantified certificate for result:6.9
-- statement:
--   Exact fully quantified source theorem/exercise as a Prop, generated from the authoritative live theorem telescope and target with no conclusion weakening.
-- source:
--   Kyprianou (2006), first edition, Lemma 6.9, printed p. 148; physical two-up PDF p. 79.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_IndexedExcursion
import Definitions.Def_Kyprianou_Ch06_AdmissibleLocalTime
open MeasureTheory Filter
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- Closed, full quantified source proposition from inverseLocalTimeStoppingTimes. -/
def certificate_result_6_9 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : NNReal → MeasurableSpace Omega)
    (X : NNReal → Omega → Real)
    (L : NNReal → Omega → NNReal)
    (hL : IsAdmissibleLocalTimeAtMaximum P F X L),
    ∀ s : NNReal,
    IsStopTime F (fun omega => inverseLocalTime L s omega) ∧
    IsStopTime F (fun omega => inverseLocalTimeLeft L s omega)

end Kyprianou.Ch06


