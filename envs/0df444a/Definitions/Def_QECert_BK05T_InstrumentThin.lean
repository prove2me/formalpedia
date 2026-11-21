-- Prove2me | Definitions.Def_QECert_BK05T_InstrumentThin
-- name    : QECert_BK05T_InstrumentThin
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T21:57:42.160623+00:00
-- url     : https://prove2.me/theorems/97dd063f-0f4c-42c9-b42c-4a9adad5ee3a
-- title:
--   Five-qubit postselection instrument check family
-- statement:
--   The five-qubit stabilizer checks used by the postselection instrument.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Postselection.lean#L335-L341

import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
set_option autoImplicit false
noncomputable section

namespace QEC.Distillation.BK05T
open Coding.PauliSymplectic

def fiveQubitCheck_QECertInstrumentThin (check : Fin 4) : Binary (Fin 5) where
  phase := 0
  vector :=
    { xPart := fun site => if ([(0, 0), (0, 3), (1, 1), (1, 4), (2, 0), (2, 2), (3, 1), (3, 3)] :
          List (Nat × Nat)).contains (check.1, site.1) then 1 else 0
      zPart := fun site => if ([(0, 1), (0, 2), (1, 2), (1, 3), (2, 3), (2, 4), (3, 0), (3, 4)] :
          List (Nat × Nat)).contains (check.1, site.1) then 1 else 0 }

theorem fiveQubitChecks_commute_QECertInstrumentThin (left right : Fin 4) :
    Commutes (fiveQubitCheck_QECertInstrumentThin left) (fiveQubitCheck_QECertInstrumentThin right) := by
  unfold Commutes
  fin_cases left <;> fin_cases right <;> decide +kernel

end QEC.Distillation.BK05T


