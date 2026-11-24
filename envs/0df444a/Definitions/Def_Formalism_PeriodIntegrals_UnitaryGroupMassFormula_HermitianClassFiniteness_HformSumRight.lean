-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_HformSumRight
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_HformSumRight
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T15:54:04.643927+00:00
-- url     : https://prove2.me/theorems/6ff7023c-6d0c-45cf-9cc4-b1adcc58028f
-- title:
--   Hform Sum Right
-- statement:
--   Definitions and structural lemmas for Hform Sum Right, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/HformSumRight.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_Development
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix Formalism.UG PI.InHHClassFin
namespace PI.UnitaryGroupMassFormula.InHHClassFin
variable {I : Formalism.MainNotions.S.AutInst} {S : Set (Fin I.n → I.E)}
def Frame.Jt (fr : Frame I S) : Matrix (Fin fr.m ⊕ Fin fr.k) (Fin fr.m ⊕ Fin fr.k) I.E :=
  cT (starRingEnd I.E) fr.B * I.J * fr.B
end PI.UnitaryGroupMassFormula.InHHClassFin


