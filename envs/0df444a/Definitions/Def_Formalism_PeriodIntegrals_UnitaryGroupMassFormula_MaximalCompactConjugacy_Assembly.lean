-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MaximalCompactConjugacy_Assembly
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MaximalCompactConjugacy_Assembly
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T12:57:47.681929+00:00
-- url     : https://prove2.me/theorems/01a32880-34bd-4522-97be-bb233d59dccc
-- title:
--   Assembly
-- statement:
--   Definitions and structural lemmas for Assembly, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MaximalCompactConjugacy/Assembly.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_AdBridge
import Definitions.Def_Formalism_PeriodIntegrals_AdBridgeSteps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.BridgeMaxCptWork
open NumberField IsDedekindDomain Matrix
open Formalism.MainNotions.S (AutInst uMat)
open Formalism.L2.SG.AdBridge
end PI.BridgeMaxCptWork


