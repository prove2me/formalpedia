-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantAlgebraComparison_MapThetaEq
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantAlgebraComparison_MapThetaEq
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T14:24:31.751013+00:00
-- url     : https://prove2.me/theorems/b1a23421-3355-473c-9b42-fafe845691c8
-- title:
--   Map Theta Eq
-- statement:
--   Definitions and structural lemmas for Map Theta Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantAlgebraComparison/MapThetaEq.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantAlgebraComparison_BridgeHomFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.UnitaryGroupMassFormula.BridgeInvAlg
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst uMat)
open Formalism.L2.SG.AdBridge
end PI.UnitaryGroupMassFormula.BridgeInvAlg


