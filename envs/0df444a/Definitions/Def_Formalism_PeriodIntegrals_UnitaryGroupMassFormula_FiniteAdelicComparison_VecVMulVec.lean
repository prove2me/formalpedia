-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_VecVMulVec
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_VecVMulVec
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T13:16:16.693878+00:00
-- url     : https://prove2.me/theorems/0493f896-cc98-4fb4-89ec-bb6f28a9db7b
-- title:
--   Vec VMul Vec
-- statement:
--   Definitions and structural lemmas for Vec VMul Vec, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteAdelicComparison/VecVMulVec.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_MemLocFrom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.FinKW
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst)
open Formalism.L2.SG.AdBridge
end PI.FinKW


