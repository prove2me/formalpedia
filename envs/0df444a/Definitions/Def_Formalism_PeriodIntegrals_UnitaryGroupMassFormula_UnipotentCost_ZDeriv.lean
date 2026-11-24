-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ZDeriv
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ZDeriv
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T16:08:03.239039+00:00
-- url     : https://prove2.me/theorems/a9a8f34e-81e0-4488-b823-d47e2680c8d7
-- title:
--   ZDeriv
-- statement:
--   Definitions and structural lemmas for ZDeriv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/ZDeriv.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_DerivB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL
noncomputable section
namespace PI.UnitaryGroupMassFormula.UsCost
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PI.UnitaryGroupMassFormula.UsCost.DA PI.UnitaryGroupMassFormula.UsCost.DB
end PI.UnitaryGroupMassFormula.UsCost


