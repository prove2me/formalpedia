-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_GlueHoldsVar
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_GlueHoldsVar
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T13:16:00.340649+00:00
-- url     : https://prove2.me/theorems/93cc7b70-fc56-485d-ba2e-262398333736
-- title:
--   Glue Holds Var
-- statement:
--   Definitions and structural lemmas for Glue Holds Var, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/GlueHoldsVar.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HGNsmulRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S
open scoped TensorProduct
namespace PI.ScRefExists.GlueC
open PI.ScRefExists PI.ScRefExists.GlueA PI.ScRefExists.GlueB PI.ScRefExists.Sk
end PI.ScRefExists.GlueC
end


