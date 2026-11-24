-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_SplitLoc
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_SplitLoc
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T14:50:52.388338+00:00
-- url     : https://prove2.me/theorems/0a2c8286-2364-4e9a-8bba-1c61e6cfead1
-- title:
--   Split Loc
-- statement:
--   Definitions and structural lemmas for Split Loc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/SplitLoc.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_SplitGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_NatCastTmul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_LocSplitChiOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.UnitaryGroupMassFormula.ScXuExists
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists
end PI.UnitaryGroupMassFormula.ScXuExists


