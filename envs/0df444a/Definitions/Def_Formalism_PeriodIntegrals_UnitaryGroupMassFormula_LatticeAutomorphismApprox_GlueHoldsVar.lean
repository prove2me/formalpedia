-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_GlueHoldsVar
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_GlueHoldsVar
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T14:55:29.989813+00:00
-- url     : https://prove2.me/theorems/5da04382-fdfe-4c56-9567-bee89bac888a
-- title:
--   Glue Holds Var
-- statement:
--   Definitions and structural lemmas for Glue Holds Var, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/GlueHoldsVar.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Reduce
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_AdelicLatticeToLocalLattices
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocFrom
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocInj
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.UnitaryGroupMassFormula.ScXuExists.Gl
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists PI.UnitaryGroupMassFormula.AdIndexEq
end PI.UnitaryGroupMassFormula.ScXuExists.Gl
end


